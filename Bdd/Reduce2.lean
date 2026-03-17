import Bdd.Collect
import Bdd.Trim

open Pointer
open Bdd
open RawBdd

/-!
# Reduce2: incremental BDD reduction via the RawBdd pattern

This file re-implements `Reduce.oreduce` without pre-allocating the full heap.
Nodes are pushed one at a time as they are discovered to be non-redundant and
non-isomorphic.  No `Trim` step is needed at the end.

The high-level structure follows Bryant (1986):
1. `discover` groups input-BDD node indices by variable level.
2. For each level (bottom-up), `step` eliminates redundant nodes (low = high)
   and merges isomorphic nodes (same reduced children).
3. The mapping `ids` records, for each input node `j`, the `RawPointer` in the
   output BDD that `j` has been reduced to.

Key innovation: `ProvedState` bundles `State n m` with a direct proof `hh` that
every heap entry is self-bounded, avoiding the need for `Classical.choose` later.
-/

-- ---------------------------------------------------------------------------
-- Discover: group reachable nodes by variable level
-- (Moved from the now-obsolete Reduce.lean)
-- ---------------------------------------------------------------------------

private def OBdd.discover_helper : List (Fin m) → Vector (Node n m) m → Vector (List (Fin m)) n → Vector (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => OBdd.discover_helper tail v (I.set v[head].var (head :: I[v[head].var]))

private lemma OBdd.discover_helper_retains_found {I : Vector (List (Fin m)) n} {i : Fin n} : j ∈ I[i] → j ∈ (OBdd.discover_helper l v I)[i] := by
  induction l generalizing I with
  | nil => exact id
  | cons head tail ih =>
    intro h
    unfold OBdd.discover_helper
    apply ih
    rcases eq_or_ne (v[head].var) i with heq | hne
    · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = head :: I[i] := by
        subst heq; simp [Vector.getElem_set_self]
      simp only [hkey]; exact List.mem_cons_of_mem _ h
    · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = I[i] :=
        Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hne)
      simp only [hkey]; exact h

private lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vector (List (Fin m)) n} :
    j ∈ l → j ∈ (OBdd.discover_helper l v I)[v[j].var] := by
  intro h
  cases h with
  | head as =>
    unfold OBdd.discover_helper
    apply OBdd.discover_helper_retains_found
    simp [Vector.getElem_set_self]
  | tail b ih =>
    unfold OBdd.discover_helper
    exact OBdd.discover_helper_spec O ih

/-- Return a vector whose `v`th entry is a list of node indices with variable index `v`. -/
def OBdd.discover (O : OBdd n m) : Vector (List (Fin m)) n :=
  OBdd.discover_helper (Collect.collect O) O.1.heap (Vector.replicate n [])

/-- `discover` is correct (forward direction). -/
theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (OBdd.discover O)[O.1.heap[j].var] :=
  (OBdd.discover_helper_spec O) ∘ Collect.collect_spec

private lemma OBdd.discover_helper_mem_var {l : List (Fin m)} {v : Vector (Node n m) m}
    {I : Vector (List (Fin m)) n} {i : Fin n} {j : Fin m} :
    j ∈ (OBdd.discover_helper l v I)[i] → j ∈ I[i] ∨ (j ∈ l ∧ v[j].var = i) := by
  induction l generalizing I with
  | nil => exact .inl
  | cons head tail ih =>
    simp only [OBdd.discover_helper]
    intro h
    rcases ih h with h | ⟨hmem, hvar⟩
    · rcases eq_or_ne (v[head].var) i with heq | hne
      · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = head :: I[i] := by
          subst heq; simp [Vector.getElem_set_self]
        rw [hkey] at h
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact .inr ⟨.head _, heq⟩
        · exact .inl h
      · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = I[i] :=
          Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hne)
        rw [hkey] at h
        exact .inl h
    · exact .inr ⟨.tail _ hmem, hvar⟩

/-- `discover` is correct (backward direction): membership implies var = i and reachability. -/
theorem OBdd.discover_spec_inv {O : OBdd n m} {j : Fin m} {i : Fin n} :
    j ∈ (OBdd.discover O)[i] →
    O.1.heap[j].var.1 = i.1 ∧ Reachable O.1.heap O.1.root (.node j) := by
  simp only [OBdd.discover, Fin.getElem_fin]
  intro h
  rcases OBdd.discover_helper_mem_var h with h | ⟨hmem, hvar⟩
  · simp [Vector.getElem_replicate] at h
  · exact ⟨congrArg Fin.val hvar, Collect.collect_spec_reverse hmem⟩

namespace Reduce2

-- ---------------------------------------------------------------------------
-- Instances for RawPointer (= Bool ⊕ Nat)
-- ---------------------------------------------------------------------------

private instance : DecidableEq RawPointer :=
  inferInstanceAs (DecidableEq (Bool ⊕ Nat))


private instance : LE RawPointer where
  le a b := match a, b with
    | .inl false, _       => True
    | .inl true,  .inl false => False
    | .inl true,  _       => True
    | .inr _,     .inl _  => False
    | .inr i,     .inr j  => i ≤ j

private instance : DecidableLE RawPointer :=
  fun a b => match a, b with
    | .inl false, _       => isTrue  trivial
    | .inl true,  .inl false => isFalse id
    | .inl true,  .inl true  => isTrue  trivial
    | .inl true,  .inr _  => isTrue  trivial
    | .inr _,     .inl _  => isFalse id
    | .inr i,     .inr j  => match Nat.decLe i j with
        | isTrue  h => isTrue  h
        | isFalse h => isFalse h

-- ---------------------------------------------------------------------------
-- State and ProvedState
-- ---------------------------------------------------------------------------

/-- Mutable state for the incremental reduction.

* `size` and `heap` together form the output heap built so far.
* `ids` maps each input-node index `j : Fin m` to its representative
  `RawPointer` in the output BDD.  An entry is `none` until the node has been
  processed; it is filled in bottom-up as each variable level is handled.
-/
private structure State (n) (m) where
  size : Nat
  heap : Vector (RawNode n) size
  ids  : Vector (Option RawPointer) m

/-- A `State` together with a proof that every heap entry is self-bounded. -/
private structure ProvedState (n m : Nat) where
  state : State n m
  hh    : ∀ k : Fin state.size, state.heap[k].Bounded k

private def initial (n m : Nat) : State n m :=
  ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩

private def provedStateInitial (n m : Nat) : ProvedState n m where
  state := ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩
  hh := fun k => k.elim0

-- ---------------------------------------------------------------------------
-- Primitive operations
-- ---------------------------------------------------------------------------

/-- Resolve an input pointer to its output `RawPointer`.
`h` is a proof that every node pointer in `p` has an entry in `ps.state.ids`; this
proof will be discharged from the loop invariant at each call site. -/
private def get_id {n m : Nat} (ps : ProvedState n m) (p : Pointer m)
    (h : ∀ j, p = .node j → (ps.state.ids[j]).isSome) : RawPointer :=
  match p with
  | .terminal b => .inl b
  | .node j     => (ps.state.ids[j]).get (h j rfl)

/-- Record that input node `j` maps to output pointer `p`. -/
private def set_id {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) : ProvedState n m :=
  { state := { size := ps.state.size, heap := ps.state.heap, ids := ps.state.ids.set j (some p) },
    hh    := ps.hh }

/-- Push a new node and extend the heap-boundedness proof. -/
private def push_node {n m : Nat} (ps : ProvedState n m) (N : RawNode n)
    (hN : N.Bounded ps.state.size) : ProvedState n m × RawPointer :=
  let hh' : ∀ k : Fin (ps.state.size + 1), (ps.state.heap.push N)[k].Bounded k := fun k => by
    by_cases hlt : k.1 < ps.state.size
    · simp only [Fin.getElem_fin, Vector.getElem_push_lt hlt]
      exact ps.hh ⟨k.1, hlt⟩
    · have hk : k.1 = ps.state.size := by omega
      simp only [Fin.getElem_fin, show k.1 = ps.state.size from hk,
                 Vector.getElem_push_eq]
      exact hN
  ⟨⟨{ size := ps.state.size + 1, heap := ps.state.heap.push N, ids := ps.state.ids }, hh'⟩,
   .inr ps.state.size⟩

/-- In a structurally canonical heap (no two positions have the same raw node),
    any ordered BDD is reduced. -/
private lemma structural_canonical_reduced {n s : Nat}
    {v : Vector (RawNode n) s} {hh : ∀ k : Fin s, v[k].Bounded k}
    (hsc : ∀ k1 k2 : Fin s, v[k1] = v[k2] → k1 = k2)
    {root : Pointer s}
    (hord : Bdd.Ordered ⟨cook_heap v hh, root⟩)
    (hnored : Bdd.NoRedundancy ⟨cook_heap v hh, root⟩) :
    OBdd.Reduced ⟨⟨cook_heap v hh, root⟩, hord⟩ := by
  let O : OBdd n s := ⟨⟨cook_heap v hh, root⟩, hord⟩
  -- Helper: cook_heap nodes relate back to raw nodes
  have cook_heap_eq : ∀ k : Fin s, (cook_heap v hh)[k] = v[k].cook (RawNode.bounded_of_le (hh k) (by omega)) := by
    intro k
    simp [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn]
  -- Helper: if cooked nodes at kp and kq are equal, then kp = kq
  have node_inj : ∀ (kp kq : Fin s),
      (cook_heap v hh)[kp].var  = (cook_heap v hh)[kq].var →
      (cook_heap v hh)[kp].low  = (cook_heap v hh)[kq].low →
      (cook_heap v hh)[kp].high = (cook_heap v hh)[kq].high →
      kp = kq := by
    intro kp kq hvar hlow hhigh
    apply hsc
    rw [cook_heap_eq kp, cook_heap_eq kq] at hvar hlow hhigh
    simp only [RawNode.cook] at hvar hlow hhigh
    have hlo : v[kp].lo = v[kq].lo := cook_inj hlow
    have hhi : v[kp].hi = v[kq].hi := cook_inj hhigh
    rcases hkp : v[kp] with ⟨vap, lop, hip⟩
    rcases hkq : v[kq] with ⟨vaq, loq, hiq⟩
    simp only [hkp] at hvar hlo hhi
    simp only [hkq] at hvar hlo hhi
    subst hvar; subst hlo; subst hhi
    rfl
  -- Main helper: for any sub-BDD P of O, if Q is another sub-BDD of O with same toTree, then P.root = Q.root
  -- We prove this by init_inductionOn on P.
  let M := cook_heap v hh
  -- Main key lemma: toTree-injectivity on pointer for a fixed heap M
  have key : ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
      OBdd.toTree P = OBdd.toTree Q → P.1.root = Q.1.root := by
    intro P
    induction P using OBdd.init_inductionOn with
    | base b =>
      intro Q hP_heap hQ_heap htree_eq
      simp [OBdd.toTree_terminal] at htree_eq
      cases hQ : Q.1.root with
      | terminal bq =>
        rw [OBdd.toTree_terminal' hQ] at htree_eq
        injection htree_eq with htree_eq
        exact congrArg _ htree_eq
      | node jq =>
        rw [OBdd.toTree_node hQ] at htree_eq
        exact absurd htree_eq (by simp)
    | step jp hl_ord ih_lo hh_ord ih_hi hj_ord =>
      intro Q hP_heap hQ_heap htree_eq
      cases hQ : Q.1.root with
      | terminal bq =>
        rw [OBdd.toTree_node (O := ⟨_, hj_ord⟩) rfl, OBdd.toTree_terminal' hQ] at htree_eq
        exact absurd htree_eq (by simp)
      | node jq =>
        -- Obtain ordered proof for Q at node jq
        have hQ_ord : Bdd.Ordered ⟨Q.1.heap, Pointer.node jq⟩ := by
          rcases Q with ⟨⟨qheap, qroot⟩, qord⟩; simp only at hQ; subst hQ; exact qord
        rw [OBdd.toTree_node (O := ⟨_, hj_ord⟩) rfl,
            OBdd.toTree_node (O := Q) hQ] at htree_eq
        injection htree_eq with hvar hlo_tree hhi_tree
        have hlo_eq_root := ih_lo
          ⟨⟨Q.1.heap, Q.1.heap[jq].low⟩, OBdd.ordered_of_low_edge hQ_ord⟩
          hP_heap hQ_heap hlo_tree
        have hhi_eq_root := ih_hi
          ⟨⟨Q.1.heap, Q.1.heap[jq].high⟩, OBdd.ordered_of_high_edge hQ_ord⟩
          hP_heap hQ_heap hhi_tree
        -- hlo_eq_root : P.1.heap[jp].low = Q.1.heap[jq].low
        -- hP_heap : P.1.heap = M; hQ_heap : Q.1.heap = M
        -- Goal: node jp = node jq
        -- Convert everything to cook_heap v hh using hP_heap and hQ_heap
        have hlo_eq : (cook_heap v hh)[jp].low = (cook_heap v hh)[jq].low := by
          have h1 : P.1.heap[jp].low = Q.1.heap[jq].low := hlo_eq_root
          rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
        have hhi_eq : (cook_heap v hh)[jp].high = (cook_heap v hh)[jq].high := by
          have h1 : P.1.heap[jp].high = Q.1.heap[jq].high := hhi_eq_root
          rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
        have hvar_eq : (cook_heap v hh)[jp].var = (cook_heap v hh)[jq].var := by
          have h1 : P.1.heap[jp].var = Q.1.heap[jq].var :=
            Fin.ext (congrArg Fin.val hvar)
          rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
        exact congrArg _ (node_inj jp jq hvar_eq hlo_eq hhi_eq)
  -- Now prove Reduced
  constructor
  · exact hnored
  · intro ⟨p, hp_reach⟩ ⟨q, hq_reach⟩ hsim
    -- hsim : SimilarRP O ⟨p, hp_reach⟩ ⟨q, hq_reach⟩
    -- = toTree of sub-BDD at p = toTree of sub-BDD at q
    show p = q
    have hop : Bdd.Ordered ⟨M, p⟩ :=
      Bdd.ordered_of_reachable (O := O) hp_reach
    have hoq : Bdd.Ordered ⟨M, q⟩ :=
      Bdd.ordered_of_reachable (O := O) hq_reach
    exact key ⟨⟨M, p⟩, hop⟩ ⟨⟨M, q⟩, hoq⟩ rfl rfl hsim

-- ---------------------------------------------------------------------------
-- Invariant
-- ---------------------------------------------------------------------------

/-- The loop invariant. `hh` is now a direct field of `ps`, not wrapped in ∃. -/
private def Invariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat) : Prop :=
  -- Completeness
  (∀ (j : Fin m),
      i < O.1.heap[j].var.1 →
      Reachable O.1.heap O.1.root (.node j) →
      (ps.state.ids[j]).isSome) ∧
  -- Correctness
  ∀ (j : Fin m) (ptr : RawPointer),
      ps.state.ids[j] = some ptr →
      ∃ hj   : Bdd.Ordered ⟨O.1.heap, .node j⟩,
        ∃ hptr : ptr.Bounded ps.state.size,
          ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩,
            OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ ∧
            ∀ I,
              OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ I =
              OBdd.evaluate ⟨⟨O.1.heap, .node j⟩, hj⟩ I

private lemma inv_initial {n m : Nat} {O : OBdd n m} {i : Nat}
    (hi : ∀ j : Fin m, O.1.heap[j].var.1 ≤ i) :
    Invariant O (provedStateInitial n m) i :=
  ⟨fun j h _ => absurd h (Nat.not_lt.mpr (hi j)),
   fun j ptr h => by simp [provedStateInitial] at h⟩

lemma Invariant.ids_isSome {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat} (inv : Invariant O ps i)
    {j : Fin m}
    (hvar  : i < O.1.heap[j].var.1)
    (hreach : Reachable O.1.heap O.1.root (.node j)) :
    (ps.state.ids[j]).isSome :=
  inv.1 j hvar hreach

/-- When ids[j] = some (.inr k), the output node's var ≥ the input node's var. -/
private def VarInvariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) : Prop :=
  ∀ (j : Fin m) (k : Fin ps.state.size),
    ps.state.ids[j] = some (.inr k.1) →
    O.1.heap[j].var.1 ≤ ps.state.heap[k].va.1

/-- All heap nodes have variable strictly above level i. -/
private def AllAbove {n m : Nat} (ps : ProvedState n m) (i : Nat) : Prop :=
  ∀ k : Fin ps.state.size, i < ps.state.heap[k].va.1

/-- The heap is injective: no two positions have the same raw node. -/
private def HeapInjective {n : Nat} (ps : ProvedState n m) : Prop :=
  ∀ k1 k2 : Fin ps.state.size, ps.state.heap[k1] = ps.state.heap[k2] → k1 = k2

private lemma varInvariant_initial {n m : Nat} {O : OBdd n m} :
    VarInvariant O (provedStateInitial n m) := by
  intro j k
  exact absurd k.isLt (by simp [provedStateInitial])

private lemma allAbove_initial {n m : Nat} {i : Nat} :
    AllAbove (provedStateInitial n m) i := by
  intro k
  exact absurd k.isLt (by simp [provedStateInitial])

private lemma heapInjective_initial {n m : Nat} :
    HeapInjective (provedStateInitial n m) := by
  intro k1
  exact absurd k1.isLt (by simp [provedStateInitial])

/-- Bundled correctness predicate for a queue entry. -/
private def EntryCorrect {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat)
    (entry : (RawPointer × RawPointer) × Fin m) : Prop :=
  Reachable O.1.heap O.1.root (.node entry.2) ∧
  O.1.heap[entry.2].var.1 = i ∧
  (∀ l, O.1.heap[entry.2].low = .node l → ps.state.ids[l] = some entry.1.1) ∧
  (∀ l, O.1.heap[entry.2].high = .node l → ps.state.ids[l] = some entry.1.2) ∧
  (∀ b, O.1.heap[entry.2].low = .terminal b → entry.1.1 = .inl b) ∧
  (∀ b, O.1.heap[entry.2].high = .terminal b → entry.1.2 = .inl b)

-- ---------------------------------------------------------------------------
-- Pure proof-carrying algorithm functions
-- ---------------------------------------------------------------------------

/-- The output pointer of `get_id` is bounded by `ps.state.size`. -/
private lemma get_id_bounded {n m : Nat} {O : OBdd n m} {ps : ProvedState n m} {i : Nat}
    (inv : Invariant O ps i) {p : Pointer m}
    (h : ∀ j, p = .node j → (ps.state.ids[j]).isSome) :
    (get_id ps p h).Bounded ps.state.size := by
  match p with
  | .terminal b => intro k hk; exact absurd hk (by simp [get_id])
  | .node k =>
    simp only [get_id]
    obtain ⟨ptr, hkptr⟩ := Option.isSome_iff_exists.mp (h k rfl)
    have heq : (ps.state.ids[k]).get (h k rfl) = ptr := by simp [hkptr]
    rw [heq]
    obtain ⟨_, hptr, _⟩ := inv.2 k ptr hkptr
    unfold RawPointer.Bounded
    intro i hi
    exact hptr hi

/-- For each node j in l: if lid = hid (redundant), set ids[j] := lid;
otherwise add to accumulator. -/
private def populate_queue {n m : Nat} (O : OBdd n m)
    (i : Fin n)
    (acc : List ((RawPointer × RawPointer) × Fin m)) :
    (l : List (Fin m)) →
    (ps : ProvedState n m) →
    Invariant O ps i.1 →
    (∀ j ∈ l, O.1.heap[j].var.1 = i.1) →
    (∀ j ∈ l, Reachable O.1.heap O.1.root (.node j)) →
    (∀ entry ∈ acc, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
    -- Non-redundancy of accumulator entries.
    (∀ entry ∈ acc, entry.1.1 ≠ entry.1.2) →
    -- Entry correctness for accumulator entries.
    (∀ entry ∈ acc, EntryCorrect O ps i.1 entry) →
    -- VarInvariant is preserved.
    VarInvariant O ps →
    { p : ProvedState n m × List ((RawPointer × RawPointer) × Fin m) //
        Invariant O p.1 i.1 ∧
        p.1.state.size = ps.state.size ∧
        -- Accumulator entries are preserved in the output list.
        (∀ entry ∈ acc, entry ∈ p.2) ∧
        -- ids only grow: once set, stays set.
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (p.1.state.ids[k]).isSome) ∧
        (∀ j ∈ l, (∃ key, (key, j) ∈ p.2) ∨ (p.1.state.ids[j]).isSome) ∧
        -- All queue entries have key pointers bounded by the output state's heap size.
        (∀ entry ∈ p.2, entry.1.1.Bounded p.1.state.size ∧ entry.1.2.Bounded p.1.state.size) ∧
        -- All queue entries are non-redundant: key.1 ≠ key.2.
        (∀ entry ∈ p.2, entry.1.1 ≠ entry.1.2) ∧
        -- Entry correctness for all queue entries.
        (∀ entry ∈ p.2, EntryCorrect O p.1 i.1 entry) ∧
        -- VarInvariant is preserved.
        VarInvariant O p.1 }
  | [], ps, inv, _, _, hbounds_acc, hnonred_acc, hec_acc, hvarinv =>
      ⟨⟨ps, acc⟩, inv, rfl,
       fun _ he => he,
       fun _ hk => hk,
       fun _ hj => by simp at hj,
       hbounds_acc,
       hnonred_acc,
       hec_acc,
       hvarinv⟩
  | j :: tail, ps, inv, hvar, hreach, hbounds_acc, hnonred_acc, hec_acc, hvarinv => by
      have hvar_j   : O.1.heap[j].var.1 = i.1 := hvar   j (.head _)
      have hreach_j : Reachable O.1.heap O.1.root (.node j) := hreach j (.head _)
      -- For any child k of j (via some edge), ids[k] is already set.
      -- Proof: orderness gives var[j] < var[k]; completeness then gives isSome.
      have hchild : ∀ (p : Pointer m), Edge O.1.heap (.node j) p →
          ∀ k, p = .node k → (ps.state.ids[k]).isSome := by
        intro p hedgep k hk; subst hk
        have hreach_k : Reachable O.1.heap O.1.root (.node k) := .tail hreach_j hedgep
        apply inv.ids_isSome _ hreach_k
        have hmay := O.2
          (show O.1.RelevantEdge ⟨.node j, hreach_j⟩ ⟨.node k, hreach_k⟩ from hedgep)
        -- Unfold the ordered-edge condition to get a Nat inequality.
        simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar,
                   Fin.mk_lt_mk] at hmay
        -- hmay : var[j].1 < var[k].1;  hvar_j : var[j].1 = i.1
        linarith [hvar_j]
      let lid := get_id ps O.1.heap[j].low  (hchild _ (Edge.low  rfl))
      let hid := get_id ps O.1.heap[j].high (hchild _ (Edge.high rfl))
      -- Helpers for reasoning about set_id without ps' aliasing issues.
      have ids_set_self : (set_id ps j lid).state.ids[j] = some lid := by
        show (ps.state.ids.set j (some lid))[j] = some lid
        simp [Vector.getElem_set_self]
      have ids_set_ne : ∀ k : Fin m, k ≠ j →
          (set_id ps j lid).state.ids[k] = ps.state.ids[k] := fun k hkj => by
        show (ps.state.ids.set j (some lid))[k] = ps.state.ids[k]
        exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hkj.symm)
      by_cases heq : lid = hid
      · -- Redundant: set ids[j] := lid and recurse on tail.
        have hinv' : Invariant O (set_id ps j lid) i.1 := by
          constructor
          · -- Completeness: j has var = i.1, so i.1 < var[k] forces k ≠ j.
            intro k hk hreach_k
            have hkj : k ≠ j := fun h => by subst h; linarith [hvar_j]
            rw [ids_set_ne k hkj]; exact inv.1 k hk hreach_k
          · -- Correctness: for k ≠ j nothing changed; for k = j, semantic sorry.
            intro k ptr hkptr
            by_cases hkj : k = j
            · subst hkj
              rw [ids_set_self] at hkptr
              simp only [Option.some.injEq] at hkptr; subst hkptr
              -- lid correctly represents sub-BDD at k (redundant case: lid = hid)
              have hj : Bdd.Ordered ⟨O.1.heap, Pointer.node k⟩ :=
                Bdd.ordered_of_reachable hreach_j
              have hlow_ord : Bdd.Ordered ⟨O.1.heap, O.1.heap[k].low⟩ :=
                Bdd.ordered_of_reachable (Relation.ReflTransGen.tail hreach_j (Edge.low rfl))
              have hhigh_ord : Bdd.Ordered ⟨O.1.heap, O.1.heap[k].high⟩ :=
                Bdd.ordered_of_reachable (Relation.ReflTransGen.tail hreach_j (Edge.high rfl))
              -- For any child pointer, extract bounded/ordered/reduced/eval from inv.
              have child_inv : ∀ (p : Pointer m) (hp : Bdd.Ordered ⟨O.1.heap, p⟩)
                  (hch : ∀ l, p = .node l → (ps.state.ids[l]).isSome),
                  ∃ (hptr : (get_id ps p hch).Bounded ps.state.size)
                    (ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh,
                                       (get_id ps p hch).cook hptr⟩),
                    OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh,
                                    (get_id ps p hch).cook hptr⟩, ho⟩ ∧
                    ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh,
                                         (get_id ps p hch).cook hptr⟩, ho⟩ I =
                         OBdd.evaluate ⟨⟨O.1.heap, p⟩, hp⟩ I := by
                intro p hp hch
                cases p with
                | terminal b =>
                  refine ⟨fun h => absurd h (by simp [get_id]), Bdd.Ordered_of_terminal,
                           Bdd.reduced_of_terminal, fun I => ?_⟩
                  change OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, .terminal b⟩, _⟩ I =
                         OBdd.evaluate ⟨⟨O.1.heap, .terminal b⟩, hp⟩ I
                  simp [OBdd.evaluate_terminal]
                | node l =>
                  simp only [get_id]
                  obtain ⟨_, hptr, ho, hred, heval⟩ :=
                    inv.2 l _ (Option.get_mem (hch l rfl))
                  exact ⟨hptr, ho, hred, heval⟩
              obtain ⟨hptr, ho, hred, heval_low⟩ :=
                child_inv _ hlow_ord (hchild _ (Edge.low rfl))
              obtain ⟨hptr_h, ho_h, _, heval_high⟩ :=
                child_inv _ hhigh_ord (hchild _ (Edge.high rfl))
              refine ⟨hj, hptr, ho, hred, fun I => ?_⟩
              -- cook with equal raw pointers gives equal Pointer m (bounds are Props).
              have cook_eq_of_eq : ∀ (p q : RawPointer)
                  (hp : p.Bounded ps.state.size) (hq : q.Bounded ps.state.size),
                  p = q → p.cook hp = q.cook hq := fun p q hp hq hpq => by
                subst hpq
                cases p with
                | inl b => rfl
                | inr i => exact congrArg Pointer.node (Fin.ext rfl)
              have hcook_eq : hid.cook hptr_h = lid.cook hptr :=
                cook_eq_of_eq hid lid hptr_h hptr heq.symm
              -- evaluations at hid and lid in cook_heap coincide.
              have heval_hid_eq_lid :
                  OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, hid.cook hptr_h⟩, ho_h⟩ I =
                  OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, lid.cook hptr⟩, ho⟩ I :=
                congrArg (OBdd.evaluate · I)
                  (Subtype.ext (by simp [hcook_eq]))
              -- eval(high in old) = eval(low in old): both children reduce to lid = hid.
              have branches_eq :
                  OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].high⟩, hhigh_ord⟩ I =
                  OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].low⟩, hlow_ord⟩ I :=
                (heval_high I).symm.trans (heval_hid_eq_lid.trans (heval_low I))
              -- Proof of ordered-proof-irrelevance for evaluate.
              have eval_pi : ∀ (B : Bdd n m) (h1 h2 : B.Ordered) (I : Vector Bool n),
                  OBdd.evaluate ⟨B, h1⟩ I = OBdd.evaluate ⟨B, h2⟩ I :=
                fun B h1 h2 I => congrArg (OBdd.evaluate · I) (Subtype.ext rfl)
              calc OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, lid.cook hptr⟩, ho⟩ I
                  = OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].low⟩, hlow_ord⟩ I :=
                    heval_low I
                _ = if I[O.1.heap[k].var]
                      then OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].high⟩, hhigh_ord⟩ I
                      else OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[k].low⟩, hlow_ord⟩ I := by
                    rw [branches_eq]; simp
                _ = OBdd.evaluate ⟨⟨O.1.heap, Pointer.node k⟩, hj⟩ I := by
                    symm; rw [OBdd.evaluate_node]
            · rw [ids_set_ne k hkj] at hkptr
              exact inv.2 k ptr hkptr
        -- EntryCorrect is preserved through set_id ps j lid for acc entries.
        have hec_acc' : ∀ entry ∈ acc, EntryCorrect O (set_id ps j lid) i.1 entry := by
          intro entry hmem
          obtain ⟨hr, hv, hlo, hhi, hlo_t, hhi_t⟩ := hec_acc entry hmem
          refine ⟨hr, hv, fun l hl => ?_, fun l hl => ?_, hlo_t, hhi_t⟩
          · -- l is a child of entry.2, so var[l] > i = var[j], hence l ≠ j
            have hord_j' : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩ := Bdd.ordered_of_reachable hr
            have hreach_l : Reachable O.1.heap O.1.root (.node l) :=
              .tail hr (Edge.low hl)
            have hmay := O.2 (show O.1.RelevantEdge ⟨.node entry.2, hr⟩ ⟨.node l, hreach_l⟩
              from Edge.low hl)
            simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar, Fin.mk_lt_mk] at hmay
            have hlj : l ≠ j := fun h => by subst h; linarith [hv]
            rw [ids_set_ne l hlj]; exact hlo l hl
          · have hreach_l : Reachable O.1.heap O.1.root (.node l) :=
              .tail hr (Edge.high hl)
            have hmay := O.2 (show O.1.RelevantEdge ⟨.node entry.2, hr⟩ ⟨.node l, hreach_l⟩
              from Edge.high hl)
            simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar, Fin.mk_lt_mk] at hmay
            have hlj : l ≠ j := fun h => by subst h; linarith [hv]
            rw [ids_set_ne l hlj]; exact hhi l hl
        -- VarInvariant is preserved through set_id ps j lid.
        have hvarinv' : VarInvariant O (set_id ps j lid) := by
          intro j₀ k₀ hids₀
          by_cases hjj₀ : j₀ = j
          · -- j₀ = j: ids[j] was just set to lid
            rw [hjj₀] at hids₀ ⊢
            rw [ids_set_self] at hids₀
            simp only [Option.some.injEq] at hids₀
            -- hids₀ : lid = .inr k₀.1
            -- lid = get_id ps O.1.heap[j].low h. Examine O.1.heap[j].low.
            -- lid = .inr k₀.1 (from hids₀). Need: O.heap[j].var ≤ ps.heap[k₀].va
            -- lid came from get_id on the low child.
            -- Use a helper lemma to extract the child node index.
            have ⟨l, hlow, hids_l⟩ : ∃ l, O.1.heap[j].low = .node l ∧
                ps.state.ids[l] = some (.inr k₀.1) := by
              -- lid = get_id ps O.1.heap[j].low _. Case-split on the low pointer.
              cases hlow_case : O.1.heap[j].low with
              | terminal b =>
                have hlid_bool : lid = .inl b := by
                  simp only [lid]; simp_rw [hlow_case]; rfl
                exact absurd (hlid_bool ▸ hids₀) (by simp)
              | node l =>
                use l, rfl
                have hlid_eq : lid = (ps.state.ids[l]).get
                    (hchild (.node l) (Edge.low hlow_case) l rfl) := by
                  simp only [lid]; simp_rw [hlow_case]; rfl
                rw [hlid_eq] at hids₀
                exact (Option.some_get _).symm.trans (congrArg some hids₀)
            have hvi := hvarinv l k₀ hids_l
            have hmay := O.2 (show O.1.RelevantEdge ⟨.node j, hreach_j⟩
              ⟨.node l, .tail hreach_j (Edge.low hlow)⟩ from Edge.low hlow)
            simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Pointer.toVar,
                       Fin.mk_lt_mk] at hmay
            exact Nat.le_trans (Nat.le_of_lt hmay) hvi
          · rw [ids_set_ne j₀ hjj₀] at hids₀
            exact hvarinv j₀ k₀ hids₀
        obtain ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hacc_f, hmono_f, hpost_f, hbounds_f, hnonred_f, hec_f, hvarinv_f⟩ :=
          populate_queue O i acc tail (set_id ps j lid) hinv'
            (fun k hk => hvar   k (.tail _ hk))
            (fun k hk => hreach k (.tail _ hk))
            -- accumulator bounds unchanged (size of set_id = size of ps)
            hbounds_acc
            hnonred_acc
            hec_acc'
            hvarinv'
        exact ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hacc_f,
               fun k hk => hmono_f k (by
                 by_cases hkj : k = j
                 · subst hkj; simp [ids_set_self]
                 · rw [ids_set_ne k hkj]; exact hk),
               fun k hk => by
                 cases hk with
                 | head =>
                   right; exact hmono_f j (by simp [ids_set_self])
                 | tail _ hk' => exact hpost_f k hk',
               hbounds_f,
               hnonred_f,
               hec_f,
               hvarinv_f⟩
      · -- Non-redundant: add ((lid, hid), j) to accumulator; recurse unchanged.
        have hlid_bound : lid.Bounded ps.state.size := get_id_bounded inv (hchild _ (Edge.low  rfl))
        have hhid_bound : hid.Bounded ps.state.size := get_id_bounded inv (hchild _ (Edge.high rfl))
        -- EntryCorrect for the new entry ((lid, hid), j)
        -- Helper: get_id on a node pointer yields (ids[l]).get
        have get_id_node : ∀ (l : Fin m) (h : ∀ k, Pointer.node l = .node k → (ps.state.ids[k]).isSome),
            get_id ps (.node l) h = (ps.state.ids[l]).get (h l rfl) := fun _ _ => rfl
        -- Helper: get_id on terminal yields .inl b
        have get_id_terminal : ∀ (b : Bool) (h : ∀ k, Pointer.terminal b = .node k → (ps.state.ids[k]).isSome),
            get_id ps (.terminal b) h = .inl b := fun _ _ => rfl
        have hec_new : EntryCorrect O ps i.1 ⟨⟨lid, hid⟩, j⟩ := by
          refine ⟨hreach_j, hvar_j, fun l hl => ?_, fun l hl => ?_, fun b hb => ?_, fun b hb => ?_⟩
          · -- lid = get_id ps (.node l) _, i.e., (ids[l]).get _
            have hlid : lid = (ps.state.ids[l]).get (hchild _ (Edge.low rfl) l hl) := by
              simp only [lid]
              simp_rw [hl]
              rfl
            rw [hlid]; exact (Option.some_get _).symm
          · have hhid : hid = (ps.state.ids[l]).get (hchild _ (Edge.high rfl) l hl) := by
              simp only [hid]
              simp_rw [hl]
              rfl
            rw [hhid]; exact (Option.some_get _).symm
          · have : lid = .inl b := by
              simp only [lid]
              simp_rw [hb]
              rfl
            exact this
          · have : hid = .inl b := by
              simp only [hid]
              simp_rw [hb]
              rfl
            exact this
        obtain ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hacc_f, hmono_f, hpost_f, hbounds_f, hnonred_f, hec_f, hvarinv_f⟩ :=
          populate_queue O i (⟨⟨lid, hid⟩, j⟩ :: acc) tail ps inv
            (fun k hk => hvar   k (.tail _ hk))
            (fun k hk => hreach k (.tail _ hk))
            -- bounds for the new head entry + old acc entries
            (fun entry he => by
              cases he with
              | head => exact ⟨hlid_bound, hhid_bound⟩
              | tail _ he' => exact hbounds_acc entry he')
            -- non-redundancy: new entry has lid ≠ hid, old acc entries are non-redundant
            (fun entry he => by
              cases he with
              | head => exact heq
              | tail _ he' => exact hnonred_acc entry he')
            -- entry correctness for new entry + old acc entries
            (fun entry he => by
              cases he with
              | head => exact hec_new
              | tail _ he' => exact hec_acc entry he')
            hvarinv
        exact ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f,
               fun e he => hacc_f e (.tail _ he),
               hmono_f,
               fun k hk => by
                 cases hk with
                 | head => left; exact ⟨⟨lid, hid⟩, hacc_f _ (.head _)⟩
                 | tail _ hk' => exact hpost_f k hk',
               hbounds_f,
               hnonred_f,
               hec_f,
               hvarinv_f⟩

/-- Pushing a new node to the heap preserves reducedness of existing sub-BDDs,
because old reachable nodes are unchanged. Proved using push_evaluate + push_ordered. -/
private lemma push_reduced {n s : Nat} {v : Vector (RawNode n) s} {N : RawNode n}
    {hh  : ∀ k : Fin s,       v[k].Bounded k}
    {hh' : ∀ k : Fin (s + 1), (v.push N)[k].Bounded k}
    {p : RawPointer} {hp : p.Bounded s} {hp' : p.Bounded (s + 1)}
    {ho  : Bdd.Ordered ⟨cook_heap v hh,       p.cook hp ⟩}
    {ho' : Bdd.Ordered ⟨cook_heap (v.push N) hh', p.cook hp'⟩}
    (hred : OBdd.Reduced ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩) :
    OBdd.Reduced ⟨⟨cook_heap (v.push N) hh', p.cook hp'⟩, ho'⟩ := by
  -- Key: every reachable .node j in new heap has j.1 < s, and j is reachable in old.
  -- Proof by induction on the Reachable path:
  --   base: root p.cook hp' = .node j, so p = .inr k with k = j.1 < s (from hp).
  --   step: edge from .node k to .node j; by IH k.1 < s; by hh' j.1 < k.1 < s;
  --         same edge exists in old heap since k.1 < s means (v.push N)[k] = v[k].
  have back : ∀ j : Fin (s + 1),
      Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') (.node j) →
      ∃ hj : j.1 < s, Pointer.Reachable (cook_heap v hh) (p.cook hp) (.node ⟨j.1, hj⟩) := by
    -- Generalise the end-point so that the induction hypothesis is strong enough.
    suffices h : ∀ q : Pointer (s + 1),
        Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') q →
        ∀ j : Fin (s + 1), q = .node j →
        ∃ hj : j.1 < s,
          Pointer.Reachable (cook_heap v hh) (p.cook hp) (.node ⟨j.1, hj⟩) from
      fun j hreach => h _ hreach j rfl
    intro q hq
    -- Helper: (.inr jj.1).cook h = .node jj  for any jj : Fin (s+1).
    have cook_inr_node : ∀ (jj : Fin (s+1)) (bnd : RawPointer.Bounded (s+1) (.inr jj.1)),
        RawPointer.cook (.inr jj.1) bnd = .node jj := fun jj _ => by
      simp only [RawPointer.cook, Fin.eta]
    induction hq with
    | refl =>
      intro j hj
      -- p.cook hp' = .node j. Extract p = .inr j.1 via cook_inj, then hp gives j.1 < s.
      have hp_eq : p = .inr j.1 :=
        cook_inj (hj.trans (cook_inr_node j (fun h => by injection h; omega)).symm)
      have hj_lt : j.1 < s := hp hp_eq
      have hcook : p.cook hp = .node ⟨j.1, hj_lt⟩ := by
        subst hp_eq; simp [RawPointer.cook]
      exact ⟨hj_lt, hcook ▸ .refl⟩
    | tail hprev edge ih =>
      intro j hj; subst hj
      -- edge : Edge (cook_heap (v.push N) hh') b (.node j)
      cases edge with
      | low h =>
        rename_i k
        simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook] at h
        -- h : (v.push N)[↑k].lo.cook _ = .node j
        have hlo : (v.push N)[k.1].lo = .inr j.1 :=
          cook_inj (h.trans (cook_inr_node j (fun h => by injection h; omega)).symm)
        have hj_lt_k : j.1 < k.1 :=
          (hh' k).1 (show (v.push N)[k].lo = .inr j.1 by simp [Fin.getElem_fin, hlo])
        obtain ⟨hk_lt, hk_reach⟩ := ih k rfl
        have hj_lt : j.1 < s := Nat.lt_trans hj_lt_k hk_lt
        refine ⟨hj_lt, .tail hk_reach (Edge.low ?_)⟩
        -- simp_rw rewrites (v.push N)[↑k] → v[↑k] inside h (handles dependent bound).
        simp_rw [Vector.getElem_push_lt hk_lt] at h
        simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook]
        exact cook_aux h (hj := hj_lt)
      | high h =>
        rename_i k
        simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook] at h
        have hhi : (v.push N)[k.1].hi = .inr j.1 :=
          cook_inj (h.trans (cook_inr_node j (fun h => by injection h; omega)).symm)
        have hj_lt_k : j.1 < k.1 :=
          (hh' k).2 (show (v.push N)[k].hi = .inr j.1 by simp [Fin.getElem_fin, hhi])
        obtain ⟨hk_lt, hk_reach⟩ := ih k rfl
        have hj_lt : j.1 < s := Nat.lt_trans hj_lt_k hk_lt
        refine ⟨hj_lt, .tail hk_reach (Edge.high ?_)⟩
        simp_rw [Vector.getElem_push_lt hk_lt] at h
        simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook]
        exact cook_aux h (hj := hj_lt)
  -- For any node j reachable from any reachable pointer q in new heap,
  -- j.1 < s and nodes are equiv.
  have sub_back : ∀ (q : Pointer (s + 1)),
      Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') q →
      ∀ j : Fin (s + 1),
      Pointer.Reachable (cook_heap (v.push N) hh') q (.node j) →
      ∃ hj : j.1 < s,
        Node.equiv (cook_heap v hh)[(⟨j.1, hj⟩ : Fin s)] (cook_heap (v.push N) hh')[j] := by
    intro q hq_root j hj_q
    have hj_root := Relation.ReflTransGen.trans hq_root hj_q
    obtain ⟨hj_lt, _⟩ := back j hj_root
    exact ⟨hj_lt, by
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn,
        Vector.getElem_push_lt hj_lt]
      exact Node.equiv_symm RawNode.cook_equiv⟩
  -- Helper: Pointer.equiv for same type implies equality.
  have equiv_eq : ∀ {m : Nat} (a b : Pointer m), Pointer.equiv a b → a = b := by
    intro m a b hab
    cases a with
    | terminal ba =>
      have := hab.1 ba rfl
      exact this ▸ rfl
    | node ja =>
      obtain ⟨jb, hjb_eq, hjab⟩ := hab.2 ja rfl
      rw [hjb_eq]
      congr 1
      exact Fin.ext hjab
  -- Helper: Pointer.equiv is transitive.
  have equiv_trans : ∀ {m1 m2 m3 : Nat} {a : Pointer m1} {b : Pointer m2} {c : Pointer m3},
      Pointer.equiv a b → Pointer.equiv b c → Pointer.equiv a c := by
    intro m1 m2 m3 a b c hab hbc
    constructor
    · intro ba ha
      exact hbc.1 ba (hab.1 ba ha)
    · intro ja hja
      obtain ⟨jb, hjb, hjab⟩ := hab.2 ja hja
      obtain ⟨jc, hjc, hjbc⟩ := hbc.2 jb hjb
      exact ⟨jc, hjc, hjab.trans hjbc⟩
  -- Part 1: NoRedundancy
  constructor
  · intro ⟨q, hq_reach⟩ hred_q
    cases q with
    | terminal b => cases hred_q
    | node j =>
      obtain ⟨hj_lt, hj_reach_old⟩ := back j hq_reach
      cases hred_q with
      | red hlow_eq_high =>
        -- Node.equiv between old and new heaps at index j
        obtain ⟨_, hnode_equiv⟩ := sub_back (.node j) hq_reach j .refl
        obtain ⟨_, hequiv_low, hequiv_high⟩ := hnode_equiv
        -- hequiv_low : Pointer.equiv old_heap[j'].low new_heap[j].low
        -- hequiv_high : Pointer.equiv old_heap[j'].high new_heap[j].high
        -- hlow_eq_high : new_heap[j].low = new_heap[j].high
        -- Therefore old.low ≡ new.low = new.high ≡ old.high
        -- i.e., Pointer.equiv old.low old.high
        have hequiv_high' : Pointer.equiv
            (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].low
            (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].high :=
          equiv_trans hequiv_low (hlow_eq_high ▸ Pointer.equiv_symm hequiv_high)
        -- Since both are in Pointer s, equiv implies equality
        have hred_old : (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].low =
                        (cook_heap v hh)[(⟨j.1, hj_lt⟩ : Fin s)].high :=
          equiv_eq _ _ hequiv_high'
        exact hred.1 ⟨.node ⟨j.1, hj_lt⟩, hj_reach_old⟩ (Pointer.Redundant.red hred_old)
  · -- Part 2: SimilarRP injectivity
    -- Need: if SimilarRP O' rp rq, then rp.val = rq.val
    intro ⟨rp, hrp_reach⟩ ⟨rq, hrq_reach⟩ hsim
    -- hsim : SimilarRP O' ⟨rp, _⟩ ⟨rq, _⟩ (= toTree equality of sub-BDDs)
    -- Case split: both must be same kind (terminal/node) for SimilarRP.
    -- We need the toTree equality for case analysis.
    have htree_sim : OBdd.toTree ⟨⟨cook_heap (v.push N) hh', rp⟩,
          Bdd.ordered_of_reachable hrp_reach⟩ =
        OBdd.toTree ⟨⟨cook_heap (v.push N) hh', rq⟩,
          Bdd.ordered_of_reachable hrq_reach⟩ := hsim
    -- Case analysis on rp
    cases rp with
    | terminal bp =>
      cases rq with
      | terminal bq =>
        -- htree_sim was simplified by cases to: bp = bq (or leaf bp = leaf bq)
        -- Goal: ⟨terminal bp, _⟩ = ⟨terminal bq, _⟩
        simp [OBdd.toTree_terminal'] at htree_sim
        subst htree_sim
        rfl
      | node jq =>
        exact absurd htree_sim (by simp [OBdd.toTree_terminal', OBdd.toTree_node])
    | node jp =>
      cases rq with
      | terminal bq =>
        exact absurd htree_sim (by simp [OBdd.toTree_terminal', OBdd.toTree_node])
      | node jq =>
        -- Both nodes: use push_ordered_aux and toTree transfer
        obtain ⟨hjp_lt, hjp_reach_old⟩ := back jp hrp_reach
        obtain ⟨hjq_lt, hjq_reach_old⟩ := back jq hrq_reach
        -- toTree in new heap = toTree in old heap, for each sub-BDD
        -- Ordered sub-BDDs in old heap
        let jp' : Fin s := ⟨jp.1, hjp_lt⟩
        let jq' : Fin s := ⟨jq.1, hjq_lt⟩
        -- Ordered sub-BDDs in old and new heaps (inferred from reachability).
        have hop  : Bdd.Ordered ⟨cook_heap v hh,         .node jp'⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩)         hjp_reach_old
        have hoq  : Bdd.Ordered ⟨cook_heap v hh,         .node jq'⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩)         hjq_reach_old
        have hop' : Bdd.Ordered ⟨cook_heap (v.push N) hh', .node jp⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap (v.push N) hh', p.cook hp'⟩, ho'⟩) hrp_reach
        have hoq' : Bdd.Ordered ⟨cook_heap (v.push N) hh', .node jq⟩ :=
          Bdd.ordered_of_reachable (O := ⟨⟨cook_heap (v.push N) hh', p.cook hp'⟩, ho'⟩) hrq_reach
        have htree_p :
            OBdd.toTree ⟨⟨cook_heap v hh, Pointer.node jp'⟩, hop⟩ =
            OBdd.toTree ⟨⟨cook_heap (v.push N) hh', Pointer.node jp⟩, hop'⟩ := by
          apply OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq
          · exact sub_back (Pointer.node jp) hrp_reach
          · -- Pointer.equiv (.node jp : Pointer (s+1)) (.node jp' : Pointer s), jp.1 = jp'.1
            constructor
            · intro b hb; exact absurd hb (by simp)
            · intro j hj
              exact ⟨jp', rfl, by have h := Pointer.node.inj hj; subst h; rfl⟩
        have htree_q :
            OBdd.toTree ⟨⟨cook_heap v hh, Pointer.node jq'⟩, hoq⟩ =
            OBdd.toTree ⟨⟨cook_heap (v.push N) hh', Pointer.node jq⟩, hoq'⟩ := by
          apply OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq
          · exact sub_back (Pointer.node jq) hrq_reach
          · constructor
            · intro b hb; exact absurd hb (by simp)
            · intro j hj
              exact ⟨jq', rfl, by have h := Pointer.node.inj hj; subst h; rfl⟩
        -- SimilarRP in old BDD
        have hsim_old : OBdd.SimilarRP ⟨⟨cook_heap v hh, p.cook hp⟩, ho⟩
            ⟨Pointer.node jp', hjp_reach_old⟩
            ⟨Pointer.node jq', hjq_reach_old⟩ := by
          show OBdd.toTree _ = OBdd.toTree _
          rw [htree_p, htree_q]
          exact htree_sim
        have hval_eq := hred.2 hsim_old
        -- hval_eq : (InvImage Eq Subtype.val) ⟨.node jp', _⟩ ⟨.node jq', _⟩
        --         = (.node jp' = .node jq')
        simp only [InvImage, Pointer.node.injEq] at hval_eq
        -- hval_eq : jp' = jq' (as Fin s); since jp.1 = jp'.1 and jq.1 = jq'.1, jp = jq
        have hjpjq : jp.1 = jq.1 := by simpa using Fin.ext_iff.mp hval_eq
        exact congrArg Pointer.node (Fin.ext hjpjq)

/-- Process one entry from the sorted queue.
`hbound` witnesses that the entry's key pointers are bounded by the current heap size. -/
private def process_record {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (entry  : (RawPointer × RawPointer) × Fin m)
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    -- When entry.1 = curkey, curptr correctly represents entry.2.
    (hcurptr_correct : entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    -- When entry.1 ≠ curkey, the freshly pushed node for entry.2 is correct.
    (hnewnode_correct : ¬(entry.1 = curkey) →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps.state.size :=
              ⟨hbound.1, hbound.2⟩
        let ps₁' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I) :
    { p : ProvedState n m × (RawPointer × RawPointer) × RawPointer //
        Invariant O p.1 i ∧
        (p.1.state.ids[entry.2]).isSome ∧
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (p.1.state.ids[k]).isSome) ∧
        ps.state.size ≤ p.1.state.size } :=
  let ⟨key, j⟩ := entry
  -- Helpers for reasoning about ids after set_id.
  have ids_set_self : ∀ (ps0 : ProvedState n m) (ptr : RawPointer),
      (set_id ps0 j ptr).state.ids[j] = some ptr := fun ps0 ptr => by
    show (ps0.state.ids.set j (some ptr))[j] = some ptr
    simp [Vector.getElem_set_self]
  have ids_set_ne : ∀ (ps0 : ProvedState n m) (ptr : RawPointer) (k : Fin m), k ≠ j →
      (set_id ps0 j ptr).state.ids[k] = ps0.state.ids[k] := fun ps0 ptr k hkj => by
    show (ps0.state.ids.set j (some ptr))[k] = ps0.state.ids[k]
    exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hkj.symm)
  if heq : key = curkey then
    -- Isomorphic: assign j to the same output pointer as curptr.
    let ps' := set_id ps j curptr
    ⟨⟨ps', curkey, curptr⟩,
     -- Invariant:
     ⟨fun k hk hreach_k => by
        by_cases hkj : k = j
        · subst hkj
          simp only [Option.isSome_iff_exists]
          exact ⟨curptr, ids_set_self ps curptr⟩
        · rw [ids_set_ne ps curptr k hkj]; exact inv.1 k hk hreach_k,
      fun k ptr hkptr => by
        by_cases hkj : k = j
        · subst hkj
          rw [ids_set_self ps] at hkptr
          simp only [Option.some.injEq] at hkptr; subst hkptr
          exact hcurptr_correct heq
        · rw [ids_set_ne ps curptr k hkj] at hkptr
          exact inv.2 k ptr hkptr⟩,
     -- ids[j].isSome:
     by simp only [Option.isSome_iff_exists]; exact ⟨curptr, ids_set_self ps curptr⟩,
     -- isSome monotone:
     fun k hk => by
       by_cases hkj : k = j
       · subst hkj
         simp only [Option.isSome_iff_exists]
         exact ⟨curptr, ids_set_self ps curptr⟩
       · rw [ids_set_ne ps curptr k hkj]; exact hk,
     -- size unchanged:
     le_refl _⟩
  else
    -- New equivalence class: push a fresh output node, then assign j to it.
    have hN : (RawNode.mk O.1.heap[j].var key.1 key.2).Bounded ps.state.size :=
      ⟨hbound.1, hbound.2⟩
    -- Use non-destructuring let so ps₁ is a transparent let binding.
    let ps₁ : ProvedState n m := (push_node ps ⟨O.1.heap[j].var, key.1, key.2⟩ hN).1
    let ptr : RawPointer             := (push_node ps ⟨O.1.heap[j].var, key.1, key.2⟩ hN).2
    -- These hold by rfl since ps₁ is a transparent let.
    have hps₁_ids : ∀ k : Fin m, ps₁.state.ids[k] = ps.state.ids[k] := fun _ => rfl
    have hps₁_size : ps₁.state.size = ps.state.size + 1 := rfl
    let ps₂ := set_id ps₁ j ptr
    ⟨⟨ps₂, key, ptr⟩,
     -- Invariant:
     ⟨fun k hk hreach_k => by
        by_cases hkj : k = j
        · subst hkj
          simp only [Option.isSome_iff_exists]
          exact ⟨ptr, ids_set_self ps₁ ptr⟩
        · rw [ids_set_ne ps₁ ptr k hkj, hps₁_ids k]
          exact inv.1 k hk hreach_k,
      fun k ptr_k hkptr => by
        by_cases hkj : k = j
        · subst hkj
          rw [ids_set_self ps₁] at hkptr
          simp only [Option.some.injEq] at hkptr; subst hkptr
          exact hnewnode_correct heq
        · -- k ≠ j: ids[k] unchanged through push and set_id
          rw [ids_set_ne ps₁ ptr k hkj, hps₁_ids k] at hkptr
          obtain ⟨hj_k, hptr_k, ho_k, hred_k, heval_k⟩ := inv.2 k ptr_k hkptr
          -- Lift hptr_k to the new (larger) heap size.
          have hptr_k' : ptr_k.Bounded ps₂.state.size :=
            RawPointer.bounded_of_le hptr_k (hps₁_size ▸ Nat.le_succ _)
          -- Lift ordering through push_node (ps₂.state.heap = ps.state.heap.push N by rfl).
          have ho_k' : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr_k.cook hptr_k'⟩ :=
            push_ordered ho_k
          exact ⟨hj_k, hptr_k', ho_k',
                 -- Reduced: push_reduced (sorry'd lemma)
                 push_reduced hred_k,
                 -- Denotation: lift through push_evaluate
                 fun I => (congr_fun (push_evaluate (hu := ho_k)) I).trans (heval_k I)⟩⟩,
     -- ids[j].isSome:
     by simp only [Option.isSome_iff_exists]; exact ⟨ptr, ids_set_self ps₁ ptr⟩,
     -- isSome monotone: push_node doesn't change ids, set_id j ptr adds one entry
     fun k hk => by
       by_cases hkj : k = j
       · subst hkj
         simp only [Option.isSome_iff_exists]
         exact ⟨ptr, ids_set_self ps₁ ptr⟩
       · rw [ids_set_ne ps₁ ptr k hkj, hps₁_ids k]; exact hk,
     -- size grows by 1:
     hps₁_size ▸ Nat.le_succ _⟩

/-- After processing one record, the new curkey'/curptr' pair correctly represents
any entry in the remaining queue whose key matches curkey'. -/
private lemma process_record_curptr_sem {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (head : (RawPointer × RawPointer) × Fin m)
    (tail : List ((RawPointer × RawPointer) × Fin m))
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (hbounds : ∀ entry ∈ head :: tail, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    (hcurptr_sem : ∀ entry ∈ head :: tail, entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    (hnewnode_sem : ∀ entry ∈ head :: tail,
        (hbound_entry : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
        ¬(entry.1 = curkey) →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps.state.size :=
              ⟨hbound_entry.1, hbound_entry.2⟩
        let ps₁' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I) :
    let result := process_record O curkey curptr head ps inv (hbounds head (.head _))
          (hcurptr_sem head (.head _))
          (hnewnode_sem head (.head _) (hbounds head (.head _)))
    let ps' := result.1.1
    let curkey' := result.1.2.1
    let curptr' := result.1.2.2
    ∀ entry ∈ tail, entry.1 = curkey' →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr'.Bounded ps'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps'.state.heap ps'.hh, curptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps'.state.heap ps'.hh, curptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps'.state.heap ps'.hh, curptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I := by
  sorry

/-- After processing one record, pushing a fresh node for non-matching tail entries is correct. -/
private lemma process_record_newnode_sem {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (head : (RawPointer × RawPointer) × Fin m)
    (tail : List ((RawPointer × RawPointer) × Fin m))
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (hbounds : ∀ entry ∈ head :: tail, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    (hcurptr_sem : ∀ entry ∈ head :: tail, entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I)
    (hnewnode_sem : ∀ entry ∈ head :: tail,
        (hbound_entry : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
        ¬(entry.1 = curkey) →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps.state.size :=
              ⟨hbound_entry.1, hbound_entry.2⟩
        let ps₁' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I) :
    let result := process_record O curkey curptr head ps inv (hbounds head (.head _))
          (hcurptr_sem head (.head _))
          (hnewnode_sem head (.head _) (hbounds head (.head _)))
    let ps' := result.1.1
    let curkey' := result.1.2.1
    let curptr' := result.1.2.2
    let hsize_rec := result.2.2.2.2
    ∀ entry ∈ tail,
        (hbound_entry : entry.1.1.Bounded ps'.state.size ∧ entry.1.2.Bounded ps'.state.size) →
        ¬(entry.1 = curkey') →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps'.state.size :=
              ⟨hbound_entry.1, hbound_entry.2⟩
        let ps₁' := (push_node ps' ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps' ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I := by
  sorry

/-- In a non-redundant queue, no entry's key matches the sentinel ⟨.inl false, .inl false⟩. -/
private lemma sentinel_no_match
    (Q : List ((RawPointer × RawPointer) × Fin m))
    (hnonred : ∀ entry ∈ Q, entry.1.1 ≠ entry.1.2) :
    ∀ entry ∈ Q, entry.1 ≠ ((.inl false : RawPointer), (.inl false : RawPointer)) := by
  intro entry hmem heq
  have h := hnonred entry hmem
  have : entry.1.1 = entry.1.2 := by
    have h1 : entry.1.1 = .inl false := congrArg Prod.fst heq
    have h2 : entry.1.2 = .inl false := congrArg Prod.snd heq
    rw [h1, h2]
  exact h this

/-- Thread `process_record` through the entire sorted queue. -/
private def process_queue {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer) :
    (Q : List ((RawPointer × RawPointer) × Fin m)) →
    (ps : ProvedState n m) →
    Invariant O ps i →
    (∀ entry ∈ Q, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
    -- Semantic correctness: when entry's key matches curkey, curptr represents entry.2.
    (hcurptr_sem : ∀ entry ∈ Q, entry.1 = curkey →
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : curptr.Bounded ps.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I) →
    -- Semantic correctness: when entry's key differs from curkey, the fresh push is correct.
    (hnewnode_sem : ∀ entry ∈ Q,
        (hbound_entry : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
        ¬(entry.1 = curkey) →
        let hN : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded ps.state.size :=
              ⟨hbound_entry.1, hbound_entry.2⟩
        let ps₁' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
        let ptr' := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
        let ps₂' := set_id ps₁' entry.2 ptr'
        ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
        ∃ hp : ptr'.Bounded ps₂'.state.size,
        ∃ ho : Bdd.Ordered ⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩,
          OBdd.Reduced ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ ∧
          ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂'.state.heap ps₂'.hh, ptr'.cook hp⟩, ho⟩ I =
               OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I) →
    { ps' : ProvedState n m //
        Invariant O ps' i ∧
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (ps'.state.ids[k]).isSome) ∧
        ∀ entry ∈ Q, (ps'.state.ids[entry.2]).isSome }
  | [], ps, inv, _, _, _ =>
      ⟨ps, inv, fun _ hk => hk, fun _ h => by simp at h⟩
  | head :: tail, ps, inv, hbounds, hcurptr_sem, hnewnode_sem =>
      let result := process_record O curkey curptr head ps inv (hbounds head (.head _))
          (hcurptr_sem head (.head _))
          (hnewnode_sem head (.head _) (hbounds head (.head _)))
      let ps' := result.1.1
      let curkey' := result.1.2.1
      let curptr' := result.1.2.2
      let inv' := result.2.1
      let hhead := result.2.2.1
      let hmono_rec := result.2.2.2.1
      let hsize_rec := result.2.2.2.2
      -- Lift the tail bounds to the (possibly larger) ps'.state.size.
      have hbounds' : ∀ entry ∈ tail,
          entry.1.1.Bounded ps'.state.size ∧ entry.1.2.Bounded ps'.state.size := by
        intro entry hmem
        have := hbounds entry (.tail _ hmem)
        exact ⟨RawPointer.bounded_of_le this.1 hsize_rec,
               RawPointer.bounded_of_le this.2 hsize_rec⟩
      let ⟨ps'', inv'', hmono_tail, htail⟩ :=
        process_queue O curkey' curptr' tail ps' inv' hbounds'
          (process_record_curptr_sem O curkey curptr head tail ps inv hbounds hcurptr_sem hnewnode_sem)
          (process_record_newnode_sem O curkey curptr head tail ps inv hbounds hcurptr_sem hnewnode_sem)
      ⟨ps'', inv'',
       -- isSome monotone: compose record's and tail's monotonicity.
       fun k hk => hmono_tail k (hmono_rec k hk),
       fun entry h => by
         cases h with
         | head =>
           -- head's id was set by process_record; tail preserves it.
           exact hmono_tail head.2 hhead
         | tail _ h => exact htail entry h⟩

/-- Lexicographic comparison on key pairs, used for sorting the queue. -/
private def leKeyPair (a b : RawPointer × RawPointer) : Bool :=
  match decEq a.1 b.1 with
  | isTrue _  => decide (a.2 ≤ b.2)
  | isFalse _ => decide (a.1 ≤ b.1)

/-- Process all input nodes at variable level `i`. -/
private def step {n m : Nat} (O : OBdd n m)
    (vlist : Vector (List (Fin m)) n) (i : Fin n)
    (ps : ProvedState n m) (inv : Invariant O ps i.1)
    (hdiscover_inv : ∀ j ∈ vlist[i],
        O.1.heap[j].var.1 = i.1 ∧ Reachable O.1.heap O.1.root (.node j))
    (hvarinv : VarInvariant O ps) (hallabove : AllAbove ps i.1)
    (hheapinj : HeapInjective ps) :
    { ps' : ProvedState n m //
        Invariant O ps' i.1 ∧
        ∀ j ∈ vlist[i], Reachable O.1.heap O.1.root (.node j) → (ps'.state.ids[j]).isSome } :=
  -- Build the queue: redundant nodes (lid = hid) are resolved immediately;
  -- non-redundant nodes are collected in `queue` as ((lid, hid), j) entries.
  let ⟨⟨ps₁, queue⟩, inv₁, hsize₁, _, hmono₁, hpost₁, hbounds₁, hnonred₁, hec₁, hvarinv₁⟩ :=
    populate_queue O i [] vlist[i] ps inv
      (fun j hj => (hdiscover_inv j hj).1)
      (fun j hj => (hdiscover_inv j hj).2)
      -- empty accumulator: trivially bounded
      (fun _ h => by simp at h)
      -- empty accumulator: trivially non-redundant
      (fun _ h => by simp at h)
      -- empty accumulator: trivially entry-correct
      (fun _ h => by simp at h)
      hvarinv
  -- Sort the queue so that equal-key entries are adjacent (enables iso-merging).
  -- Sentinel (⟨.inl false, .inl false⟩, .inl false): all real entries have key.1 ≠ key.2
  -- (populate_queue only enqueues non-redundant nodes), so the sentinel never matches
  -- any entry — the first element always starts a fresh equivalence class.
  let sorted := queue.mergeSort (fun a b => leKeyPair a.1 b.1)
  -- Process the sorted queue, assigning output pointers to each equivalence class.
  -- Bounds for sorted entries: sorting is a permutation, so bounds transfer from queue.
  have hbounds_sorted : ∀ entry ∈ sorted,
      entry.1.1.Bounded ps₁.state.size ∧ entry.1.2.Bounded ps₁.state.size := by
    intro entry hmem
    have := hbounds₁ entry ((List.Perm.mem_iff (List.mergeSort_perm _ _)).mp hmem)
    exact this
  have hnonred_sorted : ∀ entry ∈ sorted, entry.1.1 ≠ entry.1.2 := by
    intro entry hmem
    exact hnonred₁ entry ((List.Perm.mem_iff (List.mergeSort_perm _ _)).mp hmem)
  have hec_sorted : ∀ entry ∈ sorted, EntryCorrect O ps₁ i.1 entry := by
    intro entry hmem
    exact hec₁ entry ((List.Perm.mem_iff (List.mergeSort_perm _ _)).mp hmem)
  let pq := process_queue O ⟨.inl false, .inl false⟩ (.inl false)
              sorted ps₁ inv₁ hbounds_sorted
              -- hcurptr_sem: sentinel key never matches any real entry (key.1 ≠ key.2 for all entries).
              (fun entry hmem heq => absurd heq (sentinel_no_match sorted hnonred_sorted entry hmem))
              -- hnewnode_sem: pushing a fresh node for non-redundant entries is correct.
              (fun entry hmem hbound_entry _ =>
                let ⟨hreach_e, hvar_e, hlo_ids, hhi_ids, hlo_t, hhi_t⟩ := hec_sorted entry hmem
                sorry)
  ⟨pq.1, pq.2.1, by
    -- Every j ∈ vlist[i] ends up with ids[j].isSome:
    -- either it was resolved as redundant by populate_queue (hpost₁ right branch),
    -- or it was enqueued and process_queue set it (hpost₁ left branch + pq.2.2.2).
    intro j hmem hreach
    have h := hpost₁ j hmem
    cases h with
    | inl hqueue =>
      obtain ⟨key, hmem_q⟩ := hqueue
      -- j was enqueued; sorting is a permutation, so it's still in sorted.
      have hmem_sorted : (key, j) ∈ sorted := List.Perm.mem_iff
        (List.mergeSort_perm _ _) |>.mpr hmem_q
      exact pq.2.2.2 ⟨key, j⟩ hmem_sorted
    | inr hset =>
      -- j was already resolved; process_queue is monotone for isSome.
      exact pq.2.2.1 j hset⟩

-- ---------------------------------------------------------------------------
-- Proof-carrying helpers
-- ---------------------------------------------------------------------------

/-- After processing variable level `i`, the completeness extends to `i - 1`:
every reachable node at any level `≥ i` (not just `> i`) has its id set. -/
private lemma invariant_step_down {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat}
    (inv  : Invariant O ps i)
    (hset : ∀ (j : Fin m), O.1.heap[j].var.1 = i →
              Reachable O.1.heap O.1.root (.node j) → (ps.state.ids[j]).isSome)
    (hi   : 0 < i) :
    Invariant O ps (i - 1) :=
  ⟨fun j hj hreach => by
     have h : i ≤ O.1.heap[j].var.1 := by omega
     rcases h.eq_or_lt with h_eq | h_lt
     · exact hset j h_eq.symm hreach
     · exact inv.1 j h_lt hreach,
   inv.2⟩

/-- Process levels from `i` down to `O.1.heap[r].var`, returning a final state
in which `r`'s id is set and the correctness invariant holds for the root.
`h_le` witnesses that `O.1.heap[r].var.1 ≤ i.1`, maintained by the recursion. -/
private def loop_helper {n m : Nat} (O : OBdd n m) (r : Fin m)
    (hr    : O.1.root = .node r)
    (vlist : Vector (List (Fin m)) n)
    (hdiscover : ∀ (j : Fin m),
        Reachable O.1.heap O.1.root (.node j) →
        j ∈ vlist[O.1.heap[j].var])
    (hdiscover_inv : ∀ (j : Fin m) (ii : Fin n),
        j ∈ vlist[ii] →
        O.1.heap[j].var.1 = ii.1 ∧ Reachable O.1.heap O.1.root (.node j))
    (i    : Fin n)
    (h_le : O.1.heap[r].var.1 ≤ i.1)
    (ps : ProvedState n m) (inv : Invariant O ps i.1)
    (hvarinv : VarInvariant O ps) (hallabove : AllAbove ps i.1)
    (hheapinj : HeapInjective ps) :
    { ps' : ProvedState n m //
        (ps'.state.ids[r]).isSome ∧
        ∀ (ptr : RawPointer), ps'.state.ids[r] = some ptr →
          ∃ hptr : ptr.Bounded ps'.state.size,
            ∃ ho : Bdd.Ordered ⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩,
              OBdd.Reduced ⟨⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩, ho⟩ ∧
              ∀ I, OBdd.evaluate ⟨⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩, ho⟩ I =
                   O.evaluate I } :=
  let ⟨ps₁, inv₁, hset₁⟩ := step O vlist i ps inv (fun j hj => hdiscover_inv j i hj)
    hvarinv hallabove hheapinj
  match h : i.1 - O.1.heap[r].var.1 with
  | Nat.zero =>
    have hi_eq  : O.1.heap[r].var = i :=
      Fin.ext (Nat.le_antisymm h_le (Nat.le_of_sub_eq_zero h))
    have hr_in  : r ∈ vlist[i] :=
      hi_eq ▸ hdiscover r (by rw [← hr]; exact .refl)
    have hrisSome : (ps₁.state.ids[r]).isSome :=
      hset₁ r hr_in (by rw [← hr]; exact .refl)
    ⟨ps₁, hrisSome, fun ptr hkptr =>
      let ⟨hj, hptr, ho, hred, heval⟩ := inv₁.2 r ptr hkptr
      ⟨hptr, ho, hred, fun I => (heval I).trans
        (congrArg (OBdd.evaluate · I)
          (Subtype.ext
            (congrArg (fun root => ({ heap := O.1.heap, root } : Bdd n m)) hr.symm)))⟩⟩
  | Nat.succ j =>
    have hlt    : j + O.1.heap[r].var.1 < n := by
      have := i.isLt; simp only [Nat.succ_eq_add_one] at h; omega
    have hi_pos : 0 < i.1 := by omega
    have inv₁' : Invariant O ps₁ (j + O.1.heap[r].var.1) := by
      have hbase := invariant_step_down inv₁
        (fun k hk hreach => hset₁ k (Fin.ext hk ▸ hdiscover k hreach) hreach)
        hi_pos
      simp only [Nat.succ_eq_add_one] at h
      convert hbase using 1; omega
    loop_helper O r hr vlist hdiscover hdiscover_inv
      ⟨j + O.1.heap[r].var.1, hlt⟩ (Nat.le_add_left _ _) ps₁ inv₁'
      sorry sorry sorry
termination_by i.1 - O.1.heap[r].var.1
decreasing_by simp_all

-- ---------------------------------------------------------------------------
-- Top-level
-- ---------------------------------------------------------------------------

private def zero_vars_to_bool : Bdd 0 m → Bool
  | B => match B.root with
    | .terminal b => b
    | .node j     => False.elim (Nat.not_lt_zero _ B.heap[j].var.2)

def oreduce2 (O : OBdd n m) :
    { p : (s : Nat) × OBdd n s // OBdd.Reduced p.2 ∧ p.2.evaluate = O.evaluate } :=
  match n with
  | .zero =>
    match hroot : O.1.root with
    | .terminal b =>
      ⟨⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩⟩,
       Bdd.reduced_of_terminal,
       by simp [OBdd.evaluate_terminal, OBdd.evaluate_terminal' hroot]⟩
    | .node j => absurd O.1.heap[j].var.isLt (Nat.not_lt_zero _)
  | .succ nn =>
    match hroot : O.1.root with
    | .terminal b =>
      ⟨⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩⟩,
       Bdd.reduced_of_terminal,
       by simp [OBdd.evaluate_terminal, OBdd.evaluate_terminal' hroot]⟩
    | .node r =>
      let ⟨ps, hrisSome, hcorr⟩ :=
        loop_helper O r hroot (OBdd.discover O)
          (fun j hj => OBdd.discover_spec hj)
          (fun j ii hj => OBdd.discover_spec_inv hj)
          ⟨nn, Nat.lt_add_one nn⟩ (Nat.lt_succ_iff.mp O.1.heap[r].var.isLt)
          (provedStateInitial (nn + 1) m)
          (inv_initial (fun j => Nat.lt_succ_iff.mp O.1.heap[j].var.isLt))
          varInvariant_initial allAbove_initial heapInjective_initial
      -- hh is now a direct field on ps — no Classical.choose needed for hh!
      let rid  := (ps.state.ids[r]).get hrisSome
      let hrid := hcorr rid (Option.get_mem hrisSome)
      let hptr : rid.Bounded ps.state.size        := hrid.choose
      let ho   : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, rid.cook hptr⟩ :=
        hrid.choose_spec.choose
      let hred  := hrid.choose_spec.choose_spec.1
      let heval := hrid.choose_spec.choose_spec.2
      ⟨⟨ps.state.size, ⟨⟨cook_heap ps.state.heap ps.hh, rid.cook hptr⟩, ho⟩⟩,
       hred, funext heval⟩

lemma oreduce2_reduced {O : OBdd n m} : OBdd.Reduced (oreduce2 O).1.2 := (oreduce2 O).2.1

@[simp]
lemma oreduce2_evaluate {O : OBdd n m} : (oreduce2 O).1.2.evaluate = O.evaluate :=
  (oreduce2 O).2.2

end Reduce2
