import Bdd.Reduce

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

-- ---------------------------------------------------------------------------
-- Pure proof-carrying algorithm functions
-- ---------------------------------------------------------------------------

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
    { p : ProvedState n m × List ((RawPointer × RawPointer) × Fin m) //
        Invariant O p.1 i.1 ∧
        p.1.state.size = ps.state.size ∧
        -- Accumulator entries are preserved in the output list.
        (∀ entry ∈ acc, entry ∈ p.2) ∧
        -- ids only grow: once set, stays set.
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (p.1.state.ids[k]).isSome) ∧
        ∀ j ∈ l, (∃ key, (key, j) ∈ p.2) ∨ (p.1.state.ids[j]).isSome }
  | [], ps, inv, _, _ =>
      ⟨⟨ps, acc⟩, inv, rfl,
       fun _ he => he,
       fun _ hk => hk,
       fun _ hj => by simp at hj⟩
  | j :: tail, ps, inv, hvar, hreach => by
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
              exact by sorry  -- lid correctly represents sub-BDD at j
            · rw [ids_set_ne k hkj] at hkptr
              exact inv.2 k ptr hkptr
        obtain ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hacc_f, hmono_f, hpost_f⟩ :=
          populate_queue O i acc tail (set_id ps j lid) hinv'
            (fun k hk => hvar   k (.tail _ hk))
            (fun k hk => hreach k (.tail _ hk))
        exact ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hacc_f,
               fun k hk => hmono_f k (by
                 by_cases hkj : k = j
                 · subst hkj; simp [ids_set_self]
                 · rw [ids_set_ne k hkj]; exact hk),
               fun k hk => by
                 cases hk with
                 | head =>
                   right; exact hmono_f j (by simp [ids_set_self])
                 | tail _ hk' => exact hpost_f k hk'⟩
      · -- Non-redundant: add ((lid, hid), j) to accumulator; recurse unchanged.
        obtain ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f, hacc_f, hmono_f, hpost_f⟩ :=
          populate_queue O i (⟨⟨lid, hid⟩, j⟩ :: acc) tail ps inv
            (fun k hk => hvar   k (.tail _ hk))
            (fun k hk => hreach k (.tail _ hk))
        exact ⟨⟨ps_f, list_f⟩, hinv_f, hsize_f,
               fun e he => hacc_f e (.tail _ he),
               hmono_f,
               fun k hk => by
                 cases hk with
                 | head => left; exact ⟨⟨lid, hid⟩, hacc_f _ (.head _)⟩
                 | tail _ hk' => exact hpost_f k hk'⟩

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
  -- This is the content of push_ordered_aux (private in Basic.lean).
  have back : ∀ j : Fin (s + 1),
      Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') (.node j) →
      ∃ hj : j.1 < s, Pointer.Reachable (cook_heap v hh) (p.cook hp) (.node ⟨j.1, hj⟩) := by
    intro j hreach; exact by sorry
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
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) :
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
          exact by sorry  -- curptr correctly represents j (semantic)
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
          exact by sorry  -- new node correctly represents j (semantic)
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

/-- Thread `process_record` through the entire sorted queue. -/
private def process_queue {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer) :
    (Q : List ((RawPointer × RawPointer) × Fin m)) →
    (ps : ProvedState n m) →
    Invariant O ps i →
    (∀ entry ∈ Q, entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) →
    { ps' : ProvedState n m //
        Invariant O ps' i ∧
        (∀ k : Fin m, (ps.state.ids[k]).isSome → (ps'.state.ids[k]).isSome) ∧
        ∀ entry ∈ Q, (ps'.state.ids[entry.2]).isSome }
  | [], ps, inv, _ =>
      ⟨ps, inv, fun _ hk => hk, fun _ h => by simp at h⟩
  | head :: tail, ps, inv, hbounds =>
      let ⟨⟨ps', _, curptr'⟩, inv', hhead, hmono_rec, hsize_rec⟩ :=
        process_record O curkey curptr head ps inv (hbounds head (.head _))
      -- Lift the tail bounds to the (possibly larger) ps'.state.size.
      have hbounds' : ∀ entry ∈ tail,
          entry.1.1.Bounded ps'.state.size ∧ entry.1.2.Bounded ps'.state.size := by
        intro entry hmem
        have := hbounds entry (.tail _ hmem)
        exact ⟨RawPointer.bounded_of_le this.1 hsize_rec,
               RawPointer.bounded_of_le this.2 hsize_rec⟩
      let ⟨ps'', inv'', hmono_tail, htail⟩ :=
        process_queue O curkey curptr' tail ps' inv' hbounds'
      ⟨ps'', inv'',
       -- isSome monotone: compose record's and tail's monotonicity.
       fun k hk => hmono_tail k (hmono_rec k hk),
       fun entry h => by
         cases h with
         | head =>
           -- head's id was set by process_record; tail preserves it.
           exact hmono_tail head.2 hhead
         | tail _ h => exact htail entry h⟩

/-- Process all input nodes at variable level `i`. -/
private def step {n m : Nat} (O : OBdd n m)
    (vlist : Vector (List (Fin m)) n) (i : Fin n)
    (ps : ProvedState n m) (inv : Invariant O ps i.1) :
    { ps' : ProvedState n m //
        Invariant O ps' i.1 ∧
        ∀ j ∈ vlist[i], Reachable O.1.heap O.1.root (.node j) → (ps'.state.ids[j]).isSome } := by
  sorry

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
    (i    : Fin n)
    (h_le : O.1.heap[r].var.1 ≤ i.1)
    (ps : ProvedState n m) (inv : Invariant O ps i.1) :
    { ps' : ProvedState n m //
        (ps'.state.ids[r]).isSome ∧
        ∀ (ptr : RawPointer), ps'.state.ids[r] = some ptr →
          ∃ hptr : ptr.Bounded ps'.state.size,
            ∃ ho : Bdd.Ordered ⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩,
              OBdd.Reduced ⟨⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩, ho⟩ ∧
              ∀ I, OBdd.evaluate ⟨⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩, ho⟩ I =
                   O.evaluate I } :=
  let ⟨ps₁, inv₁, hset₁⟩ := step O vlist i ps inv
  match h : i.1 - O.1.heap[r].var.1 with
  | Nat.zero =>
    have hi_eq  : O.1.heap[r].var = i :=
      Fin.ext (Nat.le_antisymm h_le (Nat.le_of_sub_eq_zero h))
    have hr_in  : r ∈ vlist[i] :=
      hi_eq ▸ hdiscover r (by rw [← hr]; exact .refl)
    have hrisSome : (ps₁.state.ids[r]).isSome :=
      hset₁ r hr_in (by rw [← hr]; exact .refl)
    ⟨ps₁, hrisSome, by sorry⟩
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
    loop_helper O r hr vlist hdiscover
      ⟨j + O.1.heap[r].var.1, hlt⟩ (Nat.le_add_left _ _) ps₁ inv₁'
termination_by i.1 - O.1.heap[r].var.1
decreasing_by simp_all

-- ---------------------------------------------------------------------------
-- Top-level
-- ---------------------------------------------------------------------------

private def zero_vars_to_bool : Bdd 0 m → Bool
  | B => match B.root with
    | .terminal b => b
    | .node j     => False.elim (Nat.not_lt_zero _ B.heap[j].var.2)

def oreduce2 (O : OBdd n m) : (s : Nat) × OBdd n s :=
  match n with
  | .zero =>
    ⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal (zero_vars_to_bool O.1)⟩,
         Bdd.Ordered_of_terminal⟩⟩
  | .succ nn =>
    match hroot : O.1.root with
    | .terminal b =>
      ⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩⟩
    | .node r =>
      let ⟨ps, hrisSome, hcorr⟩ :=
        loop_helper O r hroot (OBdd.discover O)
          (fun j hj => OBdd.discover_spec hj)
          ⟨nn, Nat.lt_add_one nn⟩ (Nat.lt_succ_iff.mp O.1.heap[r].var.isLt)
          (provedStateInitial (nn + 1) m)
          (inv_initial (fun j => Nat.lt_succ_iff.mp O.1.heap[j].var.isLt))
      -- hh is now a direct field on ps — no Classical.choose needed for hh!
      let rid  := (ps.state.ids[r]).get hrisSome
      let hrid := hcorr rid (Option.get_mem hrisSome)
      let hptr : rid.Bounded ps.state.size        := hrid.choose
      let ho   : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, rid.cook hptr⟩ :=
        hrid.choose_spec.choose
      ⟨ps.state.size, ⟨⟨cook_heap ps.state.heap ps.hh, rid.cook hptr⟩, ho⟩⟩

lemma oreduce2_reduced {O : OBdd n m} : OBdd.Reduced (oreduce2 O).2 := sorry

@[simp]
lemma oreduce2_evaluate {O : OBdd n m} : (oreduce2 O).2.evaluate = O.evaluate := sorry

end Reduce2
