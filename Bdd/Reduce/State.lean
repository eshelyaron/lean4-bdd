module

public import Bdd.Basic
import Bdd.Collect
public import Mathlib.Data.Sum.Order

open Pointer
open Bdd
open RawBdd

namespace Reduce

public instance : LinearOrder RawPointer := inferInstanceAs (LinearOrder (Bool ⊕ₗ Nat))

lemma rawPointer_le_refl (a : RawPointer) : a ≤ a := le_refl a
lemma rawPointer_le_total (a b : RawPointer) : a ≤ b ∨ b ≤ a := le_total a b
lemma rawPointer_le_trans {a b c : RawPointer} : a ≤ b → b ≤ c → a ≤ c := le_trans
lemma rawPointer_le_antisymm {a b : RawPointer} : a ≤ b → b ≤ a → a = b := le_antisymm

@[expose]
public def leKeyPair (a b : RawPointer × RawPointer) : Bool :=
  if a.1 = b.1 then decide (a.2 ≤ b.2) else decide (a.1 ≤ b.1)

@[expose]
public def KeyLE (a b : RawPointer × RawPointer) : Prop := leKeyPair a b = true

public lemma keyLE_refl (a : RawPointer × RawPointer) : KeyLE a a := by
  unfold KeyLE leKeyPair
  rw [if_pos rfl]
  exact decide_eq_true (rawPointer_le_refl a.2)

lemma keyLE_total (a b : RawPointer × RawPointer) : KeyLE a b ∨ KeyLE b a := by
  unfold KeyLE leKeyPair
  by_cases h1 : a.1 = b.1
  · rw [if_pos h1, if_pos h1.symm]
    rcases rawPointer_le_total a.2 b.2 with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    rcases rawPointer_le_total a.1 b.1 with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)

public lemma keyLE_antisymm {a b : RawPointer × RawPointer} : KeyLE a b → KeyLE b a → a = b := by
  unfold KeyLE leKeyPair
  by_cases h1 : a.1 = b.1
  · rw [if_pos h1, if_pos h1.symm]
    intro hab hba
    exact Prod.ext h1 (rawPointer_le_antisymm (of_decide_eq_true hab) (of_decide_eq_true hba))
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    intro hab hba
    exact absurd (rawPointer_le_antisymm (of_decide_eq_true hab) (of_decide_eq_true hba)) h1

public lemma keyLE_trans {a b c : RawPointer × RawPointer} : KeyLE a b → KeyLE b c → KeyLE a c := by
  unfold KeyLE leKeyPair
  intro hab hbc
  by_cases h1 : a.1 = b.1 <;> by_cases h2 : b.1 = c.1
  · -- a.1 = b.1 and b.1 = c.1
    have h13 : a.1 = c.1 := h1.trans h2
    rw [if_pos h1] at hab
    rw [if_pos h2] at hbc
    rw [if_pos h13]
    exact decide_eq_true
      (rawPointer_le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  · -- a.1 = b.1 and b.1 ≠ c.1
    have h13 : a.1 ≠ c.1 := h1 ▸ h2
    rw [if_neg h2] at hbc
    rw [if_neg h13]
    rw [h1]
    exact hbc
  · -- a.1 ≠ b.1 and b.1 = c.1
    have h13 : a.1 ≠ c.1 := h2 ▸ h1
    rw [if_neg h1] at hab
    rw [if_neg h13]
    rw [← h2]
    exact hab
  · -- a.1 ≠ b.1 and b.1 ≠ c.1
    rw [if_neg h1] at hab
    rw [if_neg h2] at hbc
    have hac : a.1 ≤ c.1 :=
      rawPointer_le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)
    have h13 : a.1 ≠ c.1 := by
      intro he
      have hca : c.1 ≤ a.1 := he ▸ rawPointer_le_refl a.1
      have hba : b.1 ≤ a.1 := rawPointer_le_trans (of_decide_eq_true hbc) hca
      exact h1 (rawPointer_le_antisymm (of_decide_eq_true hab) hba)
    rw [if_neg h13]
    exact decide_eq_true hac

public lemma keyLE_sorted_mergeSort {m : Nat}
    (l : List ((RawPointer × RawPointer) × Fin m)) :
    (l.mergeSort (fun a b => leKeyPair a.1 b.1)).Pairwise (fun a b => KeyLE a.1 b.1) := by
  have htrans : ∀ (a b c : (RawPointer × RawPointer) × Fin m),
      leKeyPair a.1 b.1 → leKeyPair b.1 c.1 → leKeyPair a.1 c.1 :=
    fun a b c hab hbc => keyLE_trans (a := a.1) (b := b.1) (c := c.1) hab hbc
  have htotal : ∀ (a b : (RawPointer × RawPointer) × Fin m),
      leKeyPair a.1 b.1 || leKeyPair b.1 a.1 :=
    fun a b => by
      rcases keyLE_total a.1 b.1 with h | h
      · exact (Bool.or_eq_true _ _).mpr (Or.inl h)
      · exact (Bool.or_eq_true _ _).mpr (Or.inr h)
  exact (List.pairwise_mergeSort htrans htotal l).imp (fun h => h)

public structure State (n) (m) where
  size : Nat
  heap : Vector (RawNode n) size
  ids  : Vector (Option RawPointer) m

public structure ProvedState (n m : Nat) where
  state : State n m
  hh    : ∀ k : Fin state.size, state.heap[k].Bounded k

def initial (n m : Nat) : State n m :=
  ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩

public def provedStateInitial (n m : Nat) : ProvedState n m where
  state := ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩
  hh := fun k => k.elim0

@[expose]
public def get_id {n m : Nat} (ps : ProvedState n m) (p : Pointer m)
    (h : ∀ j, p = .node j → (ps.state.ids[j]).isSome) : RawPointer :=
  match p with
  | .terminal b => .inl b
  | .node j     => (ps.state.ids[j]).get (h j rfl)

/-- Record that input node `j` maps to output pointer `p`. -/
@[expose]
public def set_id {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) : ProvedState n m :=
  { state := { size := ps.state.size, heap := ps.state.heap, ids := ps.state.ids.set j (some p) },
    hh    := ps.hh }

public lemma set_id_self {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) :
    (set_id ps j p).state.ids[j] = some p := by
  show (ps.state.ids.set j (some p))[j] = some p
  simp [Vector.getElem_set_self]

public lemma set_id_ne {n m : Nat} (ps : ProvedState n m) (j k : Fin m) (p : RawPointer)
    (h : k ≠ j) : (set_id ps j p).state.ids[k] = ps.state.ids[k] := by
  show (ps.state.ids.set j (some p))[k] = ps.state.ids[k]
  exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h.symm)

@[expose]
public def push_node {n m : Nat} (ps : ProvedState n m) (N : RawNode n)
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

/-- Injectivity of `toTree` for sub-BDDs sharing the same heap, given heap index-injectivity. -/
lemma structural_canonical_key {n s : Nat} {M : Vector (Node n s) s}
    (node_inj : ∀ (kp kq : Fin s),
        M[kp].var = M[kq].var → M[kp].low = M[kq].low → M[kp].high = M[kq].high → kp = kq) :
    ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
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
      have hlo_eq : M[jp].low = M[jq].low := by
        have h1 : P.1.heap[jp].low = Q.1.heap[jq].low := hlo_eq_root
        rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
      have hhi_eq : M[jp].high = M[jq].high := by
        have h1 : P.1.heap[jp].high = Q.1.heap[jq].high := hhi_eq_root
        rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
      have hvar_eq : M[jp].var = M[jq].var := by
        have h1 : P.1.heap[jp].var = Q.1.heap[jq].var :=
          Fin.ext (congrArg Fin.val hvar)
        rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
      exact congrArg _ (node_inj jp jq hvar_eq hlo_eq hhi_eq)

/-- In a structurally canonical heap (no two positions have the same raw node),
    any ordered BDD is reduced. -/
public lemma structural_canonical_reduced {n s : Nat}
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
  let M := cook_heap v hh
  have key : ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
      OBdd.toTree P = OBdd.toTree Q → P.1.root = Q.1.root :=
    structural_canonical_key node_inj
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

@[expose]
public def Invariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat) : Prop :=
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

public lemma inv_initial {n m : Nat} {O : OBdd n m} {i : Nat}
    (hi : ∀ j : Fin m, O.1.heap[j].var.1 ≤ i) :
    Invariant O (provedStateInitial n m) i :=
  ⟨fun j h _ => absurd h (Nat.not_lt.mpr (hi j)),
   fun j ptr h => by simp [provedStateInitial] at h⟩

public lemma Invariant.ids_isSome {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat} (inv : Invariant O ps i)
    {j : Fin m}
    (hvar  : i < O.1.heap[j].var.1)
    (hreach : Reachable O.1.heap O.1.root (.node j)) :
    (ps.state.ids[j]).isSome :=
  inv.1 j hvar hreach

/-- When ids[j] = some (.inr k), the output node's var ≥ the input node's var. -/
@[expose]
public def VarInvariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) : Prop :=
  ∀ (j : Fin m) (k : Fin ps.state.size),
    ps.state.ids[j] = some (.inr k.1) →
    O.1.heap[j].var.1 ≤ ps.state.heap[k].va.1

@[expose]
public def AllAbove {n m : Nat} (ps : ProvedState n m) (i : Nat) : Prop :=
  ∀ k : Fin ps.state.size, i < ps.state.heap[k].va.1

/-- The heap is injective: no two positions have the same raw node. -/
@[expose]
public def HeapInjective {n : Nat} (ps : ProvedState n m) : Prop :=
  ∀ k1 k2 : Fin ps.state.size, ps.state.heap[k1] = ps.state.heap[k2] → k1 = k2

public lemma varInvariant_initial {n m : Nat} {O : OBdd n m} :
    VarInvariant O (provedStateInitial n m) := by
  intro j k
  exact absurd k.isLt (by simp [provedStateInitial])

public lemma allAbove_initial {n m : Nat} {i : Nat} :
    AllAbove (provedStateInitial n m) i := by
  intro k
  exact absurd k.isLt (by simp [provedStateInitial])

public lemma heapInjective_initial {n m : Nat} :
    HeapInjective (provedStateInitial n m) := by
  intro k1
  exact absurd k1.isLt (by simp [provedStateInitial])

@[expose]
public def EntryCorrect {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat)
    (entry : (RawPointer × RawPointer) × Fin m) : Prop :=
  Reachable O.1.heap O.1.root (.node entry.2) ∧
  O.1.heap[entry.2].var.1 = i ∧
  (∀ l, O.1.heap[entry.2].low = .node l → ps.state.ids[l] = some entry.1.1) ∧
  (∀ l, O.1.heap[entry.2].high = .node l → ps.state.ids[l] = some entry.1.2) ∧
  (∀ b, O.1.heap[entry.2].low = .terminal b → entry.1.1 = .inl b) ∧
  (∀ b, O.1.heap[entry.2].high = .terminal b → entry.1.2 = .inl b)

/-- The BDD obtained by pushing a fresh node for `entry` is ordered, reduced, and
    evaluates like the original sub-BDD at `entry.2`. -/
public abbrev NodePushedCorrectly {n m : Nat} (O : OBdd n m) (ps : ProvedState n m)
    (entry : (RawPointer × RawPointer) × Fin m)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) : Prop :=
  let N    : RawNode n := ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩
  let hN   : N.Bounded ps.state.size := ⟨hbound.1, hbound.2⟩
  let ps₁  := (push_node ps N hN).1
  let ptr  := (push_node ps N hN).2
  let ps₂  := set_id ps₁ entry.2 ptr
  ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
  ∃ hp : ptr.Bounded ps₂.state.size,
  ∃ ho : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩,
    OBdd.Reduced ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ ∧
    ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ I =
         OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I

/-- The current pointer `curptr` correctly represents the sub-BDD at `entry.2`. -/
public abbrev CurptrSemantic {n m : Nat} (O : OBdd n m) (ps : ProvedState n m)
    (curptr : RawPointer) (entry : (RawPointer × RawPointer) × Fin m) : Prop :=
  ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
  ∃ hp : curptr.Bounded ps.state.size,
  ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
    OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
    ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
         OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I

end Reduce
