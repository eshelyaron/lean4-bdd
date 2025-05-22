import Bdd.Basic

namespace Trim

private def trim_pointer : Pointer m → Pointer (k + 1)
  | .terminal b => .terminal b
  | .node j => .node ⟨j.1 % (k + 1), Nat.mod_lt j.1 (Nat.zero_lt_succ k)⟩

private def trim_node : Node n m → Node n (k + 1)
  | ⟨v, l, h⟩ => ⟨v, trim_pointer l, trim_pointer h⟩

def trim (B : Bdd n m) (h1 : k ≤ m) (h2 : ∀ j : Fin m, Pointer.Reachable B.heap B.root (.node j) → j < k) :
    Bdd n k :=
  match k with
  | .zero =>
    match h : B.root with
    | .terminal b => ⟨Vector.emptyWithCapacity 0, .terminal b⟩
    | .node j => (by rw [h] at h2; have := h2 j .refl; contradiction)
  | .succ l =>
    ⟨Vector.cast (min_eq_left h1) (Vector.map trim_node (B.heap.take (l + 1))), trim_pointer B.root⟩

private def untrim_pointer (h : k ≤ m) : Pointer k → Pointer m
  | .terminal b => .terminal b
  | .node j => .node ⟨j.1, Fin.val_lt_of_le _ h⟩

private def untrim_node (h1 : k ≤ m) : Node n k → Node n m
  | ⟨v, l, h⟩ => ⟨v, untrim_pointer h1 l, untrim_pointer h1 h⟩

private def untrim (B : Bdd (n + 1) k) (h1 : k ≤ m) : Bdd (n + 1) m :=
  ⟨ Vector.map
      (untrim_node h1)
      (Vector.cast
        (by omega)
        (B.heap ++ (Vector.replicate (m - k) (⟨0, .terminal false, .terminal false⟩ : Node (n + 1) k)))),
    untrim_pointer h1 B.root
  ⟩

private lemma trim_induction {B : Bdd n m} {h1 : k ≤ m} {h2} {motive : ∀ k, Bdd n k → Prop}
    (base : ∀ b, B.root = .terminal b → motive 0 ⟨(Vector.emptyWithCapacity 0), .terminal b⟩)
    (step : ∀ l (hl : l + 1 ≤ m), (∀ j : Fin m, Pointer.Reachable B.heap B.root (.node j) → j < l + 1) → motive (l + 1) ⟨Vector.cast (min_eq_left hl) (Vector.map trim_node (B.heap.take (l + 1))), trim_pointer B.root⟩) :
    motive k (trim B h1 h2) := by
  unfold trim
  split
  next h1 h2 =>
    split
    next b heq => exact base b heq
    next j heq => rw [heq] at h2; have := h2 j .refl; contradiction
  next l h1 h2 => exact step l h1 h2

private lemma aux {n m} {B : Bdd n m} {l} {j} (h1 : l + 1 ≤ m) (h2 : j < l + 1) :
    ((Vector.map Trim.trim_node B.heap).extract 0 (l + 1))[j] =
    (Vector.map (Trim.trim_node (k := l)) B.heap)[j] := by
  rw [Vector.getElem_extract]
  simp

private lemma aux' {B : Bdd n m} {l} {j} (h1 : l + 1 ≤ m) (h2 : j < l + 1) :
    ((Vector.map Trim.trim_node B.heap).extract 0 (l + 1))[j].low =
    (Vector.map (Trim.trim_node (k := l)) B.heap)[j].low := by
  congr 1
  exact aux h1 h2

private lemma untrim_point_trim_point (p : Pointer m) (_ : l + 1 ≤ m) (hp : ∀ j, p = .node j → j < l + 1) : (untrim_pointer (k := l + 1) h (trim_pointer p)) = p := by
  simp only [trim_pointer]
  split
  next => simp [untrim_pointer]
  next j =>
    simp only [untrim_pointer]
    congr
    simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
    apply hp
    rfl

private lemma untrim_point_trim_root : (untrim_pointer h1 (trim B h1 h2).root) = B.root := by
  simp only [trim]
  split
  next k h1 h2 =>
    split
    next => simp_all [untrim_pointer]
    next j hj => rw [hj] at h2; have := h2 j .refl; contradiction
  next l h1 h2 =>
    simp only [Nat.succ_eq_add_one]
    apply untrim_point_trim_point
    · simp_all
    · intro j hj
      apply h2
      rw [← hj]
      left

private lemma untrim_point_trim_heap_low {B : Bdd n m} {j : Fin k} {h1 : k ≤ m} {hj : Pointer.Reachable B.heap B.root (Pointer.node ⟨j.1, by omega⟩)} {h2} :
    (untrim_pointer h1 (trim B h1 h2).heap[j.1].low) = (B.heap[j.1]'(by omega)).low := by
  have := trim_induction (h2 := h2) (h1 := h1) (motive := fun k' B' ↦ ∀ (h1' : k' ≤ m) (j' : Fin k'), Pointer.Reachable B.heap B.root (.node ⟨j', by omega⟩) → Trim.untrim_pointer h1' B'.heap[j'].low = B.heap[j'].low)
  apply this
  · intro _ _ _ ⟨_, _⟩; contradiction
  · intro l hl hl2 h1' j' hj'
    simp only [Fin.getElem_fin, Vector.getElem_cast]
    simp only [Vector.take_eq_extract, Vector.map_extract]
    have := aux h1' (j := j') (B := B) (by omega)
    calc _
      _ = Trim.untrim_pointer h1' ((Vector.map Trim.trim_node B.heap))[j'.1].low := by
        congr 1
        congr 1
      _ = B.heap[j'.1].low := by
        simp only [Vector.getElem_map]
        simp [trim_node]
        rw [untrim_point_trim_point (h := hl)]
        rfl
        · exact hl
        · intro j'' hj''
          apply hl2
          right
          · exact hj'
          · left
            exact hj''
  · exact hj

private lemma untrim_point_trim_heap_high {B : Bdd n m} {j : Fin k} {h1 : k ≤ m} {hj : Pointer.Reachable B.heap B.root (Pointer.node ⟨j.1, by omega⟩)} {h2} :
    (untrim_pointer h1 (trim B h1 h2).heap[j.1].high) = (B.heap[j.1]'(by omega)).high := by
  have := trim_induction (h2 := h2) (h1 := h1) (motive := fun k' B' ↦ ∀ (h1' : k' ≤ m) (j' : Fin k'), Pointer.Reachable B.heap B.root (.node ⟨j', by omega⟩) → Trim.untrim_pointer h1' B'.heap[j'].high = B.heap[j'].high)
  apply this
  · intro _ _ _ ⟨_, _⟩; contradiction
  · intro l hl hl2 h1' j' hj'
    simp only [Fin.getElem_fin, Vector.getElem_cast]
    simp only [Vector.take_eq_extract, Vector.map_extract]
    have := aux h1' (j := j') (B := B) (by omega)
    calc _
      _ = Trim.untrim_pointer h1' ((Vector.map Trim.trim_node B.heap))[j'.1].high := by
        congr 1
        congr 1
      _ = B.heap[j'.1].high := by
        simp only [Vector.getElem_map]
        simp [trim_node]
        rw [untrim_point_trim_point (h := hl)]
        rfl
        · exact hl
        · intro j'' hj''
          apply hl2
          right
          · exact hj'
          · right
            exact hj''
  · exact hj

private lemma trim_reachable_and_edge
    (hb : Pointer.Reachable (trim B h1 h2).heap (trim B h1 h2).root b) :
    Pointer.Reachable B.heap B.root (untrim_pointer h1 b) ∧
    (∀ c, Edge (trim B h1 h2).heap b c → Edge B.heap (untrim_pointer h1 b) (untrim_pointer h1 c)) := by
  induction hb with
  | refl =>
    have hr : Pointer.Reachable B.heap B.root (Trim.untrim_pointer h1 (trim B h1 h2).root) := by
      rw [untrim_point_trim_root]; left
    constructor
    · exact hr
    · intro c e
      simp [untrim_point_trim_root]
      simp [untrim_point_trim_root] at hr
      cases hh : (trim B h1 h2).root with
      | terminal t =>
        rw [hh] at e
        contradiction
      | node j' =>
        rw [hh] at e
        have : untrim_pointer h1 (Pointer.node j') = B.root := by
          rw [← hh]
          simp [untrim_point_trim_root]
        cases e with
        | low he =>
          rw [← this]
          left
          rw [← he]
          simp only [Fin.getElem_fin]
          symm
          apply untrim_point_trim_heap_low
          rw [← this]
          left
        | high he =>
          rw [← this]
          right
          rw [← he]
          simp only [Fin.getElem_fin]
          symm
          apply untrim_point_trim_heap_high
          rw [← this]
          left
  | tail r e ih =>
    rename_i b c
    constructor
    · right
      · exact ih.1
      · exact ih.2 _ e
    · intro d hd
      cases hd with
      | low hd =>
        left
        rw [← hd]
        simp only [Fin.getElem_fin]
        symm
        apply untrim_point_trim_heap_low
        right
        · exact ih.1
        · exact ih.2 _ e
      | high hd =>
        right
        rw [← hd]
        simp only [Fin.getElem_fin]
        symm
        apply untrim_point_trim_heap_high
        right
        · exact ih.1
        · exact ih.2 _ e

lemma trim_ordered {B : Bdd n m} (o : B.Ordered) {h1 : k ≤ m} {h2} : (trim B h1 h2).Ordered := by
  simp only [trim]
  split
  next _ _ _ h2 =>
    split
    next => exact Bdd.Ordered_of_terminal
    next j hj => rw [hj] at h2; have := h2 j .refl; contradiction
  next _ _ _ l h1 h2 =>
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Nat.succ_eq_add_one]
    have := @o (⟨untrim_pointer (by simp_all) x, (trim_reachable_and_edge (h2 := h2) hx).1⟩ : B.RelevantPointer)
               (⟨untrim_pointer (by simp_all) y, (trim_reachable_and_edge (h2 := h2) hy).1⟩ : B.RelevantPointer)
               ((trim_reachable_and_edge (h1 := h1) (h2 := h2) hx).2 y hxy)
    simp only [Bdd.RelevantMayPrecede, Pointer.MayPrecede, Nat.succ_eq_add_one] at this
    convert this using 1
    · cases heq : x with
      | terminal => simp [Trim.untrim_pointer]
      | node j =>
        have := trim_reachable_and_edge (h1 := h1) (h2 := h2) hx
        rw [heq] at this
        simp only [Vector.take_eq_extract, Vector.map_extract, Nat.succ_eq_add_one,
          Pointer.toVar_node_eq, Fin.getElem_fin, Vector.getElem_cast, Fin.coe_eq_castSucc,
          untrim_pointer, Fin.castSucc_inj]
        calc _
          _ = (Vector.map (Trim.trim_node (k := l)) B.heap)[j.1].var := by
            congr 1
            apply aux <;> omega
          _ = (Trim.trim_node (k := l + 1) B.heap[j.1]).var := by simp; rfl
    · cases heq : y with
      | terminal => simp [Trim.untrim_pointer]
      | node j =>
        have := trim_reachable_and_edge (h1 := h1) (h2 := h2) hy
        rw [heq] at this
        simp only [Vector.take_eq_extract, Vector.map_extract, Nat.succ_eq_add_one,
          Pointer.toVar_node_eq, Fin.getElem_fin, Vector.getElem_cast, Fin.coe_eq_castSucc,
          untrim_pointer, Fin.castSucc_inj]
        calc _
          _ = (Vector.map (Trim.trim_node (k := l)) B.heap)[j.1].var := by
            congr 1
            exact aux (B := B) (j := j.1) (l := l) h1 (h2 ⟨j.1, by omega⟩ this.1)
          _ = (Trim.trim_node (k := l + 1) B.heap[j.1]).var := by simp; rfl

def otrim (O : OBdd n m) (h1 : k ≤ m) (h2 : ∀ j : Fin m, Pointer.Reachable O.1.heap O.1.root (.node j) → j < k) :
    OBdd n k := ⟨trim O.1 h1 h2, trim_ordered O.2⟩

lemma otrim_reduced {O : OBdd n m} {h1 : k ≤ m} {h2} :
    OBdd.Reduced O → OBdd.Reduced (otrim O h1 h2) := by
  sorry

lemma otrim_evaluate {O : OBdd n m} {h1 : k ≤ m} {h2} :
    OBdd.evaluate (otrim O h1 h2) = O.evaluate := by
  sorry

end Trim
