import Bdd.Basic

namespace Trim

private def trim_pointer : Pointer m → Pointer (k + 1)
  | .terminal b => .terminal b
  | .node j => .node ⟨j.1 % (k + 1), Nat.mod_lt j.1 (Nat.zero_lt_succ k)⟩

private lemma trim_pointer_injective {hp : ∀ j : Fin m, p = .node j → j.1 < l + 1} {hq : ∀ j : Fin m, q = .node j → j.1 < l + 1} :
    trim_pointer (k := l) (m := m) p = trim_pointer q → p = q := by
  intro h
  cases p with
  | terminal _ =>
    cases q <;> simp_all [trim_pointer]
  | node _ =>
    cases q <;> simp_all [trim_pointer]
    rw [Nat.mod_eq_of_lt hp] at h
    rw [Nat.mod_eq_of_lt hq] at h
    exact Fin.eq_of_val_eq h

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

private lemma untrim_pointer_injective {h : k ≤ m} : Function.Injective (untrim_pointer h) := by
  intro x y hxy
  cases x with
  | terminal _ =>
    cases y <;> simp_all [untrim_pointer]
  | node _ =>
    cases y <;> simp_all [untrim_pointer]
    exact Fin.eq_of_val_eq hxy

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

private lemma trim_root_terminal {B : Bdd n m} {h1 : k ≤ m} {h2} :
    (trim B h1 h2).root = .terminal b → B.root = .terminal b := by
  intro h
  unfold trim at h
  split at h
  next h1 h2 =>
    split at h
    next => simp_all
    next j hj =>
      rw [hj] at h2
      have := h2 j .refl
      contradiction
  next l h1 h2 =>
    simp_all only [Nat.succ_eq_add_one]
    simp [trim_pointer] at h
    split at h <;> simp_all

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
          untrim_pointer]
        simp only [Pointer.toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_cast,
          Fin.mk.injEq]
        rw [Fin.val_eq_val]
        calc _
          _ = (Vector.map (Trim.trim_node (k := l)) B.heap)[j.1].var := by
            congr 1
            apply aux <;> simp_all
          _ = (Trim.trim_node (k := l + 1) B.heap[j.1]).var := by simp; rfl
    · cases heq : y with
      | terminal => simp [Trim.untrim_pointer]
      | node j =>
        have := trim_reachable_and_edge (h1 := h1) (h2 := h2) hy
        rw [heq] at this
        simp only [Vector.take_eq_extract, Vector.map_extract, Nat.succ_eq_add_one,
          untrim_pointer]
        simp [Pointer.toVar]
        rw [Fin.val_eq_val]
        calc _
          _ = (Vector.map (Trim.trim_node (k := l)) B.heap)[j.1].var := by
            congr 1
            exact aux (B := B) (j := j.1) (l := l) h1 (h2 ⟨j.1, by omega⟩ this.1)
          _ = (Trim.trim_node (k := l + 1) B.heap[j.1]).var := by simp; rfl

def otrim (O : OBdd n m) (h1 : k ≤ m) (h2 : ∀ j : Fin m, Pointer.Reachable O.1.heap O.1.root (.node j) → j < k) :
    OBdd n k := ⟨trim O.1 h1 h2, trim_ordered O.2⟩

private lemma otrim_noRedundancy {O : OBdd n m} {h1 : k ≤ m} {h2} (hr : O.1.NoRedundancy) : (otrim O h1 h2).1.NoRedundancy := by
  rintro ⟨x, hx⟩ contra
  cases contra with
  | red hj =>
    rename_i j
    apply hr ⟨.node ⟨j.1, by omega⟩, (trim_reachable_and_edge hx).1⟩
    constructor
    simp only [otrim, Fin.getElem_fin] at hj
    simp only [Fin.getElem_fin]
    rw [← untrim_point_trim_heap_low (h1 := h1) (h2 := h2) (hj := (trim_reachable_and_edge hx).1)]
    rw [← untrim_point_trim_heap_high (h1 := h1) (h2 := h2) (hj := (trim_reachable_and_edge hx).1)]
    congr

private lemma trim_root {B : Bdd n m} {h1 : l + 1 ≤ m} {h2} : (trim B h1 h2).root = trim_pointer B.root := by
  simp only [trim]

private def trim_root_node {h1 : k + 1 ≤ m} {h2} :
    (trim B h1 h2).root = .node j → { j' // B.root = .node j' } := by
  intro h
  conv at h =>
    lhs
    rw [trim_root]
  simp [trim_pointer] at h
  split at h
  next => contradiction
  next j' hj' => use j'

private def trim_root_node' {h1 : k + 1 ≤ m} {h2} :
    (trim B h1 h2).root = .node j → B.root = .node ⟨j.1, by omega⟩ := by
  intro h
  conv at h =>
    lhs
    rw [trim_root]
  simp [trim_pointer] at h
  split at h
  next => contradiction
  next j' hj' =>
    simp_all
    rw [Fin.eq_mk_iff_val_eq] at h
    simp_all only
    apply Fin.eq_of_val_eq
    simp only
    rw [← h]
    symm
    simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
    apply h2
    left

private lemma otrim_low_aux {O : OBdd n m} {h : O.1.root = .node j} :
    (∀ (j : Fin m), Pointer.Reachable O.1.heap O.1.root (Pointer.node j) → j.1 < k) →
    (∀ (j : Fin m), Pointer.Reachable (O.low h).1.heap (O.low h).1.root (Pointer.node j) → j.1 < k) := by
  intro h j' hj'
  apply h
  rw [OBdd.reachable_from_node_iff']
  right
  left
  exact hj'

private lemma otrim_high_aux {O : OBdd n m} {h : O.1.root = .node j} :
    (∀ (j : Fin m), Pointer.Reachable O.1.heap O.1.root (Pointer.node j) → j.1 < k) →
    (∀ (j : Fin m), Pointer.Reachable (O.high h).1.heap (O.high h).1.root (Pointer.node j) → j.1 < k) := by
  intro h j' hj'
  apply h
  rw [OBdd.reachable_from_node_iff']
  right
  right
  exact hj'

private lemma trim_pointer_untrim_pointer {p : Pointer (l + 1)} (hp : ∀ j, p = .node j → j.1 < l + 1) {h1 : l + 1 ≤ m} :
    Trim.trim_pointer (Trim.untrim_pointer h1 p) = p := by
  cases h : p with
  | terminal _ => simp [untrim_pointer, trim_pointer]
  | node j =>
    simp only [trim_pointer, untrim_pointer, Pointer.node.injEq]
    have := hp j h
    apply Fin.eq_of_val_eq
    simp

private lemma trim_reachable_reverse' {B : Bdd n m} {h1 : l + 1 ≤ m} {h2} :
    Pointer.Reachable B.heap B.root p →
    Pointer.Reachable (trim B h1 h2).heap (trim B h1 h2).root (trim_pointer p) ∧
    (∀ q, Edge B.heap p q → Edge (trim B h1 h2).heap (trim_pointer p) (trim_pointer q)):= by
  intro h
  induction h with
  | refl =>
    constructor
    · conv =>
        congr
        rfl
        rfl
        rw [← untrim_point_trim_root (h1 := h1) (h2 := h2)]
      rw [trim_pointer_untrim_pointer]
      left
      intro j' hj'
      have : B.root = .node ⟨j'.1, by omega⟩ := by
        rw [trim_root] at hj'
        simp [trim_pointer] at hj'
        split at hj' <;> simp_all
        rw [← hj']
        apply Fin.eq_of_val_eq
        simp only
        rename_i j'' hj''
        have := h2 j'' .refl
        exact Eq.symm (Nat.mod_eq_of_lt this)
      have := h2 ⟨j'.1, by omega⟩ (by rw [this]; left)
      exact this
    · intro q e
      cases h : B.root with
      | terminal _ => rw [h] at e; contradiction
      | node j' =>
        rcases B with ⟨heap, root⟩
        cases e with
        | low heq =>
          left
          simp_all only [Pointer.node.injEq, Fin.getElem_fin]
          symm at h
          subst h
          rw [← heq]
          simp only [trim, Nat.succ_eq_add_one, Vector.take_eq_extract, Vector.map_extract, Vector.getElem_cast]
          have : j'.1 < l + 1 := by
            apply h2
            left
          have : j'.1 % (l + 1) = j'.1 := Nat.mod_eq_of_lt this
          simp_rw [this]
          have := Vector.getElem_extract (as := (Vector.map (Trim.trim_node (k := l)) heap)) (n := m) (start := 0) (stop := l + 1) (i := j'.1) (by omega)
          have : ((Vector.map (Trim.trim_node (k := l)) heap).extract 0 (l + 1))[↑j'].low = (Vector.map Trim.trim_node heap)[0 + ↑j'].low := by simp_all
          simp at this
          convert this
        | high heq =>
          right
          simp_all only [Pointer.node.injEq, Fin.getElem_fin]
          symm at h
          subst h
          rw [← heq]
          simp only [trim, Nat.succ_eq_add_one, Vector.take_eq_extract, Vector.map_extract, Vector.getElem_cast]
          have : j'.1 < l + 1 := by
            apply h2
            left
          have : j'.1 % (l + 1) = j'.1 := Nat.mod_eq_of_lt this
          simp_rw [this]
          have := Vector.getElem_extract (as := (Vector.map (Trim.trim_node (k := l)) heap)) (n := m) (start := 0) (stop := l + 1) (i := j'.1) (by omega)
          have : ((Vector.map (Trim.trim_node (k := l)) heap).extract 0 (l + 1))[↑j'].high = (Vector.map Trim.trim_node heap)[0 + ↑j'].high := by simp_all
          simp at this
          convert this
  | tail r e ih =>
    constructor
    · right
      exact ih.1
      exact ih.2 _ e
    · intro q hq
      cases hq with
      | low hq =>
        nth_rw 1 [trim_pointer]
        left
        rename_i j
        have hj : Pointer.Reachable B.heap B.root (Pointer.node j) := .tail r e
        have : j.1 < l + 1 := h2 _ hj
        have := untrim_point_trim_heap_low (j := ⟨j.1, by omega⟩) (h2 := h2) (hj := hj) (h1 := h1)
        simp at this
        simp at hq
        conv at hq =>
          lhs
          rw [← this]
        rw [← hq]
        simp [trim_pointer_untrim_pointer]
        congr
        simpa
      | high _ =>
        nth_rw 1 [trim_pointer]
        right
        rename_i j hq
        have hj : Pointer.Reachable B.heap B.root (Pointer.node j) := .tail r e
        have : j.1 < l + 1 := h2 _ hj
        have := untrim_point_trim_heap_high (j := ⟨j.1, by omega⟩) (h2 := h2) (hj := hj) (h1 := h1)
        simp at this
        simp at hq
        conv at hq =>
          lhs
          rw [← this]
        rw [← hq]
        simp [trim_pointer_untrim_pointer]
        congr
        simpa

private lemma trim_reachable_reverse {B : Bdd n m} {h1 : l + 1 ≤ m} {j : Fin (l + 1)} {h2} :
    Pointer.Reachable B.heap B.root (Pointer.node ⟨j, by omega⟩) →
    Pointer.Reachable (trim B h1 h2).heap (trim B h1 h2).root (Pointer.node j) := by
  intro h
  have := (trim_reachable_reverse' (B := B) (h1 := h1) (h2 := h2) (p := (Pointer.node ⟨j, by omega⟩)) h).1
  convert this
  simp only [trim_pointer, Pointer.node.injEq]
  apply Fin.eq_of_val_eq
  have := h2 ⟨j.1, by omega⟩ h
  exact Eq.symm (Nat.mod_eq_of_lt this)

@[simp]
private lemma trim_low {B : Bdd n m} {h1 : l + 1 ≤ m} {h2} {j : Fin (l + 1)} {hj : Pointer.Reachable B.heap B.root (Pointer.node ⟨j.1, by omega⟩)}:
    (trim B h1 h2).heap[j.1].low = trim_pointer B.heap[j.1].low := by
  conv =>
    rhs
    congr
    rw [← untrim_point_trim_heap_low (h1 := h1) (B := B) (h2 := h2) (hj := hj)]
  rw [trim_pointer_untrim_pointer]
  intro j' hj'
  apply h2 ⟨j', by omega⟩
  have : Pointer.Reachable (trim B h1 h2).heap (trim B h1 h2).root (.node j') := by
    right
    exact trim_reachable_reverse hj
    left
    exact hj'
  have := (trim_reachable_and_edge this).1
  simp only [untrim_pointer] at this
  exact this

@[simp]
private lemma trim_high {B : Bdd n m} {h1 : l + 1 ≤ m} {h2} {j : Fin (l + 1)} {hj : Pointer.Reachable B.heap B.root (Pointer.node ⟨j.1, by omega⟩)}:
    (trim B h1 h2).heap[j.1].high = trim_pointer B.heap[j.1].high := by
  conv =>
    rhs
    congr
    rw [← untrim_point_trim_heap_high (h1 := h1) (B := B) (h2 := h2) (hj := hj)]
  rw [trim_pointer_untrim_pointer]
  intro j' hj'
  apply h2 ⟨j', by omega⟩
  have : Pointer.Reachable (trim B h1 h2).heap (trim B h1 h2).root (.node j') := by
    right
    exact trim_reachable_reverse hj
    right
    exact hj'
  have := (trim_reachable_and_edge this).1
  simp only [untrim_pointer] at this
  exact this

private lemma otrim_low {O : OBdd n m} {h1 : l + 1 ≤ m} {h2} {h : (otrim O h1 h2).1.root = .node j} :
    (otrim O h1 h2).low h = (otrim (O.low (trim_root_node' (h1 := h1) (h2 := h2) (j := j) (by simp_all [otrim]))) h1 (otrim_low_aux h2)) := by
  simp only [OBdd.low, Bdd.low, otrim, Fin.getElem_fin]
  congr
  simp only
  apply trim_low
  simp [otrim] at h
  rw [← untrim_point_trim_root (h1 := h1) (h2 := h2)]
  rw [h]
  left

private lemma otrim_high {O : OBdd n m} {h1 : k + 1 ≤ m} {h2} {h : (otrim O h1 h2).1.root = .node j} :
    (otrim O h1 h2).high h = (otrim (O.high (trim_root_node' (h1 := h1) (h2 := h2) (j := j) (by simp_all [otrim]))) h1 (otrim_high_aux h2)) := by
  simp only [OBdd.high, Bdd.high, otrim, Fin.getElem_fin]
  congr
  simp only
  apply trim_high
  simp [otrim] at h
  rw [← untrim_point_trim_root (h1 := h1) (h2 := h2)]
  rw [h]
  left

private lemma trim_var {B : Bdd n m} {h1 : l + 1 ≤ m} {h2} {j : Fin (l + 1)} {hj : Pointer.Reachable B.heap B.root (Pointer.node ⟨j.1, by omega⟩)} :
    (trim B h1 h2).heap[j.1].var = B.heap[j.1].var := by
  apply trim_induction (motive := fun k T ↦ ∀ (hk : k = l + 1), T.heap[j.1].var = B.heap[j].var)
  · simp
  · intro l' h1' h2' hk
    simp only [Nat.add_right_cancel_iff] at hk
    symm at hk
    subst hk
    simp only [Vector.take_eq_extract, Vector.map_extract, Vector.getElem_cast, Fin.getElem_fin]
    have : j.1 < l + 1 := by
      have := h2' ⟨j.1, by omega⟩ hj
      simp only at this
      exact this
    have := Vector.getElem_extract (as := (Vector.map (Trim.trim_node (k := l)) B.heap)) (n := m) (start := 0) (stop := l + 1) (i := j.1) (by omega)
    simp at this
    rw [this]
    simp [trim_node]
    congr
  · simp

private lemma otrim_toTree' {O : OBdd n m} {h1 : l + 1 ≤ m} {h2} :
    OBdd.toTree (otrim O h1 h2) = OBdd.toTree O := by
  cases heq : (otrim O h1 h2).1.root with
  | terminal b =>
    have : O.1.root = .terminal b := by
      simp only [otrim] at heq
      simp only [trim] at heq
      simp [trim_pointer] at heq
      split at heq
      next => simp_all
      next => simp at heq
    simp only [OBdd.toTree_terminal' heq]
    simp only [OBdd.toTree_terminal' this]
  | node j =>
    rw [OBdd.toTree_node heq]
    conv =>
      lhs
      rw [otrim_low]
      rw [otrim_high]
    rw [OBdd.toTree_node (trim_root_node' heq (h1 := h1) (h2 := h2))]
    congr 1
    · have hj : Pointer.Reachable O.1.heap O.1.root (Pointer.node ⟨j.1, by omega⟩) := by
        simp only [otrim] at heq
        rw [trim_root] at heq
        have := trim_pointer_untrim_pointer (l := l) (h1 := h1) (p := (Pointer.node ⟨j.1, by omega⟩)) ?_
        · rw [← this] at heq
          have := trim_pointer_injective
            (p := O.1.root)
            (q := (Trim.untrim_pointer h1 (Pointer.node ⟨↑j, by omega⟩)))
            (hp := by intro j' hj'; apply h2; rw [hj']; left)
            (hq := fun j' hj' ↦ by
              simp only [untrim_pointer, Pointer.node.injEq] at hj'
              rw [Fin.eq_mk_iff_val_eq] at hj'
              simp_all
              omega
            )
            (l := l) heq
          rw [this]
          left
        · intro j' hj'
          omega
      exact trim_var (hj := hj) (h2 := h2) (h1 := h1)
    · exact otrim_toTree'
    · exact otrim_toTree'
termination_by O

private lemma otrim_toTree {h1 : l + 1 ≤ m} (hx : Pointer.Reachable (otrim O h1 h2).1.heap (otrim O h1 h2).1.root x) :
    OBdd.toTree ⟨⟨(otrim O h1 h2).1.heap, x⟩, Bdd.ordered_of_reachable hx⟩ =
    OBdd.toTree ⟨⟨O.1.heap, Trim.untrim_pointer h1 x⟩, Bdd.ordered_of_reachable (trim_reachable_and_edge hx).1⟩ := by
  induction hx with
  | refl =>
    have : OBdd.toTree ⟨{ heap := (otrim O h1 h2).1.heap, root := (otrim O h1 h2).1.root }, trim_ordered O.2 (h1 := h1) (h2 := h2)⟩ = (otrim O h1 h2).toTree := rfl
    rw [this]
    rw [otrim_toTree']
    simp only [otrim]
    simp_rw [untrim_point_trim_root]
    rfl
  | tail r e ih =>
    rename_i b c
    cases b with
    | terminal b => contradiction
    | node j =>
      simp [untrim_pointer] at ih
      rw [OBdd.toTree_node rfl] at ih
      conv at ih =>
        rhs
        rw [OBdd.toTree_node rfl]
      injection ih with hv hl hh
      cases e with
      | low heq =>
        convert hl
        · simp only [OBdd.low, Bdd.low, Fin.getElem_fin]
          simp only [Fin.getElem_fin] at heq
          simp_rw [heq]
        · simp only [OBdd.low, Bdd.low, Fin.getElem_fin]
          simp only [Fin.getElem_fin] at heq
          simp_rw [← heq]
          simp only [otrim]
          congr
          rw [untrim_point_trim_heap_low]
          exact (trim_reachable_and_edge r (h2 := h2) (h1 := h1)).1
      | high heq =>
        convert hh
        · simp only [OBdd.high, Bdd.high, Fin.getElem_fin]
          simp only [Fin.getElem_fin] at heq
          simp_rw [heq]
        · simp only [OBdd.high, Bdd.high, Fin.getElem_fin]
          simp only [Fin.getElem_fin] at heq
          simp_rw [← heq]
          simp only [otrim]
          congr
          rw [untrim_point_trim_heap_high]
          exact (trim_reachable_and_edge r (h2 := h2) (h1 := h1)).1

private lemma otrim_similarRp {h1 : l + 1 ≤ m}:
    (otrim O h1 h2).SimilarRP ⟨x, hx⟩ ⟨y, hy⟩ →
    O.SimilarRP ⟨Trim.untrim_pointer h1 x, (trim_reachable_and_edge hx).1⟩ ⟨Trim.untrim_pointer h1 y, (trim_reachable_and_edge hy).1⟩ := by
  simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar]
  intro h
  rw [otrim_toTree hx] at h
  rw [otrim_toTree hy] at h
  exact h

private lemma otrim_reduced_helper {O : OBdd n m} {h1 : l + 1 ≤ m} {h2} (hr : Subrelation (OBdd.SimilarRP O) (InvImage Eq Subtype.val)) :
    Subrelation (OBdd.SimilarRP (otrim O h1 h2)) (InvImage Eq Subtype.val) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only [InvImage]
  have : untrim_pointer h1 x = untrim_pointer h1 y := by
    refine @hr
      ⟨(untrim_pointer h1 x), (trim_reachable_and_edge (h2 := h2) hx).1⟩
      ⟨(untrim_pointer h1 y), (trim_reachable_and_edge (h2 := h2) hy).1⟩
      ?_
    apply (otrim_similarRp (h1 := h1) (h2 := h2) hxy) <;> simp_all
  exact untrim_pointer_injective this

lemma otrim_reduced {O : OBdd n m} {h1 : k ≤ m} {h2} (hr : OBdd.Reduced O) :
    OBdd.Reduced (otrim O h1 h2) :=
  match k with
  | .zero => OBdd.reduced_of_terminal (Bdd.terminal_of_zero_heap (B := (otrim O h1 h2).1) (m := 0) rfl)
  | .succ _ => ⟨otrim_noRedundancy hr.1, otrim_reduced_helper hr.2⟩

lemma otrim_evaluate {O : OBdd n m} {h1 : k ≤ m} {h2} :
    OBdd.evaluate (otrim O h1 h2) = O.evaluate := by
  cases k with
  | zero =>
    have := (Bdd.terminal_of_zero_heap (B := (otrim O h1 h2).1) (m := 0) rfl)
    rcases this with ⟨b, hb⟩
    rw [OBdd.evaluate_terminal' hb]
    simp only [otrim] at hb
    have := trim_root_terminal hb
    rw [OBdd.evaluate_terminal' this]
  | succ _ => simp only [OBdd.evaluate, Function.comp_apply, otrim_toTree']

end Trim
