import Bdd.Basic

namespace Trim

private def trim_pointer [NeZero k] : Pointer m → Pointer k
  | .terminal b => .terminal b
  | .node j => .node ⟨j.1 % k, Nat.mod_lt j.1 (by rename_i h; rcases h; omega)⟩

private def trim_node [NeZero k] : Node n m → Node n k
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

lemma trim_ordered {B : Bdd n m} (o : B.Ordered) {h1 : k ≤ m} {h2} : (trim B h1 h2).Ordered := by
  simp only [trim]
  split
  next _ _ _ h2 =>
    split
    next => exact Bdd.Ordered_of_terminal
    next j hj => rw [hj] at h2; have := h2 j .refl; contradiction
  next _ _ _ l h1 h2 => sorry

def otrim (O : OBdd n m) (h1 : k ≤ m) (h2 : ∀ j : Fin m, Pointer.Reachable O.1.heap O.1.root (.node j) → j < k) :
    OBdd n k := ⟨trim O.1 h1 h2, trim_ordered O.2⟩

lemma otrim_reduced {O : OBdd n m} {h1 : k ≤ m} {h2} :
    OBdd.Reduced O → OBdd.Reduced (otrim O h1 h2) := by
  sorry

lemma otrim_evaluate {O : OBdd n m} {h1 : k ≤ m} {h2} :
    OBdd.evaluate (otrim O h1 h2) = O.evaluate := by
  sorry

end Trim
