import Bdd.Basic

namespace Choice

open Pointer
open OBdd

private def choice_helper (O : OBdd n m) : O.1.root = .node j → Vector Bool n → Vector Bool n := fun hj I ↦
  match hl : O.1.heap[j].low with
  | .node j => choice_helper (O.low hj) hl I
  | .terminal true => I.set O.1.heap[j].var false
  | .terminal false =>
    match hh : O.1.heap[j].high with
    | .terminal _ => I.set O.1.heap[j].var true
    | .node j' => (choice_helper (O.high hj) hh I).set O.1.heap[j].var true
termination_by O

def choice (O : OBdd n m) : (∃ I, O.evaluate I) → Vector Bool n := fun ht ↦
  match O_root_def : O.1.root with
  | .terminal true => Vector.replicate n false
  | .terminal false => by
    absurd ht
    rw [OBdd.evaluate_terminal' O_root_def]
    simp only [Function.const_apply, Bool.false_eq_true, exists_const, not_false_eq_true]
  | .node j => choice_helper O O_root_def (Vector.replicate n false)

private lemma Vector.get_set_ne {xs : Vector α n} {x : α} (hi : i < n) {j : Fin n} (h : i ≠ j) :
    (xs.set i x hi).get j = xs.get j := by
  simp only [Vector.get]
  aesop

private def choice_helper_spec' {O : OBdd n m} (hr : O.Reduced) (hj : O.1.root = .node j) (i : Fin n) :
    i < O.1.heap[j].var → (choice_helper O hj (Vector.replicate n false)).get i = false := by
  intro hi
  unfold choice_helper
  split
  next jl hl =>
    have := var_lt_low_var (h := hj)
    simp only [var, Nat.succ_eq_add_one, Bdd.var, hj, low, Bdd.low, hl, toVar] at this
    apply choice_helper_spec' (low_reduced hr)
    simp_all
    omega
  next hl => simp [Vector.get]
  next hl =>
    split
    next bh hh =>
      simp [Vector.get]
      rw [Array.getElem_set_ne]
      · simp
      · simp
      · apply ne_of_gt
        exact hi
    next jh hh =>
      have := var_lt_high_var (h := hj)
      simp only [var, Nat.succ_eq_add_one, Bdd.var, hj, high, Bdd.high, hh, toVar] at this
      rw [Vector.get_set_ne]
      apply choice_helper_spec' (high_reduced hr)
      · simp_all
        omega
      · omega
termination_by O

private def choice_helper_spec'' {O : OBdd n m} (hr : O.Reduced) (hj : O.1.root = node j) (i : Fin n) :
    i < O.1.heap[j].var → (choice_helper O hj (Vector.replicate n false))[i] = false := by
  have := choice_helper_spec' hr hj i
  exact this

private def choice_helper_spec {O : OBdd n m} (hr : O.Reduced) (hj : O.1.root = node j) :
    O.evaluate (choice_helper O hj (Vector.replicate n false)) := by
  unfold choice_helper
  split
  next jl hl =>
    rw [evaluate_node'' hj]
    simp only
    suffices s : (choice_helper (O.low hj) hl (Vector.replicate n false))[O.1.heap[j].var] = false by
      rw [s]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply choice_helper_spec (low_reduced hr)
    rw [choice_helper_spec'' (low_reduced hr) hl]
    have := var_lt_low_var (h := hj)
    simp only [var, Nat.succ_eq_add_one, Bdd.var, toVar, hj, hl, low, Bdd.low] at this
    simp_all
  next hl =>
    rw [evaluate_node'' hj]
    have : (O.low hj).1.root = terminal true := by simp only [low, Bdd.low, hl]
    simp [evaluate_terminal' this]
  next hl =>
    split
    next bh hh =>
      rw [evaluate_node'' hj]
      have : (O.high hj).1.root = terminal true := by
        simp only [high, Bdd.high]
        rw [hh]
        congr
        cases bh with
        | false => exact False.elim (hr.1 ⟨node j, by simp_all; left⟩ ⟨by simp_all⟩)
        | true => rfl
      simp [evaluate_terminal' this]
    next jh hh =>
      rw [evaluate_node'' hj]
      simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
      have : (O.high hj).evaluate ((choice_helper (O.high hj) hh (Vector.replicate n false)).set O.1.heap[j.1].var.1 true) =
             (O.high hj).evaluate (choice_helper (O.high hj) hh ((Vector.replicate n false))) := by
        rw [OBdd.independentOf_lt_root (O.high hj) ⟨O.1.heap[j.1].var.1, ?_⟩ true (choice_helper (O.high hj) hh (Vector.replicate n false))]
        rw [show O.1.heap[j.1].var.1 = O.var by simp [hj]]
        exact var_lt_high_var
      rw [this]
      apply choice_helper_spec (high_reduced hr)
termination_by O

@[simp]
def choice_evaluate {O : OBdd n m} (hr : O.Reduced) (ht : ∃ I, O.evaluate I) : O.evaluate (choice O ht) = true := by
  simp only [choice]
  split
  next O_root_def => rw [evaluate_terminal' O_root_def]; simp
  next O_root_def =>
    absurd ht
    rw [evaluate_terminal' O_root_def]
    simp only [Function.const_apply, Bool.false_eq_true, exists_const, not_false_eq_true]
  next j O_root_def => exact choice_helper_spec hr O_root_def

end Choice
