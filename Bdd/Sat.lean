import Std.Sat.CNF.Basic
import Bdd.BDD

namespace Sat

def BDD_of_literal (l : Std.Sat.Literal (Fin n)) : BDD := if l.2 then (BDD.var l.1) else (BDD.var l.1).not

def BDD_of_clause (c : Std.Sat.CNF.Clause (Fin n)) : BDD := (c.map BDD_of_literal).foldr BDD.or (BDD.const false)

def BDD_of_CNF (C : Std.Sat.CNF (Fin n)) : BDD := (C.map BDD_of_clause).foldr BDD.and (BDD.const true)

@[simp]
lemma BDD_of_literal_nvars : (BDD_of_literal (n := n) C).nvars ≤ n := by
  simp only [BDD_of_literal]
  split <;> (simp; omega)

@[simp]
lemma BDD_of_clause_nvars : (BDD_of_clause (n := n) C).nvars ≤ n := by
  induction C <;> simp_all [BDD_of_clause]

@[simp]
lemma BDD_of_CNF_nvars : (BDD_of_CNF (n := n) C).nvars ≤ n := by
  induction C <;> simp_all [BDD_of_CNF]

lemma BDD_of_CNF_correct {n} {f : Fin n → Bool} (C : Std.Sat.CNF (Fin n)) :
    Std.Sat.CNF.eval f C = (BDD_of_CNF C).denotation (n := n) (by simp) (Vector.ofFn f) := by
  induction C with
  | nil => simp [BDD_of_CNF]
  | cons head tail ih =>
    simp only [Std.Sat.CNF.eval_cons, BDD_of_CNF, List.map_cons, List.foldr_cons, BDD.and_denotation]
    simp only [Std.Sat.CNF.eval_cons, BDD_of_CNF, List.map_cons, List.foldr_cons] at ih
    rw [ih]
    congr 1
    induction head with
    | nil => simp [BDD_of_clause]
    | cons head tail ih =>
      simp only [Std.Sat.CNF.Clause.eval_cons, Fin.eta]
      rw [ih]
      simp only [BDD_of_clause, Fin.eta, List.map_cons, List.foldr_cons, BDD.or_denotation]
      congr 1
      simp only [BDD_of_literal]
      split <;> simp_all

instance instDecidableUnsat (C : Std.Sat.CNF (Fin n)) : Decidable (Std.Sat.CNF.Unsat C) :=
  decidable_of_iff ((BDD_of_CNF C).SemanticEquiv (BDD.const false)) ⟨l_to_r, r_to_l⟩ where
    l_to_r h := by
      simp only [BDD.SemanticEquiv] at h
      contrapose h
      rw [funext_iff]
      simp only [Std.Sat.CNF.Unsat, not_forall, Bool.not_eq_false] at h
      rcases h with ⟨f, hf⟩
      rw [BDD_of_CNF_correct] at hf
      simp only [Fin.eta, BDD.const_nvars, BDD.const_denotation, Function.const_apply, not_forall, Bool.not_eq_false]
      use Vector.cast (by simp) (Vector.ofFn fun i : Fin (BDD_of_CNF C).nvars ↦ f ⟨i.1, lt_of_lt_of_le i.2 BDD_of_CNF_nvars⟩)
      simp only [le_refl, BDD.denotation_cast]
      rw [BDD.denotation_take'] at hf
      rw [← hf]
      congr
      ext i hi
      have := Vector.getElem_extract (as := (Vector.ofFn f)) (show i < (min (BDD_of_CNF C).nvars n) - 0 by simpa)
      simp_all
    r_to_l h := by
      simp only [Std.Sat.CNF.Unsat] at h
      simp only [BDD.SemanticEquiv]
      ext I
      simp only [BDD.const_nvars, BDD.const_denotation, Function.const_apply]
      have := h (fun i ↦ if hi : i < (max (BDD_of_CNF C).nvars (BDD.const false).nvars) then I[i] else false)
      simp only [BDD.const_nvars, zero_le, sup_of_le_left, Fin.getElem_fin] at this
      rw [BDD_of_CNF_correct] at this
      rw [BDD.denotation_take (m := max (BDD_of_CNF C).nvars (BDD.const false).nvars)] at this
      rw [← this]
      simp only [BDD.const_nvars]
      conv => lhs; rw [BDD.denotation_take' (hn := by simp)]
      conv => rhs; rw [BDD.denotation_take' (hn := by simp)]
      congr 1
      swap; simp
      swap; simp
      simp only [Vector.take_eq_extract, Vector.extract_extract, Nat.add_zero, Nat.sub_zero,
        Vector.cast_cast, Vector.cast_eq_cast]
      ext i hi
      simp only [Nat.sub_zero, Vector.getElem_cast]
      have := Vector.getElem_extract (as := I) (show i < (min (BDD_of_CNF C).nvars (max (BDD_of_CNF C).nvars (BDD.const false).nvars)) - 0 by simp; omega)
      simp_all only [BDD.const_nvars, Vector.take_eq_extract, Nat.sub_zero, zero_add]
      have := Vector.getElem_extract (as := (Vector.ofFn fun i : Fin n ↦ if h : i.1 < (BDD_of_CNF C).nvars then I[i.1] else false)) (show i < min ((min (0 + (BDD_of_CNF C).nvars) (max (BDD_of_CNF C).nvars 0))) n - 0 by simp_all; omega)
      simp_all only [Nat.sub_zero, BDD.const_nvars, zero_add, Vector.getElem_ofFn]
      split
      next => rfl
      next c => absurd c; omega

-- #eval Std.Sat.CNF.eval (fun _ : Nat ↦ true) []
-- #eval Std.Sat.CNF.eval (fun _ : Nat ↦ true) []
--#eval! instDecidableUnsat (n := 3) [[⟨1, true⟩], [⟨2, false⟩]]
-- #eval! (BDD_of_CNF (n := 3) [[⟨1, true⟩, ⟨2, false⟩]]).size

end Sat
