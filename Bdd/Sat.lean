import Std.Sat.CNF.Basic
import Bdd.BDD

namespace Sat

def BDD_of_literal : Std.Sat.Literal (Fin n) → BDD
  | ⟨i, true⟩  =>  (BDD.var i).lift (n := n) (by simp; omega)
  | ⟨i, false⟩ => ((BDD.var i).lift (n := n) (by simp; omega)).not

def BDD_of_clause (C : Std.Sat.CNF.Clause (Fin n)) : BDD := (C.map BDD_of_literal).foldr BDD.or ((BDD.const false).lift (n := n) (by simp))

def BDD_of_CNF (C : Std.Sat.CNF (Fin n)) : BDD := (C.map BDD_of_clause).foldr BDD.and ((BDD.const true).lift (n := n) (by simp))

@[simp]
lemma BDD_of_literal_nvars : (BDD_of_literal (n := n) C).nvars = n := by
  simp only [BDD_of_literal]
  split <;> simp

@[simp]
lemma BDD_of_clause_nvars : (BDD_of_clause (n := n) C).nvars = n := by
  induction C with
  | nil => simp [BDD_of_clause]
  | cons head tail ih => simp_all [BDD_of_clause]

@[simp]
lemma BDD_of_CNF_nvars : (BDD_of_CNF (n := n) C).nvars = n := by
  induction C with
  | nil => simp [BDD_of_CNF]
  | cons head tail ih => simp_all [BDD_of_CNF]

lemma BDD_of_CNF_correct {n} {f : Fin n → Bool} (C : Std.Sat.CNF (Fin n)) :
    Std.Sat.CNF.eval f C = (BDD_of_CNF C).denotation (n := n) (by simp) (Vector.ofFn f) := by
  induction C with
  | nil => simp [BDD_of_CNF]
  | cons head tail ih =>
    simp only [Std.Sat.CNF.eval_cons, BDD.denotation', BDD_of_CNF, List.map_cons, List.foldr_cons, BDD.and_denotation]
    simp only [Std.Sat.CNF.eval_cons, BDD.denotation', BDD_of_CNF, List.map_cons, List.foldr_cons] at ih
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
      split <;> simp

private lemma aux {v : Vector Bool m} (h : m = n) : HEq v (Vector.ofFn fun x : Fin n ↦ v[x.1]) := by
  subst h
  simp_all only [heq_eq_eq]
  ext i x : 1
  simp_all only [Vector.getElem_ofFn]

instance instDecidableUnsat (C : Std.Sat.CNF (Fin n)) : Decidable (Std.Sat.CNF.Unsat C) :=
  decidable_of_iff
    ((BDD_of_CNF C).SemanticEquiv (BDD.const false))
    (by
      constructor
      · intro h
        simp only [BDD.SemanticEquiv] at h
        rw [funext_iff] at h
        contrapose h
        simp only [Std.Sat.CNF.Unsat, not_forall, Bool.not_eq_false] at h
        rcases h with ⟨f, hf⟩
        rw [BDD_of_CNF_correct] at hf
        simp_all only [Fin.eta, BDD.const_nvars, BDD.const_denotation, Function.const_apply,
          not_forall, Bool.not_eq_false]
        use Vector.cast (by simp) (Vector.ofFn fun i ↦ f i)
        simp only [BDD_of_CNF_nvars, le_refl, BDD.denotation_cast]
        exact hf
      · intro h
        simp only [Std.Sat.CNF.Unsat] at h
        simp only [BDD.SemanticEquiv]
        ext I
        simp only [BDD.const_nvars, BDD.const_denotation, Function.const_apply]
        have := h (fun i ↦ if i < (max (BDD_of_CNF C).nvars (BDD.const false).nvars) then I[i] else false)
        simp at this
        rw [BDD_of_CNF_correct] at this
        convert this using 1
        congr 1
        · simp
        · simp
        · exact aux (by simp)
    )

-- #eval Std.Sat.CNF.eval (fun _ : Nat ↦ true) []
-- #eval Std.Sat.CNF.eval (fun _ : Nat ↦ true) []
-- #eval! instDecidableUnsat (n := 3) [[⟨1, true⟩], [⟨1, false⟩]]
-- #eval! (BDD_of_CNF (n := 3) [[⟨1, true⟩, ⟨2, false⟩]]).size

end Sat
