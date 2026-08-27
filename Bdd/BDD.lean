module

public import Bdd.Count
-- Only for Fintype instance for Vector
public import Bdd.Evaluate
public import Bdd.Sim
public import Bdd.Tactic

import Bdd.Apply
import Bdd.Choice
import Bdd.Nary
import Bdd.Reduce
import Bdd.Relabel
import Bdd.Restrict

/-
Cannot compile inline/specializing declaration `instDecidableSemanticEquiv` as it uses `Lift.olift`
of module `Bdd.Lift` which must be imported publicly. This limitation may be lifted in the future.
-/
public import Bdd.Lift
import Bdd.Size
import Bdd.Count

/-- Abstract BDD type. -/
public structure BDD where
  /-- BDD input size (number of variables). -/
  nvars         : Nat
  private nheap : Nat
  private obdd  : OBdd nvars nheap
  private hred  : obdd.Reduced

namespace BDD

/--
Raise the input size (`nvars`) of a `BDD` to `n`,
given a proof that the current input size is at most `n`.
-/
public def lift (B : BDD) {n} (h : B.nvars ≤ n) : BDD :=
  ⟨n, _, Lift.olift h B.obdd, Lift.olift_reduced B.hred⟩

/-- Lifting a `BDD` to `n` yields a `BDD` with input size (`nvars`) of `n`. -/
@[simp, bdd_nvars]
public lemma lift_nvars {B : BDD} {n} {h : B.nvars ≤ n} : (B.lift h).nvars = n := (rfl)

/-- Lifting a `BDD` `B` to its current input size (`nvars`) yields back `B`. -/
@[simp]
public lemma lift_refl {B : BDD} : (B.lift (Nat.le_refl _)) = B := by simp [lift]

/--
Evaluate the given BDD on the given variable assignment, assuming that the assignment interprets
all variables of the BDD.

The `get_elem_tactic_extensible` has been extended to simplify all hypothesis using the lemmas
marked with `bdd_nvars`, and hence the validity of the bounds can usually be inferred automatically.
-/
@[no_expose]
public instance {n} : GetElem BDD (Vector Bool n) Bool (fun B _ ↦ B.nvars ≤ n) where
  getElem B v h := Evaluate.evaluate (B.lift h).obdd v

lemma getElem_eq_evaluate {n} (B : BDD) (I : Vector Bool n) (h : B.nvars ≤ n) :
    B[I] = Evaluate.evaluate (B.lift h).obdd I := rfl

/--
A BDD `B` depends on a variable `i` if there are two variable assignemts `I` and `I'` such that
`I` and `I'` only differ on the variable `i` and `B[I] ≠ B[I']`.
-/
public def DependsOn (B : BDD) (i : ℕ) : Prop :=
  ∃ h : i < B.nvars, Nary.DependsOn (Evaluate.evaluate B.obdd) ⟨i, h⟩

lemma dependsOn_iff_evaluate {B : BDD} {i} (h : i < B.nvars) :
    B.DependsOn i ↔ Nary.DependsOn (Evaluate.evaluate B.obdd) ⟨i, h⟩ := by
  grind only [DependsOn]

/-- A `BDD` does not depend on variables greater or equal to its input size. -/
@[simp]
public lemma not_dependsOn_of_ge {B : BDD} {i} (h : i ≥ B.nvars) : ¬ B.DependsOn i := by
  grind only [DependsOn]

@[simp]
public lemma getElem_cast {B : BDD} {n m} {I : Vector Bool n} {hn : B.nvars ≤ n} (h : n = m) :
    B[Vector.cast h I] = B[I] := by
  subst h
  simp

/--
Two `BDD`s are semantically equivalent when they have the same evaluation on all variable assignemts.
-/
@[expose]
public def SemanticEquiv (B C : BDD) := ∀ I : Vector Bool (max B.nvars C.nvars), B[I] = C[I]

def Similar (B : BDD) (B' : BDD) :=
  (Lift.olift (Nat.le_max_left ..) B.obdd).Similar (Lift.olift (Nat.le_max_right ..) B'.obdd)

public lemma getElem_take {B : BDD} {n} {I : Vector Bool n} {m} {h1 : B.nvars ≤ m} {h2 : m ≤ n} :
    B[I.take m] = B[I] := by
  simp only [getElem_eq_evaluate, lift, Evaluate.evaluate_evaluate, Lift.olift_evaluate]
  simp only [Vector.take_eq_extract, Vector.extract_extract, Nat.add_zero, Nat.sub_zero,
    Vector.cast_cast]
  congr!
  omega

public lemma getElem_take' {B : BDD} {n} {I : Vector Bool n} {hn : B.nvars ≤ n} :
     B[I.take B.nvars] = B[I] :=
  getElem_take (h1 := le_rfl) (h2 := hn)

lemma Vector.append_take {α n m} (v : Vector α n) (u : Vector α m) :
    (v ++ u).take n = (Vector.cast (by simp) v) := by
  ext i hi
  simp only [Vector.getElem_cast, Vector.getElem_take hi]
  exact Vector.getElem_append_left (by omega)

lemma getElem_append {B : BDD} {n} {hn : B.nvars ≤ n} {m k} (h : n + m = k)
    (I : Vector Bool n) (J : Vector Bool m) : B[I] = B[Vector.cast h (I ++ J)] := by
  rw [getElem_cast]
  · conv =>
      rhs
      rw [← getElem_take (m := n) (h1 := hn) (h2 := by simp)]
    rw [Vector.append_take, getElem_cast]
  · omega

public lemma congrBDD {B C : BDD} {n m}
    (hn : B.nvars ≤ n) (h : C.nvars ≤ n) (hm : max B.nvars C.nvars ≤ m)
    (h : ∀ I : Vector Bool n, B[I] = C[I]) : (∀ I : Vector Bool m, B[I] = C[I]) :=
  if h1 : n ≤ m
  then by
    intro I
    have h2 : min n m = n := by omega
    suffices h3 : B[(I.take n).cast h2] = C[(I.take n).cast h2] by
      grind only [getElem_cast, getElem_take]
    apply h
  else by
    intro Id.ext_iff
    have h2 : m + (n - m) = n := by omega
    rw [getElem_append h2 _ (Vector.replicate (n - m) false)]
    rw [getElem_append h2 _ (Vector.replicate (n - m) false)]
    apply h

public lemma congrInterpretation {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    (∀ i : Fin B.nvars, B.DependsOn i → I[i] = J[i]) → B[I] = B[J] := by
  intro h1
  have h2 : min B.nvars n = B.nvars := by omega
  have h3 : min B.nvars m = B.nvars := by omega
  suffices B[(I.take B.nvars).cast h2] = B[(J.take B.nvars).cast h3] by
    grind only [getElem_cast, !getElem_take]
  apply Nary.eq_of_forall_dependency_getElem_eq
  rintro ⟨j, h4⟩
  calc
  (I.take B.nvars)[↑j]
  _ = I[j] := by
    grind only [= Fin.getElem_fin, = Vector.getElem_take]
  _ = J[j] := by
    simp only [lift, Lift.olift_trivial_eq] at h4
    simp only [Fin.is_lt, dependsOn_iff_evaluate] at h1
    exact h1 j h4
  _ = (J.take B.nvars)[↑j] := by
    grind only [= Fin.getElem_fin, = Vector.getElem_take]

public lemma congrInterpretation' {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    (∀ i : Fin B.nvars, I[i] = J[i]) → B[I] = B[J] := by
  grind only [congrInterpretation]

lemma dependsOn_iff' {B : BDD} {i} (h : i < B.nvars) :
    B.DependsOn i ↔ Nary.DependsOn (fun I : Vector Bool B.nvars ↦ B[I]) ⟨i, h⟩ := by
  simp_all only [dependsOn_iff_evaluate, getElem_eq_evaluate, lift, Lift.olift_trivial_eq]

public lemma dependsOn_iff {B : BDD} {i : ℕ} n (h : B.nvars ≤ n) : B.DependsOn i ↔
    ∃ v1 v2 : Vector Bool n, (∀ i' : Fin n, i ≠ i' → v1[i'] = v2[i']) ∧ B[v1] ≠ B[v2] := by
  if hi : i < B.nvars then
    contrapose
    simp only [ne_eq, Fin.getElem_fin, not_exists, not_and, Decidable.not_not]
    constructor
    · intro h1 v1 v2 h2
      apply congrInterpretation
      intro i' hi'
      specialize h2 (i'.castLE h)
      grind only [= Fin.val_castLE, = Fin.getElem_fin]
    · intro h1
      simp only [dependsOn_iff' hi, Nary.dependsOn_iff, ne_eq, Fin.getElem_fin, not_exists, not_and,
        Decidable.not_not]
      intro v1 v2 h2
      have h3 : B.nvars + (n - B.nvars) = n := by omega
      rw [getElem_append h3 _ (Vector.replicate (n - B.nvars) false)]
      rw [getElem_append h3 _ (Vector.replicate (n - B.nvars) false)]
      apply h1
      intro i' hi'
      simp [Vector.getElem_append]
      split
      · exact h2 ⟨i', by omega⟩ (by grind only)
      · rfl
  else
    simp_all [not_dependsOn_of_ge]
    intro v1 v2 h1
    apply congrInterpretation'
    intro i'
    specialize h1 (i'.castLE h)
    grind only [= Fin.val_castLE, = Lean.Grind.toInt_fin, = Fin.getElem_fin]

public lemma dependsOn_getElem_ne_of_ne {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    B[I] ≠ B[J] → ∃ i : Fin B.nvars, B.DependsOn i ∧ I[i] ≠ J[i] := by
  contrapose
  simp only [Fin.getElem_fin, ne_eq, not_exists, not_and, Decidable.not_not]
  exact congrInterpretation

@[simp, bdd_nvars]
public lemma getElem_lift {B : BDD} {n} {h1 : B.nvars ≤ n} {m} {I : Vector Bool m} {h2} :
    (B.lift h1)[I]'h2 = B[I] := by
  simp [getElem_eq_evaluate, lift, Evaluate.evaluate_evaluate]

public lemma lift_dependsOn {B : BDD} {n} {h1 : B.nvars ≤ n} {i} :
    (B.lift h1).DependsOn i ↔ B.DependsOn i := by
  repeat rw [dependsOn_iff n (by simp [h1])]
  simp only [ne_eq, Fin.getElem_fin, getElem_lift]

/-- `SemanticEquiv` is an equivalence relation on `BDD`. -/
public theorem SemanticEquiv.equivalence : Equivalence SemanticEquiv :=
  { refl B I := rfl,
    symm h I := by
      specialize h (I.cast (max_comm _ _))
      simp at h
      exact h.symm
    trans := by
      intro B C D hBC hCD I
      simp_all only [SemanticEquiv]
      let m := max (max B.nvars C.nvars) D.nvars
      apply congrBDD (n := m) (by omega) (by omega) (by omega)
      intro I
      trans C[I]
      · exact congrBDD _ _ (by omega) hBC I
      · exact congrBDD _ _ (by omega) hCD I
  }

instance instDecidableSimilar : DecidableRel Similar
  | B, C =>
    Sim.decidableRobddHSimilar
      (Lift.olift (Nat.le_max_left  ..) B.obdd) (Lift.olift_reduced B.hred)
      (Lift.olift (Nat.le_max_right ..) C.obdd) (Lift.olift_reduced C.hred)

theorem SemanticEquiv_iff_Similar {B C : BDD} :
    B.SemanticEquiv C ↔ B.Similar C := ⟨l_to_r, r_to_l⟩ where
  l_to_r h := by
    simp [getElem_eq_evaluate, Evaluate.evaluate_evaluate, SemanticEquiv] at h
    apply OBdd.Canonicity (Lift.olift_reduced B.hred) (Lift.olift_reduced C.hred)
    ext I
    exact h I
  r_to_l h := by
    simp only [SemanticEquiv, getElem_eq_evaluate, Evaluate.evaluate_evaluate]
    simp only [Similar] at h
    intro I
    erw [OBdd.Canonicity_reverse h]
    rfl

/-- `SemanticEquiv` is `Decidable`.

Use this instance to decide whether two `BDD`s are equivalent. -/
@[no_expose]
public instance instDecidableSemanticEquiv : DecidableRel SemanticEquiv
  | _, _ => decidable_of_iff' _ SemanticEquiv_iff_Similar

/-- Return the number of reachable nodes in given BDD. -/
public def size : BDD → Nat
  | B => Size.size B.obdd

def zero_vars_to_bool (B : BDD) : B.nvars = 0 → Bool := fun h ↦
  match B.obdd.1.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ (Eq.subst h B.obdd.1.heap[j].var.2))

lemma zero_vars_to_bool_spec {B : BDD} (h : B.nvars = 0) :
    B.obdd.1.root = .terminal (B.zero_vars_to_bool h) := by
  simp only [zero_vars_to_bool]
  split
  next => assumption
  next => contradiction

/-- Return the constant `BDD` for the boolean value `b`. -/
public def const (b : Bool) : BDD :=
  { nvars := 0,
    nheap := 0,
    obdd  := ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.ordered_of_terminal rfl⟩,
    hred  := Bdd.reduced_of_terminal
  }

@[simp, bdd_nvars]
public lemma const_nvars {b} : (const b).nvars = 0 := (rfl)

@[simp]
public lemma getElem_const {n b} : ∀ I : Vector Bool n, (const b)[I] = b := by
  simp [getElem_eq_evaluate, const, Evaluate.evaluate_terminal _, lift]

@[simp]
public lemma const_dependsOn {b} : ∀ i, ¬(const b).DependsOn i := by
  simp only [const_nvars, ge_iff_le, Nat.zero_le, not_dependsOn_of_ge, not_false_eq_true,
    implies_true]

abbrev var_raw (n : Nat) : Bdd (n+1) 1 :=
  ⟨Vector.singleton ⟨⟨n, Nat.lt_add_one n⟩, .terminal false, .terminal true⟩, .node 0⟩

lemma var_ordered : Bdd.Ordered (var_raw n) := by
  apply Bdd.ordered_of_low_high_ordered rfl
  · simp only [Bdd.low_eq]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    exact Bdd.ordered_of_terminal rfl
  · simp [Bdd.low_eq, Bdd.var_eq]
    apply Fin.lt_def.mpr
    refine Nat.lt_succ_of_le ?_
    simp
  · simp only [Bdd.high_eq]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    exact Bdd.ordered_of_terminal rfl
  · simp [Bdd.high_eq, Bdd.var_eq]
    apply Fin.lt_def.mpr
    refine Nat.lt_succ_of_le ?_
    simp

lemma var_reduced : OBdd.Reduced ⟨(var_raw n), var_ordered⟩ := by
  constructor
  · rintro ⟨p, hp⟩
    simp only [Fin.isValue] at hp
    rintro ⟨contra⟩
    simp_all
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [InvImage]
    simp only [OBdd.similarRP_iff] at hxy
    cases Pointer.Reachable_iff.mp hx with
    | inl hh =>
      simp at hh
      cases Pointer.Reachable_iff.mp hy with
      | inl hhh =>
        simp only at hhh
        simp_rw [← hh, hhh]
      | inr hhh =>
        rcases hhh with ⟨j, hj, hhh⟩
        simp only at hj
        injection hj with hj
        simp only at hhh
        rw [← hj] at hhh
        simp at hhh
        rcases hhh with rfl | rfl <;>
        simp only [Vector.singleton_def, OBdd.subBdd_eq, Pointer.terminal.injEq,
          OBdd.toTree_terminal, OBdd.toTree_eq_leaf_iff_terminal] at hxy <;>
        exact hxy
    | inr hh =>
      simp only at hh
      rcases hh with ⟨j, hj, hh⟩
      injection hj with hj
      rw [← hj] at hh
      simp at hh
      cases Pointer.Reachable_iff.mp hy with
      | inl hhh =>
        simp only at hhh
        symm at hxy
        rcases hh with rfl | rfl <;>
        simp [Vector.singleton_def, Pointer.terminal.injEq, Bool.true_eq, OBdd.toTree_terminal,
          OBdd.toTree_eq_leaf_iff_terminal] at hxy <;>
        exact hxy.symm
      | inr hhh =>
        simp only at hhh
        rcases hhh with ⟨i, hi, hhh⟩
        injection hi with hi
        rw [← hi] at hhh
        simp at hhh
        rcases hh with (rfl | rfl) <;>
        · symm at hxy
          simp only [Vector.singleton_def, OBdd.subBdd_eq, Pointer.terminal.injEq, Bool.false_eq,
            OBdd.toTree_terminal, OBdd.toTree_eq_leaf_iff_terminal] at hxy
          exact hxy.symm

/-- Return the `BDD` representing the `n`th projection function. -/
public def var (n : Nat) : BDD :=
  { nvars := n + 1,
    nheap := 1,
    obdd  := ⟨⟨Vector.singleton ⟨⟨n, Nat.lt_add_one n⟩, .terminal false, .terminal true⟩, .node 0⟩, var_ordered⟩,
    hred  := var_reduced
  }

@[simp, bdd_nvars]
public lemma var_nvars {i} : (var i).nvars = i + 1 := (rfl)

@[simp]
public lemma getElem_var {i n} {h : i < n} :
    ∀ I : Vector Bool n, (var i)[I]'(by rw [var_nvars]; omega) = I[i] := by
  intro I
  simp only [var, Vector.singleton_def, getElem_eq_evaluate, lift,
    Evaluate.evaluate_evaluate, Lift.olift_evaluate, Pointer.node.injEq,
    OBdd.evaluate_node, Fin.getElem_fin, Fin.val_eq_zero, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, Vector.getElem_cast, OBdd.high_root_eq_high, Pointer.terminal.injEq,
    Bool.true_eq, OBdd.evaluate_terminal, OBdd.low_root_eq_low, Bool.false_eq, Bool.if_false_right,
    Bool.decide_eq_true, Bool.and_true, Vector.getElem_take]

@[simp]
public lemma var_dependsOn {n i} :
    (var n).DependsOn i ↔ i = n := by
  rw [dependsOn_iff (n + 1) (by simp)]
  simp only [ne_eq, Fin.getElem_fin, Nat.lt_add_one, getElem_var]
  constructor
  · rintro ⟨v1, v2, h2, h3⟩
    by_contra h4
    apply h3
    exact h2 ⟨n, by omega⟩ h4
  · rintro rfl
    let v := Vector.replicate (i + 1) false
    use v, v.set i true
    simp_all [v]

/-- Apply the given binary Boolean operator to the two `BDD`s. -/
public def apply : (Bool → Bool → Bool) → BDD → BDD → BDD := fun op B C ↦
  let r := Reduce.oreduce (Apply.oapply op B.obdd C.obdd).2
  ⟨_, _, r.1.2, r.2.1⟩

@[simp, bdd_nvars]
public lemma apply_nvars {B C : BDD} {o} : (apply o B C).nvars = max B.nvars C.nvars := (rfl)

@[simp]
public lemma getElem_apply {n} {B C : BDD} {op} {h1 : max B.nvars C.nvars ≤ n} :
    ∀ I : Vector Bool n, (apply op B C)[I] = op B[I] C[I] := by
  wlog h2 : n = max B.nvars C.nvars
  · intro I
    have h3 : B[I] = B[I.take (apply op B C).nvars] := by
      rw [getElem_take] <;> simp_all
    have h4 : C[I] = C[I.take (apply op B C).nvars] := by
      rw [getElem_take] <;> simp_all
    rw [← getElem_take', h3, h4]
    apply this
    simp_all only [sup_le_iff, forall_and_index, Vector.take_eq_extract, apply_nvars,
      inf_of_le_left]
  · rcases h2 with ⟨rfl⟩
    simp only [getElem_eq_evaluate, Evaluate.evaluate_evaluate, lift, Lift.olift_evaluate]
    simp [apply, Apply.oapply_correct]

public lemma apply_dependsOn {o} {B C : BDD} {i} :
    (apply o B C).DependsOn i → B.DependsOn i ∨ C.DependsOn i := by
  repeat rw [dependsOn_iff (max B.nvars C.nvars) (by simp)]
  grind only [getElem_apply]

/-- Return the conjuction of the two given `BDD`s. -/
public def and : BDD → BDD → BDD := apply Bool.and

@[simp, bdd_nvars]
public lemma and_nvars {B C : BDD} : (B.and C).nvars = max B.nvars C.nvars := apply_nvars

@[simp]
public lemma getElem_and {B C : BDD} {n} {h : (B.and C).nvars ≤ n} :
    ∀ I : Vector Bool n, (B.and C)[I] = (B[I] && C[I]) :=
  getElem_apply

public lemma and_dependsOn {B C : BDD} {i} :
    (B.and C).DependsOn i → B.DependsOn i ∨ C.DependsOn i :=
  apply_dependsOn

/-- Return the disjunction of the two given `BDD`s. -/
public def or  : BDD → BDD → BDD := apply Bool.or

@[simp, bdd_nvars]
public lemma or_nvars {B C : BDD} : (B.or C).nvars = max B.nvars C.nvars := apply_nvars

@[simp]
public lemma getElem_or {B C : BDD} {n} {h : (B.or C).nvars ≤ n} :
    ∀ I : Vector Bool n, (B.or C)[I] = (B[I] || C[I]) := getElem_apply

public lemma or_dependsOn {B C : BDD} {i} :
    (B.or C).DependsOn i → B.DependsOn i ∨ C.DependsOn i :=
  apply_dependsOn

/-- Return the exclusive disjunction of the two given `BDD`s. -/
public def xor : BDD → BDD → BDD := apply Bool.xor

@[simp, bdd_nvars]
public lemma xor_nvars {B C : BDD} : (B.xor C).nvars = max B.nvars C.nvars :=
  apply_nvars

@[simp]
public lemma getElem_xor {B C : BDD} {n} {h : (B.xor C).nvars ≤ n} :
    ∀ I : Vector Bool n, (B.xor C)[I] = (B[I] ^^ C[I]) :=
  getElem_apply

public lemma xor_dependsOn {B C : BDD} {i} :
    (B.xor C).DependsOn i → B.DependsOn i ∨ C.DependsOn i :=
  apply_dependsOn

/-- Compute the logical implication `a → b` of the two given `BDD`s. -/
public def imp : BDD → BDD → BDD := apply (! · || ·)

@[simp, bdd_nvars]
public lemma imp_nvars {B C : BDD} : (B.imp C).nvars = max B.nvars C.nvars := apply_nvars

@[simp]
public lemma getElem_imp {B C : BDD} {n} {h : (B.imp C).nvars ≤ n} :
    ∀ I : Vector Bool n, (B.imp C)[I] = (!B[I] || C[I]) :=
  getElem_apply

public lemma imp_dependsOn {B C : BDD} {i} :
    (B.imp C).DependsOn i → B.DependsOn i ∨ C.DependsOn i :=
  apply_dependsOn

/-- Return the negation of the given `BDD`. -/
public def not : BDD → BDD :=
  fun B ↦ imp B (const false)

@[simp, bdd_nvars]
public lemma not_nvars {B : BDD} : B.not.nvars = B.nvars := by
  simp only [not, imp, apply_nvars, const_nvars, Nat.zero_le, sup_of_le_left]

@[simp]
public lemma getElem_not {n} {B : BDD} {h : B.not.nvars ≤ n} :
    ∀ I : Vector Bool n, B.not[I] = !B[I] := by
  grind only [not, getElem_imp, getElem_const]

@[simp]
public lemma not_dependsOn {B : BDD} {i} : B.not.DependsOn i ↔ B.DependsOn i := by
  repeat rw [dependsOn_iff B.nvars (by simp)]
  simp [getElem_not]

def relabel' (B : BDD) (f : Nat → Nat)
      (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
      (h2 : ∀ i i' : Fin B.nvars, B.DependsOn i → B.DependsOn i' → i < i' → f i < f i') :
    BDD :=
  ⟨ f B.nvars, _,
    Relabel.orelabel B.obdd h1 (by
      intro i i' hii' hi hi'
      rw [OBdd.usesVar_iff_dependsOn_of_reduced B.hred] at hi
      rw [OBdd.usesVar_iff_dependsOn_of_reduced B.hred] at hi'
      grind only [Fin.is_lt, dependsOn_iff_evaluate, Evaluate.evaluate_evaluate]),
    Relabel.orelabel_reduced B.hred
  ⟩

def relabel_wrap (m n : Nat) (f : Fin m → Fin n) : Nat → Nat :=
  fun i ↦ if h : i < m then f ⟨i, h⟩ else n

@[simp]
lemma relabel_helper_aux {m n f} : relabel_wrap m n f m = n := by
  simp [relabel_wrap]

@[simp]
lemma relabel_helper_aux' {m n f} {i : Fin m} : relabel_wrap m n f i.1 = f i := by
  simp [relabel_wrap]

/-- Relabel the variables in a `BDD` according to a relabeling function `f`.

See also `getElem_relabel`. -/
public def relabel (B : BDD) (f : Fin B.nvars → Fin n)
    (h : ∀ i i' : Fin B.nvars, B.DependsOn i → B.DependsOn i' → i < i' → f i < f i') : BDD :=
  relabel' B (relabel_wrap B.nvars n f) (by simp) (fun i i' h' hi hi' ↦ by simp [h i i' h' hi hi'])

@[simp, bdd_nvars]
public lemma relabel_nvars {B : BDD} {f : _ → Fin n} {h} : (relabel B f h).nvars = n := by
  simp [relabel, relabel']

@[simp]
lemma getElem_relabel' {B : BDD} {f : Nat → Nat} {hf hu n} {I : Vector Bool n} {h} :
    (relabel' B f hf hu)[I] = B[Vector.ofFn fun i ↦ I[f i]'(lt_of_lt_of_le (hf i) h)] := by
  simp_rw [getElem_eq_evaluate, Evaluate.evaluate_evaluate, lift, relabel']
  simp
  grind only [Vector.getElem_extract]

@[simp]
public lemma getElem_relabel {B : BDD} {n} {f : Fin B.nvars → Fin n} {hf} {m} {I : Vector Bool m}
    (h1 : n ≤ m) : (relabel B f hf)[I] = B[Vector.ofFn (I[f ·])] := by
  simp only [relabel, getElem_relabel', relabel_helper_aux', Fin.getElem_fin]

noncomputable def relabel_vector (B : BDD) {n} (f : Fin B.nvars → Fin n) (v : Vector Bool B.nvars) :
    Vector Bool n :=
  have : ∀ i, Decidable (∃ j : Fin B.nvars, B.DependsOn j ∧ i = f j) := by
      intro i
      apply Classical.propDecidable
  Vector.ofFn fun i ↦
    if h : ∃ j : Fin B.nvars, B.DependsOn j ∧ i = f j then v[h.choose.val] else false

lemma relabel_dependsOn_aux {B : BDD} {n} {f : Fin B.nvars → Fin n}
    (hf : ∀ (i i' : Fin B.nvars), B.DependsOn ↑i → B.DependsOn ↑i' → i < i' → f i < f i') v :
    B[v] = (B.relabel f hf)[B.relabel_vector f v] := by
  simp only [relabel_vector, Std.le_refl, getElem_relabel]
  apply congrInterpretation
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  intro i hi
  split
  next h =>
    grind only [= Fin.getElem_fin, usr Exists.choose_spec]
  next h =>
    grind only

public lemma relabel_dependsOn {B : BDD} {n} {f : Fin B.nvars → Fin n} {hf} {i : Fin n} :
    (B.relabel f hf).DependsOn i ↔ ∃ j, i = f j ∧ B.DependsOn j := by
  have h1 : ∀ i i' : Fin B.nvars, B.DependsOn i → B.DependsOn i' →  (f i = f i' ↔ i = i') := by
    grind only
  rw [dependsOn_iff n (by simp)]
  constructor
  · rintro ⟨v1, v2, h2, h3⟩
    simp at h3
    obtain ⟨j, hj, h4⟩ := dependsOn_getElem_ne_of_ne h3
    use j
    specialize h2 ((f j).castLE (by omega))
    grind only [= Fin.getElem_fin, = Fin.val_castLE, = Vector.getElem_ofFn, = Lean.Grind.toInt_fin]
  · rintro ⟨j, rfl, h1⟩
    rw [dependsOn_iff B.nvars (by simp)] at h1
    rcases h1 with ⟨v1, v2, h1, h2⟩
    use relabel_vector B f v1, relabel_vector B f v2
    constructor
    · intro i h3
      simp only [relabel_vector, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
      split
      next h =>
        grind only [= Fin.getElem_fin, usr Exists.choose_spec]
      next h =>
        grind only
    · simp only [Std.le_refl, getElem_relabel, Fin.getElem_fin]
      intro h3
      obtain ⟨j, hj, h4⟩ := dependsOn_getElem_ne_of_ne h2
      apply h2
      rw [relabel_dependsOn_aux hf v1, relabel_dependsOn_aux hf v2]
      simp only [Std.le_refl, getElem_relabel, Fin.getElem_fin, h3]

/-- Return a satisfying assignment for the given `BDD`, assuming it is satisfiable. -/
public def choice {B : BDD} (s : ∃ I : Vector Bool B.nvars, B[I]) : Vector Bool B.nvars :=
  Choice.choice B.obdd (by simp_all [getElem_eq_evaluate, Evaluate.evaluate_evaluate, lift])

@[simp]
public lemma getElem_choice {B : BDD} {s : ∃ I : Vector Bool B.nvars, B[I]} : B[B.choice s] = true := by
  simp only [choice, getElem_eq_evaluate, lift, Lift.olift_trivial_eq, Evaluate.evaluate_evaluate]
  apply Choice.choice_evaluate B.hred

lemma find_aux' {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool (max B.nvars 0)), B[I] := by
  intro h
  contrapose h
  simp_all only [not_exists, Bool.not_eq_true, SemanticEquiv, getElem_const]
  exact h

lemma find_aux {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool B.nvars), B[I] := by
  intro h
  rcases find_aux' h with ⟨I, hI⟩
  use I.cast (show (max B.nvars 0) = B.nvars by simp)
  simp [hI]

/--
Return `some` input vector that satisfying the given `BDD`, or `none` if none exists.
See also `choice`.
-/
public def find {B : BDD} : Option (Vector Bool B.nvars) :=
  if h : B.SemanticEquiv (const false) then none else some (choice (find_aux h))

public lemma find_none {B : BDD} : B.find.isNone → ∀ I : Vector Bool B.nvars, B[I] = false := by
  intro h I
  simp only [find] at h
  split at h
  next ht =>
    simp only [SemanticEquiv, getElem_const] at ht
    specialize ht (Vector.cast (by simp) I)
    simp_all only [Option.isNone_none, le_refl, getElem_cast]
  next hf => contradiction

public lemma find_some {B : BDD} {I : Vector Bool B.nvars} : B.find = some I → B[I] = true := by
  intro h
  simp only [find] at h
  split at h
  next ht => contradiction
  next hf => injection h with heq; simp [← heq]

def restrict' (B : BDD) (b : Bool) (i : Fin B.nvars) : BDD :=
  let r := Reduce.oreduce (Restrict.orestrict b i B.obdd).2
  ⟨_, _, r.1.2, r.2.1⟩

/-- Return the `BDD` obtained by fixing variable `i` to value `b` in `B`. -/
public def restrict (b : Bool) (i : Nat) (B : BDD) : BDD :=
  if h : i < B.nvars
  then restrict' B b ⟨i, h⟩
  else B

public lemma restrict_geq_eq_self {B : BDD} : i ≥ B.nvars → B.restrict b i = B := by
  grind only [restrict]

@[simp, bdd_nvars]
public lemma restrict_nvars {B : BDD} {i} : (B.restrict b i).nvars = B.nvars := by
  simp only [restrict, restrict']
  split <;> simp

@[simp]
lemma Vector.cast_set {v : Vector α n} {i : Fin m} :
  (Vector.cast h v).set i a = Vector.cast h (v.set i a) := by rfl

@[simp]
public lemma getElem_restrict {B : BDD} {i} {hi : i < n} {h} : ∀ I : Vector Bool n,
    (B.restrict b i)[I] = B[I.set i b] := by
  intro I
  simp only [restrict]
  split
  next hlt =>
    simp only [restrict', getElem_eq_evaluate, lift, Evaluate.evaluate_evaluate, Lift.olift_evaluate]
    simp only [Reduce.oreduce_evaluate]
    simp only [Vector.take_eq_extract, Restrict.orestrict_correct, Nary.restrict]
    congr
    grind only [Vector.getElem_set_ne, Vector.getElem_cast, = Vector.getElem_set,
      Vector.getElem_extract]
  next hlt =>
    apply congrInterpretation
    grind only [Fin.getElem_fin, Vector.getElem_set]

public lemma restrict_dependsOn {B : BDD} {b i j} {hi : i < B.nvars} :
    (B.restrict b i).DependsOn j → B.DependsOn j ∧ i ≠ j := by
  repeat rw [dependsOn_iff B.nvars (by simp)]
  rintro ⟨v1, v2, h1, h2⟩
  simp only [hi, getElem_restrict] at h2
  obtain ⟨j', h3, h4⟩ := dependsOn_getElem_ne_of_ne h2
  grind only [= Fin.getElem_fin, = Vector.getElem_set]

@[no_expose]
public instance instDecidableDependsOn (B : BDD) : DecidablePred B.DependsOn :=
  fun i ↦
    if hi : i < B.nvars then
      decidable_of_iff (B.obdd.bdd.usesVar ⟨i, hi⟩) (by
        rw [dependsOn_iff_evaluate, Evaluate.evaluate_evaluate]
        exact OBdd.usesVar_iff_dependsOn_of_reduced B.hred)
    else
      isFalse (not_dependsOn_of_ge (by omega))

/-- Eliminate the variable `i` from the given `BDD` via universal quantification. -/
public def bforall (B : BDD) (i : Nat) : BDD := (and (B.restrict false i) (B.restrict true i))

/-- Eliminate variables in `l` from the given `BDD` via universal quantification. -/
public def bforalls (B : BDD) (l : List Nat) := List.foldl bforall B l

@[simp, bdd_nvars]
public lemma bforall_nvars {B : BDD} {i} : (B.bforall i).nvars = B.nvars := by
  simp only [bforall, and_nvars, restrict_nvars, max_self]

@[simp]
public lemma getElem_bforall {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bforall i)[I] = decide (∀ b, B[I.set i b]) := by
  simp_all only [bforall, getElem_and, getElem_restrict, Bool.forall_bool, Bool.decide_and,
    Bool.decide_eq_true]

public lemma bforall_dependsOn {B : BDD} {i j} {hi : i < B.nvars} :
    (B.bforall i).DependsOn j → B.DependsOn j ∧ i ≠ j := by
  intro h
  simp [bforall] at h
  obtain (h1 | h1) := and_dependsOn h
  · exact restrict_dependsOn h1 (hi := hi)
  · exact restrict_dependsOn h1 (hi := hi)

@[simp]
public lemma bforall_idem {B : BDD} {i n} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall i)[I] = (B.bforall i)[I] := by
  repeat (rw [getElem_bforall (hi := hi)]; simp_all)

public lemma bforall_comm {B : BDD} {i j : Fin B.nvars} {n} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall j)[I] = ((B.bforall j).bforall i)[I] := by
  repeat
    ( rw [getElem_bforall (i := i.1) (hi := by simp_all; omega)]
      rw [getElem_bforall (i := j.1) (hi := by simp_all; omega)]
      simp only [Bool.forall_bool, Bool.decide_and, Bool.decide_eq_true]
    )
  cases decEq j.1 i.1 with
  | isTrue ht => simp_rw [ht]
  | isFalse hf =>
    rw [show ((I.set (↑j) false _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) false _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    grind only

/-- Eliminate the variable `i` from the given `BDD` via existential quantification. -/
public def bexists (B : BDD) (i : Nat) : BDD := (or (B.restrict false i) (B.restrict true i))

/-- Eliminate variables in `l` from the given `BDD` via existential quantification. -/
public def bexistss (B : BDD) (l : List Nat) : BDD := List.foldl bexists B l

@[simp, bdd_nvars]
public lemma bexists_nvars {B : BDD} {i} : (B.bexists i).nvars = B.nvars := by simp [bexists]

@[simp]
public lemma getElem_bexists {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bexists i)[I] = decide (∃ b, B[I.set i b]) := by simp_all [bexists]

public lemma bexists_dependsOn {B : BDD} {i j} {hi : i < B.nvars} :
    (B.bexists i).DependsOn j → B.DependsOn j ∧ i ≠ j := by
  intro h
  simp [bexists] at h
  obtain (h1 | h1) := or_dependsOn h
  · exact restrict_dependsOn h1 (hi := hi)
  · exact restrict_dependsOn h1 (hi := hi)

@[simp]
public lemma bexists_idem {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bexists i).bexists i)[I] = (B.bexists i)[I] := by
  repeat (rw [getElem_bexists (hi := hi)]; simp_all)

public lemma bexists_comm {B : BDD} {i j : Fin B.nvars} {I : Vector Bool n} {h} :
    ((B.bexists i).bexists j)[I] = ((B.bexists j).bexists i)[I] := by
  repeat
    ( rw [getElem_bexists (i := i.1) (hi := by simp_all; omega)]
      rw [getElem_bexists (i := j.1) (hi := by simp_all; omega)]
      simp only [Bool.exists_bool, Bool.decide_or, Bool.decide_eq_true]
    )
  cases decEq j.1 i.1 with
  | isTrue ht => simp_rw [ht]
  | isFalse hf =>
    rw [show ((I.set (↑j) false _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) false _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    grind only

/-- Return the number of satisfying assignments the given `BDD`. -/
public def count (B : BDD) : Nat := Count.count B.obdd

public lemma count_eq_card {B : BDD} :
    B.count = Fintype.card { I : Vector Bool B.nvars // B[I] = true } := by
  simp only [count, Count.count_correct, Count.numSolutions, Count.Solution, getElem_eq_evaluate,
    lift, Lift.olift_trivial_eq, Evaluate.evaluate_evaluate]

end BDD
