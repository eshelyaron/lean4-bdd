module

public import Bdd.Nary
public import Bdd.Sim
-- Only for Fintype instance for Vector
public import Bdd.Count
import Bdd.Reduce
import Bdd.Apply
import Bdd.Relabel
import Bdd.Choice
import Bdd.Restrict
import Bdd.Evaluate
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

@[simp]
abbrev evaluate (B : BDD) : Vector Bool B.nvars → Bool := Evaluate.evaluate B.obdd

/-- Raise the input size (`nvars`) of a `BDD` to `n`, given a proof that the current input size is at most `n`. -/
public def lift (B : BDD) (h : B.nvars ≤ n) : BDD :=
  ⟨n, _, Lift.olift h B.obdd, Lift.olift_reduced B.hred⟩

/-- Lifting a `BDD` to `n` yields a `BDD` with input size (`nvars`) of `n`. -/
@[simp]
public lemma lift_nvars {B : BDD} {h : B.nvars ≤ n} : (B.lift h).nvars = n := (rfl)

/-- Lifting a `BDD` `B` to its current input size (`nvars`) yields back `B`. -/
@[simp]
public lemma lift_refl {B : BDD} : (B.lift (Nat.le_refl _)) = B := by simp [lift]

/-- The `denotation` of a `BDD` is the Boolean function that it represents. -/
public def denotation (B : BDD) (h : B.nvars ≤ n) : Vector Bool n → Bool := (B.lift h).evaluate

@[simp]
public abbrev denotation' O := denotation O (le_refl _)

/-- `lift` does not affect `denotation`. -/
@[simp]
public lemma lift_denotation {B : BDD} {h1 : B.nvars ≤ n} {h2 : n ≤ m} :
    (B.lift h1).denotation (le_of_eq_of_le lift_nvars h2)  = B.denotation (.trans h1 h2) := by
  simp [denotation, lift, Evaluate.evaluate_evaluate]

/-- `denotation` absorbs `Vector.cast`. -/
@[simp]
public lemma denotation_cast {B : BDD} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} (h : n = m) :
    B.denotation hm (Vector.cast h I) = B.denotation hn I := by
  subst h
  simp

/-- The `denotation` of a `BDD` is independent of indices greater or equal to its input size. -/
public lemma denotation_independentOf_of_geq_nvars {n : Nat} {i : Fin n} {B : BDD} {h1 : B.nvars ≤ n} {h2 : B.nvars ≤ i} :
    Nary.IndependentOf (B.denotation h1) i := by
  rintro b I
  simp only [denotation, Evaluate.evaluate_evaluate, Lift.olift_evaluate, lift]
  suffices s : (I.set i b).take B.nvars = I.take B.nvars by rw [s]
  ext j hj
  simp only [Vector.getElem_take]
  rw [Vector.getElem_set_ne _ _ (by omega)]

/-- `BDD`s are semantically equivalent when their `denotation`s coincide. -/
@[expose]
public def SemanticEquiv (B C : BDD) := B.denotation (le_max_left ..) = C.denotation (le_max_right ..)

def Similar (B : BDD) (B' : BDD) :=
  (Lift.olift (Nat.le_max_left ..) B.obdd).HSimilar (Lift.olift (Nat.le_max_right ..) B'.obdd)

public lemma denotation_take {B : BDD} {hn : B.nvars ≤ n} {hm1 : B.nvars ≤ m} {hm2 : m ≤ n}:
    B.denotation hn I = B.denotation (by simp_all) (I.take m) := by
  simp [denotation, Evaluate.evaluate_evaluate, lift]
  congr!
  omega

public lemma denotation_take' {B : BDD} {hn : B.nvars ≤ n} :
    B.denotation hn I = B.denotation (Nat.le_refl _) (Vector.cast (by simp_all) (I.take B.nvars)) := by
  simp [denotation, Evaluate.evaluate_evaluate, lift]

lemma Vector.append_take (v : Vector α n) (u : Vector α m) : (v ++ u).take n = (Vector.cast (by simp) v) := by
  ext i hi
  simp only [Vector.getElem_cast, Vector.getElem_take hi]
  exact Vector.getElem_append_left (by omega)

lemma denotation_append {B : BDD} {hn : B.nvars ≤ n} {hm : n ≤ m} {J : Vector Bool (m - n)} :
    B.denotation hn I = B.denotation (n := m) (.trans hn hm) (Vector.cast (by omega) (I ++ J)) := by
  rw [denotation_cast]
  swap; omega
  conv =>
    rhs
    rw [denotation_take (m := n) (hn := by omega) (hm1 := hn) (hm2 := by simp)]
  rw [Vector.append_take, denotation_cast]

lemma denotation_eq_of_denotation_eq_leq (B C : BDD) (hn : max B.nvars C.nvars ≤ n) (hm : max B.nvars C.nvars ≤ m) (hnm : n ≤ m):
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) →
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) := by
  intro h
  ext I
  rw [denotation_take (hm2 := hnm)]
  rw [denotation_take (hm2 := hnm)]
  rw [← denotation_cast (show min n m = n by omega)]
  rw [← denotation_cast (show min n m = n by omega)]
  rw [h]
  all_goals omega

lemma denotation_eq_of_denotation_eq_geq (B C : BDD) (hn : max B.nvars C.nvars ≤ n) (hm : max B.nvars C.nvars ≤ m) (hnm : n ≤ m):
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) →
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) := by
  intro h
  ext I
  rw [denotation_append (hm := hnm) (J := Vector.replicate _ false)]
  rw [denotation_append (hm := hnm) (J := Vector.replicate _ false)]
  rw [h]

/-- If two `BDD` have the same `denotation` with respect to some input size `n`, then they have the same `denotation` with respect to any other input size `m` as well. -/
public lemma denotation_eq_of_denotation_eq {B C : BDD} (hn : B.nvars ⊔ C.nvars ≤ n) (hm : B.nvars ⊔ C.nvars ≤ m) :
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) →
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) := fun h ↦
  if hleq : n ≤ m
  then denotation_eq_of_denotation_eq_leq B C hn hm hleq h
  else denotation_eq_of_denotation_eq_geq _ _ hm hn (le_of_not_ge hleq) h

public lemma denotation_congr_dependsOn {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    (∀ i : Nary.Dependency B.denotation', I[i.val] = J[i.val]) →
    B.denotation hn I = B.denotation hm J := by
  intro h1
  have h2 : min B.nvars n = B.nvars := by omega
  have h3 : min B.nvars m = B.nvars := by omega
  suffices B.denotation' ((I.take B.nvars).cast h2) = B.denotation' ((J.take B.nvars).cast h3) by
    grind only [denotation_cast, !denotation_take]
  apply Nary.eq_of_forall_dependency_getElem_eq
  rintro ⟨j, h4⟩
  calc
  (I.take B.nvars)[↑j]
  _ = I[j] := by
    grind only [= Fin.getElem_fin, = Vector.getElem_take]
  _ = J[j] := by exact h1 ⟨j, h4⟩
  _ = (J.take B.nvars)[↑j] := by
    grind only [= Fin.getElem_fin, = Vector.getElem_take]

public lemma denotation_congr {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    (∀ i : Fin B.nvars, I[i] = J[i]) → B.denotation hn I = B.denotation hm J := by
  grind only [denotation_congr_dependsOn]

/-- `SemanticEquiv` is an equivalence relation on `BDD`. -/
public theorem SemanticEquiv.equivalence : Equivalence SemanticEquiv :=
  { refl := fun _ ↦ rfl,
    symm := fun h ↦ Eq.symm (denotation_eq_of_denotation_eq (by omega) (by omega) h),
    trans := by
      intro B C D hBC hCD
      simp_all only [SemanticEquiv]
      let m := max (max B.nvars C.nvars) D.nvars
      apply denotation_eq_of_denotation_eq (n := m) (by omega) (by omega)
      trans C.denotation (by omega)
      · exact denotation_eq_of_denotation_eq .refl (by omega) hBC
      · exact denotation_eq_of_denotation_eq .refl (by omega) hCD
  }

instance instDecidableSimilar : DecidableRel Similar
  | B, C =>
    Sim.decidableRobddHSimilar
      (Lift.olift (Nat.le_max_left  ..) B.obdd) (Lift.olift_reduced B.hred)
      (Lift.olift (Nat.le_max_right ..) C.obdd) (Lift.olift_reduced C.hred)

theorem SemanticEquiv_iff_Similar {B C : BDD} :
    B.SemanticEquiv C ↔ B.Similar C := ⟨l_to_r, r_to_l⟩ where
  l_to_r h := by
    simp [Evaluate.evaluate_evaluate, SemanticEquiv, denotation] at h
    exact OBdd.Canonicity (Lift.olift_reduced B.hred) (Lift.olift_reduced C.hred) h
  r_to_l h := by
    simp [SemanticEquiv, denotation, Evaluate.evaluate_evaluate]
    exact OBdd.Canonicity_reverse h

/-- `SemanticEquiv` is `Decidable`.

Use this instance to decide whether two `BDD`s are equivalent. -/
@[no_expose]
public instance instDecidableSemanticEquiv : DecidableRel SemanticEquiv
  | _, _ => decidable_of_iff' _ SemanticEquiv_iff_Similar

public def size : BDD → Nat
  | B => Size.size B.obdd

def zero_vars_to_bool (B : BDD) : B.nvars = 0 → Bool := fun h ↦
  match B.obdd.1.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ (Eq.subst h B.obdd.1.heap[j].var.2))

lemma zero_vars_to_bool_spec {B : BDD} (h : B.nvars = 0) : B.obdd.1.root = .terminal (B.zero_vars_to_bool h) := by
  simp only [zero_vars_to_bool]
  split
  next => assumption
  next => contradiction

/-- Return a `BDD` denoting the constantly-`b` function.

See also `const_denotation`. -/
public def const (b : Bool) : BDD :=
  { nvars := 0,
    nheap := 0,
    obdd  := ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩,
    hred  := Bdd.reduced_of_terminal
  }

abbrev var_raw (n : Nat) : Bdd (n+1) 1 := ⟨Vector.singleton ⟨⟨n, Nat.lt_add_one n⟩, .terminal false, .terminal true⟩, .node 0⟩

lemma var_ordered : Bdd.Ordered (var_raw n) := by
  apply Bdd.ordered_of_low_high_ordered rfl
  · simp only [Bdd.low]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    apply Bdd.Ordered_of_terminal
  · simp [Bdd.low]
    apply Fin.lt_def.mpr
    refine Nat.lt_succ_of_le ?_
    simp
  · simp only [Bdd.high]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    apply Bdd.Ordered_of_terminal
  · simp [Bdd.high]
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
    simp only [OBdd.SimilarRP] at hxy
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
        rcases hhh with hhh | hhh <;>
        apply Pointer.eq_terminal_of_reachable at hhh <;>
        simp_rw [← hh, hhh] at hxy <;>
        simp only [OBdd.Similar, OBdd.HSimilar] at hxy <;>
        unfold OBdd.toTree at hxy <;>
        simp at hxy
    | inr hh =>
      simp only at hh
      rcases hh with ⟨j, hj, hh⟩
      injection hj with hj
      rw [← hj] at hh
      simp at hh
      cases Pointer.Reachable_iff.mp hy with
      | inl hhh =>
        simp only at hhh
        rcases hh with hh | hh <;>
        apply Pointer.eq_terminal_of_reachable at hh <;>
        simp_rw [hh, ← hhh] at hxy <;>
        simp only [OBdd.Similar, OBdd.HSimilar] at hxy <;>
        unfold OBdd.toTree at hxy <;>
        simp at hxy
      | inr hhh =>
        simp only at hhh
        rcases hhh with ⟨i, hi, hhh⟩
        injection hi with hi
        rw [← hi] at hhh
        simp at hhh
        cases hh with
        | inl hh =>
          apply Pointer.eq_terminal_of_reachable at hh
          cases hhh with
          | inl hhh =>
            apply Pointer.eq_terminal_of_reachable at hhh
            simp_all
          | inr hhh =>
            apply Pointer.eq_terminal_of_reachable at hhh
            simp_rw [hh, hhh] at hxy
            simp [OBdd.Similar, OBdd.HSimilar] at hxy
        | inr hh =>
          cases hhh with
          | inl hhh =>
            apply Pointer.eq_terminal_of_reachable at hh
            apply Pointer.eq_terminal_of_reachable at hhh
            simp_rw [hh, hhh] at hxy
            simp only [OBdd.Similar, OBdd.HSimilar] at hxy
            unfold OBdd.toTree at hxy
            simp at hxy
          | inr hhh =>
            apply Pointer.eq_terminal_of_reachable at hh
            apply Pointer.eq_terminal_of_reachable at hhh
            rw [hh, hhh]

/-- Return a `BDD` denoting the `n`th projection function.

See also `var_denotation`. -/
public def var (n : Nat) : BDD :=
  { nvars := n + 1,
    nheap := 1,
    obdd  := ⟨⟨Vector.singleton ⟨⟨n, Nat.lt_add_one n⟩, .terminal false, .terminal true⟩, .node 0⟩, var_ordered⟩,
    hred  := var_reduced
  }

/-- Apply a binary Boolean operator to two `BDD`s.

See also `apply_denotation`. -/
public def apply : (Bool → Bool → Bool) → BDD → BDD → BDD := fun op B C ↦
  let r := Reduce.oreduce (Apply.oapply op B.obdd C.obdd).2.1
  ⟨_, _, r.1.2, r.2.1⟩

@[simp]
public lemma apply_nvars {B C : BDD} {o} : (apply o B C).nvars = B.nvars ⊔ C.nvars := by
  simp only [apply]

/-- Return a `BDD` denoting the conjuction of the denotations of two given `BDD`s.

See also `and_denotation`. -/
public def and : BDD → BDD → BDD := apply Bool.and

/-- Return a `BDD` denoting the disjunction of the denotations of two given `BDD`s.

See also `or_denotation`. -/
public def or  : BDD → BDD → BDD := apply Bool.or

public def xor : BDD → BDD → BDD := apply Bool.xor
public def imp : BDD → BDD → BDD := apply (! · || ·)

/-- Return a `BDD` denoting the negation of the denotation of a given `BDD`.

See also `not_denotation`. -/
public def not : BDD → BDD       := fun B ↦ imp B (const false)

@[simp]
public lemma const_nvars : (const b).nvars = 0 := (rfl)

@[simp]
public lemma const_denotation : (const b).denotation h = Function.const _ b := by
  simp [denotation, const, lift, Evaluate.evaluate_terminal, Lift.olift_preserves_root]

@[simp]
public lemma var_nvars : (var i).nvars = i + 1 := (rfl)

@[simp]
public lemma var_denotation {n i h1} {h2 : i < n} {I : Vector Bool n} :
    (var i).denotation h1 I = I[i]'h2 := by
  simp [denotation, evaluate, var, lift, Evaluate.evaluate_evaluate, Lift.olift_evaluate]
  have : (I.take (i + 1))[i] = I[i] := by
    apply Vector.getElem_take
  erw [← this]
  rfl

public lemma apply_denotation' {B C : BDD} {op} I :
    (apply op B C).denotation (le_refl _) I =
    (op (B.denotation (by simp_all) I) (C.denotation (by simp_all) I)) := by
  unfold apply
  generalize he : (apply op B C) = e
  unfold apply at he
  simp only [denotation, Evaluate.evaluate_evaluate, lift, Lift.olift_evaluate, Reduce.oreduce_evaluate]
  calc _
    _ = (Apply.oapply op (BDD.obdd B) (BDD.obdd C)).2.1.evaluate I := by simp
  exact (Apply.oapply op (BDD.obdd B) (BDD.obdd C)).2.2 I

@[simp]
public lemma apply_denotation {B C : BDD} {op} {I : Vector Bool n} {h} :
    (apply op B C).denotation h I =
    (op (B.denotation (by simp_all) I) (C.denotation (by simp_all) I)) := by
  rw [denotation_take']
  rw [apply_denotation']
  congr 1
  rw [denotation_cast (I := (I.take (apply op B C).nvars))]
  · nth_rw 2 [denotation_take] <;> simp_all
  · rw [denotation_cast]
    nth_rw 2 [denotation_take] <;> simp_all

@[simp]
public lemma and_nvars {B C : BDD} : (B.and C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
public lemma and_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.and C).denotation h I = ((B.denotation (by simp_all) I) && (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
public lemma or_nvars {B C : BDD} : (B.or C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
public lemma or_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.or C).denotation h I = ((B.denotation (by simp_all) I) || (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
public lemma xor_nvars {B C : BDD} : (B.xor C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
public lemma xor_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.xor C).denotation h I = ((B.denotation (by simp_all) I) ^^ (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
public lemma imp_nvars {B C : BDD} : (B.imp C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
public lemma imp_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.imp C).denotation h I = (!(B.denotation (by simp_all) I) || (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
public lemma not_nvars {B : BDD} : B.not.nvars = B.nvars := by
  simp only [not, imp, apply_nvars, const_nvars, Nat.zero_le, sup_of_le_left]

@[simp]
public lemma not_denotation {B : BDD} {I : Vector Bool n} {h} :
    B.not.denotation h I = ! B.denotation (by simp_all) I := by simp [not]

def relabel' (B : BDD) (f : Nat → Nat)
      (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
      (h2 : ∀ i i', i < i' → Nary.DependsOn B.denotation' i → Nary.DependsOn B.denotation' i' → f i < f i') :
    BDD :=
  ⟨ f B.nvars, _,
    Relabel.orelabel B.obdd h1 (by
      intro i i' hii' hi hi'
      rw [OBdd.usesVar_iff_dependsOn_of_reduced B.hred] at hi
      rw [OBdd.usesVar_iff_dependsOn_of_reduced B.hred] at hi'
      simp only [denotation, Evaluate.evaluate_evaluate, Lift.olift_trivial_eq, lift] at h2
      exact h2 i i' hii' hi hi'),
    Relabel.orelabel_reduced B.hred
  ⟩

def relabel'' (B : BDD) (f : Nat → Nat)
      (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
      (h2 : ∀ i i' : (Nary.Dependency B.denotation'), i.1 < i'.1 → f i.1 < f i'.1) :
    BDD :=
  relabel' B f h1 (fun i i' hii' hi hi' ↦ h2 ⟨i, hi⟩ ⟨i', hi'⟩ hii')

def relabel_wrap (m n : Nat) (f : Fin m → Fin n) : Nat → Nat :=
  fun i ↦ if h : i < m then f ⟨i, h⟩ else n

@[simp]
lemma relabel_helper_aux : relabel_wrap m n f m = n := by
  simp [relabel_wrap]

@[simp]
lemma relabel_helper_aux' {i : Fin m} : relabel_wrap m n f i.1 = f i := by
  simp [relabel_wrap]

/-- Relabel the variables in a `BDD` according to a relabeling function `f`.

See also `relabel_denotation`. -/
public def relabel (B : BDD) (f : Fin B.nvars → Fin n)
    (h : ∀ i i' : (Nary.Dependency B.denotation'), i.1 < i'.1 → f i.1 < f i'.1) :
  BDD := relabel'' B (relabel_wrap B.nvars n f) (by simp) (fun i i' h' ↦ by simp [h i i' h'])

@[simp]
public lemma relabel_nvars {B : BDD} {f : _ → Fin n} {h} : (relabel B f h).nvars = n := by
  simp [relabel, relabel'', relabel']

lemma relabel_spec {B : BDD} {f : Nat → Nat} {hf} {hu} {I} :
    (relabel'' B f hf hu).denotation (le_refl _) I = B.denotation' (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp [denotation, Evaluate.evaluate_evaluate, relabel'', relabel', lift]

@[simp]
lemma relabel''_denotation {B : BDD} {f : Nat → Nat} {hf} {hu} {I : Vector Bool n} {h} :
    (relabel'' B f hf hu).denotation h I =
    B.denotation' (Vector.ofFn (fun i ↦ I[f i]'(lt_of_lt_of_le (hf i) h))) := by
  rw [denotation_take']
  rw [relabel_spec]
  simp only [denotation']
  congr
  ext i
  simp only [Vector.getElem_cast]
  apply Vector.getElem_take

@[simp]
public lemma relabel_denotation {B : BDD} {f : Fin B.nvars → Fin n} {hf} {I : Vector Bool n} {h} :
    (relabel B f hf).denotation h I = B.denotation' (Vector.ofFn (fun i ↦ I[f i])) := by
  simp [relabel]

public lemma relabel_dependsOn {n} {B : BDD} {f : Fin B.nvars → Fin n} {hf h i} :
  Nary.DependsOn ((B.relabel f hf).denotation h) i ↔
  ∃ j, i = f j ∧ Nary.DependsOn B.denotation' j :=
  by
    have h1 : ∀ (i i' : Nary.Dependency B.denotation'), f i.val = f i'.val ↔ i = i' := by
      rintro i i'
      have := hf i i'
      specialize hf i i'
      grind only [Subtype.val_inj]
    simp only [Nary.DependsOn, Nary.IndependentOf, BDD.relabel_denotation, BDD.denotation',
      Fin.getElem_fin, Bool.forall_bool, not_and, not_forall]
    constructor
    · intro h2
      rw [imp_iff_not_or, not_forall] at h2
      rcases h2 with ⟨v, h2⟩ | ⟨v, h2⟩
      · have h3 := Nary.ne_implies_dependency_getElem_ne h2
        rcases h3 with ⟨j, h3⟩
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_set, Bool.if_false_left,
          ne_eq, Bool.eq_and_self, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          Classical.not_imp, Decidable.not_not, Fin.val_inj] at h3
        use j.val, h3.2
        intro h4
        use Vector.ofFn fun j ↦ (v.set i false)[f j]
        apply ne_of_ne_of_eq (ne_comm.1 h2)
        apply Nary.eq_of_forall_dependency_getElem_eq
        intro j'
        specialize h1 j j'
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Vector.getElem_set,
          Bool.if_false_left, Bool.if_true_left]
        grind only [= Lean.Grind.toInt_fin, Vector.getElem_set]
      · have h3 := Nary.ne_implies_dependency_getElem_ne h2
        rcases h3 with ⟨j, h3⟩
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Vector.getElem_set, Fin.val_inj,
          Bool.if_true_left, ne_eq, Bool.eq_or_self, decide_eq_true_eq, Classical.not_imp,
          Bool.not_eq_true] at h3
        use j.val, h3.1
        intro h4
        use Vector.ofFn fun j ↦ v[f j]
        apply ne_of_ne_of_eq h2
        apply Nary.eq_of_forall_dependency_getElem_eq
        rintro j'
        specialize h1 j j'
        simp only [h3, Vector.getElem_set, Bool.if_true_left, Fin.getElem_fin, Vector.getElem_ofFn,
          Fin.eta]
        grind only [= Lean.Grind.toInt_fin]
    · rintro ⟨j, rfl, h2⟩ h3
      simp_all only [Vector.set_set, not_true_eq_false, exists_const, imp_false, not_forall]
      rcases h2 with ⟨v, h2⟩
      apply h2
      have : ∀ i, Decidable (∃ j : Nary.Dependency B.denotation', i = f j.val) := by
        intro i
        apply Classical.propDecidable
      let g := fun i ↦ if h : ∃ j : Nary.Dependency B.denotation', i = f j.val then v[h.choose.val] else false
      have hg : ∀ j' : Nary.Dependency B.denotation', g (f j'.val) = v[j'.val] := by
        rintro ⟨j', hj'⟩
        simp [g]
        split
        next h =>
          obtain ⟨j'', h⟩ := h
          simp_all only [Classical.choose_eq']
          specialize h1 ⟨j', hj'⟩ j''
          simp [h] at h1
          rcases h1 with rfl
          simp
        next h =>
          rw [not_exists] at h
          specialize h ⟨j', hj'⟩
          simp at h
      specialize h3 (Vector.ofFn g)
      simp only [Vector.getElem_ofFn, Fin.eta, Vector.getElem_set, Fin.val_inj,
        Bool.if_false_left] at h3
      calc
        B.denotation le_rfl v
        _ = B.denotation le_rfl (Vector.ofFn fun i ↦ g (f i)) := by
          apply Nary.eq_of_forall_dependency_getElem_eq
          simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, hg, implies_true]
        _ = B.denotation le_rfl (Vector.ofFn fun i ↦ !decide (f j = f i) && g (f i)) := h3
        _ = B.denotation le_rfl (v.set j.val false _) := by
          apply Nary.eq_of_forall_dependency_getElem_eq
          simp only [denotation', Nary.DependsOn, Nary.IndependentOf, Fin.getElem_fin,
            Vector.getElem_ofFn, Fin.eta, Vector.getElem_set, Fin.val_inj, Bool.if_false_left, hg]
          apply Nary.ne_implies_dependency_getElem_ne at h2
          simp [Vector.getElem_set, Fin.val_inj] at h2
          rcases h2 with ⟨j, h2, rfl⟩
          intro j'
          specialize h1 j j'
          simp only [Nary.DependsOn, Nary.IndependentOf] at *
          grind only [usr Subtype.property, Subtype.val_inj]

/-- Return an input vector that satisfies the denotation of a given `BDD`, under the assumption that its denotation is satisfiable.

See also `choice_denotation`. -/
public def choice {B : BDD} (s : ∃ I, B.denotation' I) : Vector Bool B.nvars :=
  Choice.choice B.obdd (by simp_all [denotation, Evaluate.evaluate_evaluate, lift])

@[simp]
public lemma choice_denotation {B : BDD} {s : ∃ I, B.denotation' I} : B.denotation' (B.choice s) = true := by
  simp [choice, denotation, lift, Evaluate.evaluate_evaluate, Choice.choice_evaluate B.hred (by simp_all [denotation, Evaluate.evaluate_evaluate, lift])]

lemma find_aux' {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool (max B.nvars 0)), B.denotation (by simp) I := by
  intro h
  contrapose h
  simp_all only [not_exists, Bool.not_eq_true, SemanticEquiv, const_denotation]
  ext x
  simp only [Function.const_apply]
  apply h

lemma find_aux {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool B.nvars), B.denotation' I := by
  intro h
  rcases find_aux' h with ⟨I, hI⟩
  use ((show (max B.nvars 0) = B.nvars by simp) ▸ I)
  rw [← hI]
  clear hI
  congr! <;> simp

/-- Return `some` input vector that satisfies the denotation of a given `BDD`, or `none` if none exists.

See also `choice`, `find_none` and `find_some`. -/
public def find {B : BDD} : Option (Vector Bool B.nvars) :=
  if h : B.SemanticEquiv (const false) then none else some (choice (find_aux h))

public lemma find_none {B : BDD} : B.find.isNone → B.denotation' = Function.const _ false := by
  intro h
  ext I
  simp only [find] at h
  split at h
  next ht =>
    simp only [SemanticEquiv, const_denotation] at ht
    rw [funext_iff] at ht
    simp only [denotation']
    have := ht (Vector.cast (by simp) I)
    simp only [le_refl, denotation_cast, Function.const_apply] at this
    simpa
  next hf => contradiction

public lemma find_some {B : BDD} {I} : B.find = some I → B.denotation' I = true := by
  intro h
  simp only [find] at h
  split at h
  next ht => contradiction
  next hf => injection h with heq; simp [← heq]

def restrict' (B : BDD) (b : Bool) (i : Fin B.nvars) : BDD :=
  let r := Reduce.oreduce (Restrict.orestrict b i B.obdd).2.1
  ⟨_, _, r.1.2, r.2.1⟩

/-- Return a `BDD` denoting the restriction of a given `BDD` at an index `i` to a Boolean `b`.

See also `restrict_denotation`. -/
public def restrict (b : Bool) (i : Nat) (B : BDD) : BDD :=
  if h : i < B.nvars
  then restrict' B b ⟨i, h⟩
  else B

public lemma restrict_geq_eq_self {B : BDD} : i ≥ B.nvars → B.restrict b i = B := by
  intro h
  rw [restrict]
  split
  next ht => absurd h; simpa
  next => simp

@[simp]
public lemma restrict_nvars {B : BDD} {i} : (B.restrict b i).nvars = B.nvars := by
  simp only [restrict, restrict']
  split <;> simp

@[simp]
lemma Vector.cast_set {v : Vector α n} {i : Fin m} :
  (Vector.cast h v).set i a = Vector.cast h (v.set i a) := by rfl

@[simp]
public lemma restrict_denotation {B : BDD} {I : Vector Bool n} {i} {hi : i < n} {h} :
    (B.restrict b i).denotation h I =
    (Nary.restrict (B.denotation (restrict_nvars ▸ h)) b ⟨i, hi⟩) I := by
  simp only [restrict]
  split
  next hlt =>
    simp only [restrict', denotation, lift, evaluate, Evaluate.evaluate_evaluate, Lift.olift_evaluate]
    simp only [Reduce.oreduce_evaluate]
    have := (Restrict.orestrict b ⟨i, hlt⟩ (BDD.obdd B)).2.2
    rw [this]
    simp only [Nary.restrict, Vector.take_eq_extract, Lift.olift_evaluate]
    congr
    ext j hj
    simp
    rw [Vector.getElem_set]
    split
    next heq =>
      subst heq
      have := Vector.getElem_extract (as := I.set i b) (start := 0) (stop := B.nvars) (i := i) (by omega)
      simp_all
    next heq =>
      simp only [restrict_nvars] at h
      have := Vector.getElem_extract (as := I.set i b) (start := 0) (stop := B.nvars) (i := j) (by omega)
      have := Vector.getElem_extract (as := I) (start := 0) (stop := B.nvars) (i := j) (by omega)
      simp_all
  next hlt =>
    have := denotation_independentOf_of_geq_nvars (B := B) (h1 := restrict_nvars ▸ h) (h2 := (by simp_all)) (i := ⟨i, hi⟩)
    rw [Nary.restrict_eq_self_of_independentOf this]

@[no_expose]
public instance instDecidableDependsOn (B : BDD) : DecidablePred (Nary.DependsOn B.denotation') := fun i ↦
  (show B.denotation' = B.obdd.evaluate by simp [denotation, Evaluate.evaluate_evaluate, lift]) ▸
  (decidable_of_iff _ (OBdd.usesVar_iff_dependsOn_of_reduced B.hred))

/-- Universal quantification over input at index `i`.

See also `bforall_denotation`. -/
public def bforall (B : BDD) (i : Nat) : BDD := (and (B.restrict false i) (B.restrict true i))

/-- Universal quantification over a list of input indices `l`. -/
public def bforalls (B : BDD) (l : List Nat) := List.foldl bforall B l

@[simp]
public lemma bforall_nvars {B : BDD} {i} : (B.bforall i).nvars = B.nvars := by simp [bforall]

@[simp]
public lemma bforall_denotation {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bforall i).denotation h I = (∀ b, B.denotation (by simp_all) (I.set i b) : Bool) := by simp_all [bforall]

@[simp]
public lemma bforall_idem {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall i).denotation h I = (B.bforall i).denotation (by simp_all) I := by
  repeat (rw [bforall_denotation (hi := hi)]; simp_all)

public lemma bforall_comm {B : BDD} {i j : Fin B.nvars} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall j).denotation h I = ((B.bforall j).bforall i).denotation (by simp_all) I := by
  repeat
    ( rw [bforall_denotation (i := i.1) (hi := by simp_all; omega)]
      rw [bforall_denotation (i := j.1) (hi := by simp_all; omega)]
      simp only [Bool.forall_bool, Bool.decide_and, Bool.decide_eq_true]
    )
  cases decEq j.1 i.1 with
  | isTrue ht => simp_rw [ht]
  | isFalse hf => grind only [Vector.set_comm]

/-- Existential quantification over input at index `i`.

See also `bexists_denotation`. -/
public def bexists (B : BDD) (i : Nat) : BDD := (or (B.restrict false i) (B.restrict true i))

/-- Existential quantification over a list of input indices `l`. -/
public def bexistss (B : BDD) (l : List Nat) := List.foldl bexists B l

@[simp]
public lemma bexists_nvars {B : BDD} {i} : (B.bexists i).nvars = B.nvars := by simp [bexists]

@[simp]
public lemma bexists_denotation {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bexists i).denotation h I = ((∃ b, B.denotation (by simp_all) (I.set i b)) : Bool) := by simp_all [bexists]

@[simp]
public lemma bexists_idem {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bexists i).bexists i).denotation h I = (B.bexists i).denotation (by simp_all) I := by
  repeat (rw [bexists_denotation (hi := hi)]; simp_all)

public lemma bexists_comm {B : BDD} {i j : Fin B.nvars} {I : Vector Bool n} {h} :
    ((B.bexists i).bexists j).denotation h I = ((B.bexists j).bexists i).denotation (by simp_all) I := by
  repeat
    ( rw [bexists_denotation (i := i.1) (hi := by simp_all; omega)]
      rw [bexists_denotation (i := j.1) (hi := by simp_all; omega)]
      simp only [Bool.exists_bool, Bool.decide_or, Bool.decide_eq_true]
    )
  cases decEq j.1 i.1 with
  | isTrue ht => simp_rw [ht]
  | isFalse hf =>
    rw [show ((I.set (↑j) false _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) false _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [Bool.or_assoc]
    rw [Bool.or_assoc]
    congr 1
    conv =>
      rhs
      rw [Bool.or_comm]
      rw [Bool.or_assoc]
    congr 1
    rw [Bool.or_comm]

/-- Return the number of different input vectors for which the `denotation` of a given `BDD` returns `true`.

See also `count_eq_card`. -/
public def count (B : BDD) : Nat := Count.count B.obdd

public lemma count_eq_card {B : BDD} : B.count = Fintype.card { I // B.denotation' I = true } := by
  simp [count, denotation', denotation, lift, Evaluate.evaluate_evaluate, Count.count_corrent, Count.numSolutions, Count.Solution]

end BDD
