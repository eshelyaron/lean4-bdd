import Bdd.Reduce
import Bdd.Apply
import Bdd.Relabel
import Bdd.Choice
import Bdd.Restrict
import Bdd.Evaluate
import Bdd.Sim
import Bdd.Size

/-- Abstract BDD type. -/
structure BDD where
  /-- BDD input size (number of variables). -/
  nvars         : Nat
  private nheap : Nat
  private obdd  : OBdd nvars nheap
  private hred  : obdd.Reduced

namespace BDD


@[simp]
private abbrev evaluate (B : BDD) : Vector Bool B.nvars → Bool := Evaluate.evaluate B.obdd

/-- Raise the input size (`nvars`) of a `BDD` to `n`, given a proof that the current input size is at most `n`. -/
def lift (B : BDD) (h : B.nvars ≤ n) : BDD :=
  ⟨n, _, Lift.olift h B.obdd, Lift.olift_reduced B.hred⟩

/-- Lifting a `BDD` to `n` yields a `BDD` with input size (`nvars`) of `n`. -/
@[simp]
lemma lift_nvars {B : BDD} {h : B.nvars ≤ n} : (B.lift h).nvars = n := rfl

/-- Lifting a `BDD` `B` to its current input size (`nvars`) yields back `B`. -/
@[simp]
lemma lift_refl {B : BDD} : (B.lift (le_refl _)) = B := by simp [lift]

/-- The `denotation` of a `BDD` is the Boolean function that it represents. -/
def denotation (B : BDD) (h : B.nvars ≤ n) : Vector Bool n → Bool := (B.lift h).evaluate

/-- `lift` does not affect `denotation`. -/
@[simp]
lemma lift_denotation {B : BDD} {h1 : B.nvars ≤ n} {h2 : n ≤ m} :
    (B.lift h1).denotation h2 = B.denotation (.trans h1 h2) := by
  simp [denotation, lift, Evaluate.evaluate_evaluate]

/-- `denotation` absorbs `Vector.cast`. -/
@[simp]
lemma denotation_cast {B : BDD} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} (h : n = m) :
    B.denotation hm (Vector.cast h I) = B.denotation hn I := by
  subst h
  simp

/-- The `denotation` of a `BDD` is independent of indices that exceed its input size. -/
lemma denotation_independentOf_of_geq_nvars {n : Nat} {i : Fin n} {B : BDD} {h1 : B.nvars ≤ n} {h2 : B.nvars ≤ i} :
    Nary.IndependentOf (B.denotation h1) i := by
  rintro b I
  simp only [denotation, Evaluate.evaluate_evaluate, Lift.olift_evaluate, lift]
  suffices s : (I.set i b).take B.nvars = I.take B.nvars by rw [s]
  ext j hj
  simp only [Vector.getElem_take]
  rw [Vector.getElem_set_ne _ _ (by omega)]

/-- `BDD`s are semantically equivalent when their `denotation`s coincide. -/
def SemanticEquiv : BDD → BDD → Prop := fun B C ↦
  B.denotation (Nat.le_max_left  ..) = C.denotation (Nat.le_max_right ..)

private def Similar (B : BDD) (B' : BDD) :=
  (Lift.olift (Nat.le_max_left ..) B.obdd).HSimilar (Lift.olift (Nat.le_max_right ..) B'.obdd)

lemma denotation_take {B : BDD} {hn : B.nvars ≤ n} {hm1 : B.nvars ≤ m} {hm2 : m ≤ n}:
    B.denotation hn I = B.denotation (by simp_all) (I.take m) := by
  simp [denotation, Evaluate.evaluate_evaluate, lift]
  congr!
  omega

lemma denotation_take' {B : BDD} {hn : B.nvars ≤ n} :
    B.denotation hn I = B.denotation (le_refl _) (Vector.cast (by simp_all) (I.take B.nvars)) := by
  simp [denotation, Evaluate.evaluate_evaluate, lift]

private lemma Vector.append_take (v : Vector α n) (u : Vector α m) : (v ++ u).take n = (Vector.cast (by simp) v) := by
  ext i hi
  simp only [Nat.sub_zero, Vector.getElem_cast, Vector.getElem_take hi]
  exact Vector.getElem_append_left (by omega)

private lemma denotation_append {B : BDD} {hn : B.nvars ≤ n} {hm : n ≤ m} {J : Vector Bool (m - n)} :
    B.denotation hn I = B.denotation (n := m) (.trans hn hm) (Vector.cast (by omega) (I ++ J)) := by
  rw [denotation_cast]
  swap; omega
  conv =>
    rhs
    rw [denotation_take (m := n) (hn := by omega) (hm1 := hn) (hm2 := by simp)]
  rw [Vector.append_take, denotation_cast]

private lemma denotation_eq_of_denotation_eq_leq (B C : BDD) (hn : max B.nvars C.nvars ≤ n) (hm : max B.nvars C.nvars ≤ m) (hnm : n ≤ m):
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

private lemma denotation_eq_of_denotation_eq_geq (B C : BDD) (hn : max B.nvars C.nvars ≤ n) (hm : max B.nvars C.nvars ≤ m) (hnm : n ≤ m):
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) →
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) := by
  intro h
  ext I
  rw [denotation_append (hm := hnm) (J := Vector.replicate _ false)]
  rw [denotation_append (hm := hnm) (J := Vector.replicate _ false)]
  rw [h]

lemma denotation_eq_of_denotation_eq {B C : BDD} (hn : B.nvars ⊔ C.nvars ≤ n) (hm : B.nvars ⊔ C.nvars ≤ m) :
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) →
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) := fun h ↦
  if hleq : n ≤ m
  then denotation_eq_of_denotation_eq_leq B C hn hm hleq h
  else denotation_eq_of_denotation_eq_geq _ _ hm hn (le_of_not_le hleq) h

theorem SemanticEquiv.equivalence : Equivalence SemanticEquiv :=
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

private instance instDecidableSimilar : DecidableRel Similar
  | B, C =>
    Sim.instDecidableRobddHSimilar
      (Lift.olift (Nat.le_max_left  ..) B.obdd) (Lift.olift_reduced B.hred)
      (Lift.olift (Nat.le_max_right ..) C.obdd) (Lift.olift_reduced C.hred)

private theorem SemanticEquiv_iff_Similar {B C : BDD} :
    B.SemanticEquiv C ↔ B.Similar C := ⟨l_to_r, r_to_l⟩ where
  l_to_r h := by
    simp [Evaluate.evaluate_evaluate, SemanticEquiv, denotation] at h
    exact OBdd.Canonicity (Lift.olift_reduced B.hred) (Lift.olift_reduced C.hred) h
  r_to_l h := by
    simp [SemanticEquiv, denotation, Evaluate.evaluate_evaluate]
    exact OBdd.Canonicity_reverse h

instance instDecidableSemacticEquiv : DecidableRel SemanticEquiv
  | _, _ => decidable_of_iff' _ SemanticEquiv_iff_Similar

def size : BDD → Nat
  | B => Size.size B.obdd

private def zero_vars_to_bool (B : BDD) : B.nvars = 0 → Bool := fun h ↦
  match B.obdd.1.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ (Eq.subst h B.obdd.1.heap[j].var.2))

private lemma zero_vars_to_bool_spec {B : BDD} (h : B.nvars = 0) : B.obdd.1.root = .terminal (B.zero_vars_to_bool h) := by
  simp only [zero_vars_to_bool]
  split
  next => assumption
  next => contradiction

def const (b : Bool) : BDD :=
  { nvars := 0,
    nheap := 0,
    obdd  := ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩,
    hred  := Bdd.reduced_of_terminal
  }

private abbrev var_raw (n : Nat) : Bdd (n+1) 1 := ⟨Vector.singleton ⟨n, .terminal false, .terminal true⟩, .node 0⟩

private lemma var_ordered : Bdd.Ordered (var_raw n) := by
  apply Bdd.ordered_of_low_high_ordered rfl
  · simp only [Bdd.low]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    apply Bdd.Ordered_of_terminal
  · simp [Bdd.low, Fin.last]
    apply Fin.lt_def.mpr
    simp only [Fin.val_natCast]
    refine Nat.lt_succ_of_le ?_
    exact Nat.mod_le n (n + 1 + 1)
  · simp only [Bdd.high]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    apply Bdd.Ordered_of_terminal
  · simp [Bdd.high, Fin.last]
    apply Fin.lt_def.mpr
    simp only [Fin.val_natCast]
    refine Nat.lt_succ_of_le ?_
    exact Nat.mod_le n (n + 1 + 1)

private lemma var_reduced : OBdd.Reduced ⟨(var_raw n), var_ordered⟩ := by
  constructor
  · rintro ⟨p, hp⟩
    simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.isValue] at hp
    simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.isValue]
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
        simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at hxy <;>
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
        simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at hxy <;>
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
            simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at hxy
            unfold OBdd.toTree at hxy
            simp at hxy
          | inr hhh =>
            apply Pointer.eq_terminal_of_reachable at hh
            apply Pointer.eq_terminal_of_reachable at hhh
            rw [hh, hhh]

def var (n : Nat) : BDD :=
  { nvars := n + 1,
    nheap := 1,
    obdd  := ⟨⟨Vector.singleton ⟨n, .terminal false, .terminal true⟩, .node 0⟩, var_ordered⟩,
    hred  := var_reduced
  }

def apply : (Bool → Bool → Bool) → BDD → BDD → BDD := fun op B C ↦
  ⟨_, _, (Reduce.oreduce (Apply.oapply op B.obdd C.obdd).2.1).2, Reduce.oreduce_reduced⟩

@[simp]
lemma apply_nvars {B C : BDD} {o} : (apply o B C).nvars = B.nvars ⊔ C.nvars := by
  simp only [apply]

def and : BDD → BDD → BDD := apply Bool.and
def or  : BDD → BDD → BDD := apply Bool.or
def xor : BDD → BDD → BDD := apply Bool.xor
def imp : BDD → BDD → BDD := apply (! · || ·)
def not : BDD → BDD       := fun B ↦ imp B (const false)

@[simp]
lemma const_nvars : (const b).nvars = 0 := rfl

@[simp]
lemma const_denotation : (const b).denotation h = Function.const _ b := by
  simp [denotation, const, Evaluate.evaluate_terminal _, lift]

@[simp]
lemma var_nvars : (var i).nvars = i + 1 := rfl

@[simp]
lemma var_denotation : (var i).denotation h I = I[i] := by
  simp [denotation, evaluate, var, lift, Evaluate.evaluate_evaluate, Lift.olift_evaluate]
  rename_i n
  rw [var_nvars] at h
  have : (I.take (i + 1))[i] = I[i] := by
    apply Vector.getElem_take
  rw [← this]
  rfl

@[simp]
abbrev denotation' O := denotation O (le_refl _)

lemma apply_denotation' {B C : BDD} {op} I :
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
lemma apply_denotation {B C : BDD} {op} {I : Vector Bool n} {h} :
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
lemma and_nvars {B C : BDD} : (B.and C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
lemma and_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.and C).denotation h I = ((B.denotation (by simp_all) I) && (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
lemma or_nvars {B C : BDD} : (B.or C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
lemma or_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.or C).denotation h I = ((B.denotation (by simp_all) I) || (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
lemma xor_nvars {B C : BDD} : (B.xor C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
lemma xor_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.xor C).denotation h I = ((B.denotation (by simp_all) I) ^^ (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
lemma imp_nvars {B C : BDD} : (B.imp C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
lemma imp_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.imp C).denotation h I = (!(B.denotation (by simp_all) I) || (C.denotation (by simp_all) I)) := apply_denotation

@[simp]
lemma not_nvars {B : BDD} : B.not.nvars = B.nvars := by
  simp only [not, imp, apply_nvars, const_nvars, zero_le, sup_of_le_left]

@[simp]
lemma not_denotation {B : BDD} {I : Vector Bool n} {h} :
    B.not.denotation h I = ! B.denotation (by simp_all) I := by simp [not]

private def relabel' (B : BDD) (f : Nat → Nat)
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

private def relabel'' (B : BDD) (f : Nat → Nat)
      (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
      (h2 : ∀ i i' : (Nary.Dependency B.denotation'), i.1 < i'.1 → f i.1 < f i'.1) :
    BDD :=
  relabel' B f h1 (fun i i' hii' hi hi' ↦ h2 ⟨i, hi⟩ ⟨i', hi'⟩ hii')

private def relabel_wrap (m n : Nat) (f : Fin m → Fin n) : Nat → Nat :=
  fun i ↦ if h : i < m then f ⟨i, h⟩ else n

@[simp]
private lemma relabel_helper_aux : relabel_wrap m n f m = n := by
  simp [relabel_wrap]

@[simp]
private lemma relabel_helper_aux' {i : Fin m} : relabel_wrap m n f i.1 = f i := by
  simp [relabel_wrap]

def relabel (B : BDD) (f : Fin B.nvars → Fin n)
    (h : ∀ i i' : (Nary.Dependency B.denotation'), i.1 < i'.1 → f i.1 < f i'.1) :
  BDD := relabel'' B (relabel_wrap B.nvars n f) (by simp) (fun i i' h' ↦ by simp [h i i' h'])

@[simp]
lemma relabel_nvars {B : BDD} {f : _ → Fin n} {h} : (relabel B f h).nvars = n := by
  simp [relabel, relabel'', relabel']

private lemma relabel_spec {B : BDD} {f : Nat → Nat} {hf} {hu} {I} :
    (relabel'' B f hf hu).denotation (le_refl _) I = B.denotation' (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp [denotation, Evaluate.evaluate_evaluate, relabel'', relabel', lift]

@[simp]
private lemma relabel''_denotation {B : BDD} {f : Nat → Nat} {hf} {hu} {I : Vector Bool n} {h} :
    (relabel'' B f hf hu).denotation h I =
    B.denotation' (Vector.ofFn (fun i ↦ I[f i]'(lt_of_lt_of_le (hf i) h))) := by
  rw [denotation_take']
  rw [relabel_spec]
  simp only [denotation']
  congr
  ext i
  simp only [relabel_nvars, Vector.getElem_cast]
  apply Vector.getElem_take

@[simp]
lemma relabel_denotation {B : BDD} {f} {hf} {I : Vector Bool n} {h} :
    (relabel B f hf).denotation h I = B.denotation' (Vector.ofFn (fun i ↦ I[f i])) := by
  simp [relabel]

def choice {B : BDD} (s : ∃ I, B.denotation' I) : Vector Bool B.nvars :=
  Choice.choice B.obdd (by simp_all [denotation, Evaluate.evaluate_evaluate, lift])

@[simp]
lemma choice_denotation {B : BDD} {s : ∃ I, B.denotation' I} : B.denotation' (B.choice s) = true := by
  simp [choice, denotation, lift, Evaluate.evaluate_evaluate, Choice.choice_evaluate B.hred (by simp_all [denotation, Evaluate.evaluate_evaluate, lift])]

private lemma find_aux' {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool (max B.nvars 0)), B.denotation (by simp) I := by
  intro h
  contrapose h
  simp_all only [not_exists, Bool.not_eq_true, SemanticEquiv, const_nvars, const_denotation, not_not]
  ext x
  simp only [Function.const_apply]
  apply h

private lemma find_aux {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool B.nvars), B.denotation' I := by
  intro h
  rcases find_aux' h with ⟨I, hI⟩
  use ((show (max B.nvars 0) = B.nvars by simp) ▸ I)
  rw [← hI]
  clear hI
  congr! <;> simp

def find {B : BDD} : Option (Vector Bool B.nvars) :=
  if h : B.SemanticEquiv (const false) then none else some (choice (find_aux h))

-- def find_none' {B : BDD} : B.find.isNone → B.SemanticEquiv (const false) := by
--   intro h
--   simp only [find] at h
--   split at h
--   next ht _ => exact ht
--   next hf _ => contradiction

lemma find_none {B : BDD} : B.find.isNone → B.denotation' = Function.const _ false := by
  intro h
  ext I
  simp only [find] at h
  split at h
  next ht =>
    simp only [SemanticEquiv, const_nvars, const_denotation] at ht
    rw [funext_iff] at ht
    simp only [denotation']
    have := ht (Vector.cast (by simp) I)
    simp only [le_refl, denotation_cast, Function.const_apply] at this
    simpa
  next hf => contradiction

lemma find_some {B : BDD} {I} : B.find = some I → B.denotation' I = true := by
  intro h
  simp only [find] at h
  split at h
  next ht => contradiction
  next hf => injection h with heq; simp [← heq]


private def restrict' (B : BDD) (b : Bool) (i : Fin B.nvars) : BDD :=
  ⟨_, _, (Reduce.oreduce (Restrict.orestrict b i B.obdd).2.1).2, Reduce.oreduce_reduced⟩

def restrict (b : Bool) (i : Nat) (B : BDD) : BDD :=
  if h : i < B.nvars
  then restrict' B b ⟨i, h⟩
  else B

lemma restrict_geq_eq_self {B : BDD} : i ≥ B.nvars → B.restrict b i = B := by
  intro h
  rw [restrict]
  split
  next ht => absurd h; simpa
  next => simp

@[simp]
lemma restrict_nvars {B : BDD} {i} : (B.restrict b i).nvars = B.nvars := by
  simp only [restrict, restrict']
  split <;> simp

@[simp]
private lemma Vector.cast_set {v : Vector α n} {i : Fin m} :
  (Vector.cast h v).set i a = Vector.cast h (v.set i a) := by rfl

@[simp]
lemma restrict_denotation {B : BDD} {I : Vector Bool n} {i} {hi : i < n} {h} :
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

instance instDecidableDependsOn (B : BDD) : DecidablePred (Nary.DependsOn B.denotation') := fun i ↦
  (show B.denotation' = B.obdd.evaluate by simp [denotation, Evaluate.evaluate_evaluate, lift]) ▸
  (decidable_of_iff _ (OBdd.usesVar_iff_dependsOn_of_reduced B.hred))

def bforall (B : BDD) (i : Nat) : BDD := (and (B.restrict false i) (B.restrict true i))

def bforalls (B : BDD) (l : List Nat) := List.foldl bforall B l

@[simp]
lemma bforall_nvars {B : BDD} {i} : (B.bforall i).nvars = B.nvars := by simp [bforall]

@[simp]
lemma bforall_denotation {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bforall i).denotation h I = (∀ b, B.denotation (by simp_all) (I.set i b) : Bool) := by simp_all [bforall]

@[simp]
lemma bforall_idem {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall i).denotation h I = (B.bforall i).denotation (by simp_all) I := by
  repeat (rw [bforall_denotation (hi := hi)]; simp_all)

lemma bforall_comm {B : BDD} {i j : Fin B.nvars} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall j).denotation h I = ((B.bforall j).bforall i).denotation (by simp_all) I := by
  repeat
    ( rw [bforall_denotation (i := i.1) (hi := by simp_all; omega)]
      rw [bforall_denotation (i := j.1) (hi := by simp_all; omega)]
      simp only [Bool.forall_bool, Bool.decide_and, Bool.decide_eq_true]
    )
  cases decEq j.1 i.1 with
  | isTrue ht => simp_rw [ht]
  | isFalse hf =>
    rw [show ((I.set (↑j) false _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) false _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [Bool.and_assoc]
    rw [Bool.and_assoc]
    congr 1
    conv =>
      rhs
      rw [Bool.and_comm]
      rw [Bool.and_assoc]
    congr 1
    rw [Bool.and_comm]

def bexists (B : BDD) (i : Nat) : BDD := (or (B.restrict false i) (B.restrict true i))

def bexistss (B : BDD) (l : List Nat) := List.foldl bexists B l

@[simp]
lemma bexists_nvars {B : BDD} {i} : (B.bexists i).nvars = B.nvars := by simp [bexists]

@[simp]
lemma bexists_denotation {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bexists i).denotation h I = ((∃ b, B.denotation (by simp_all) (I.set i b)) : Bool) := by simp_all [bexists]

@[simp]
lemma bexists_idem {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bexists i).bexists i).denotation h I = (B.bexists i).denotation (by simp_all) I := by
  repeat (rw [bexists_denotation (hi := hi)]; simp_all)

lemma bexists_comm {B : BDD} {i j : Fin B.nvars} {I : Vector Bool n} {h} :
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

abbrev majority3 :=
    (or (or (and (var 0) (var 1)) (and (var 0) (var 2))) (and (var 1) (var 2)))

-- abbrev majority3' :=
--     (and (imp (var 0) (or (var 1) (var 2))) (imp (var 0).not (and (var 1) (var 2))))

-- example : Nary.DependsOn (majority3.denotation') ⟨1, by simp⟩ := by
--   decide +native

-- example : ∀ b, ¬ Nary.DependsOn ((majority3.restrict b 1).denotation') ⟨1, by simp⟩ := by
--     decide +native
example : ¬ majority3.SemanticEquiv (const true) := by decide +native
end BDD

--#eval! BDD.majority3.find.bind (fun I ↦ some I.toList)
--#eval! BDD.instDecidableSemacticEquiv BDD.majority3 BDD.majority3'
-- #eval (BDD.const true).robdd.1
--#eval! (BDD.var 3).not.obdd
--#eval! (BDD.apply    (fun b b' ↦ (! b) || b') (BDD.var 3)      (BDD.const false)     ).obdd
--#eval! (Reduce.oreduce (Lift.olift (show (max (BDD.const false).nvars (BDD.var 2).nvars) ≤ (max (BDD.const false).nvars (BDD.var 2).nvars) + 1 by simp) ((Apply.oapply (Bool.and) (BDD.const false).obdd (BDD.var 2).obdd).2))).2
--#eval! (Reduce.oreduce (Apply.oapply (fun b b' ↦ (! b) || b') (BDD.var 3).obdd (BDD.const false).obdd).2).2
--#eval! (Apply.oapply (fun b b' ↦ (! b) || b') (BDD.var 3).obdd (BDD.const false).obdd).2
--#eval! (Reduce.oreduce (BDD.and ((BDD.and (BDD.var 0) (BDD.var 2)).restrict false 0) ((BDD.and (BDD.var 0) (BDD.var 2)).restrict true 0)).obdd).2
--#eval! ((BDD.or (BDD.and (BDD.var 0) (BDD.var 1)) (BDD.or (BDD.and (BDD.var 0) (BDD.var 2)) (BDD.and (BDD.var 1) (BDD.var 2)))).bforall ⟨1, by simp⟩).robdd.1
--#eval! (((BDD.or (BDD.var 0) (BDD.or (BDD.and (BDD.var 0) (BDD.var 2)) (BDD.and (BDD.var 1) (BDD.var 2)))).bforall ⟨1, by simp⟩).bforall ⟨0, by simp⟩).robdd.1
--#eval! ((BDD.or (BDD.and (BDD.var 0) (BDD.var 1)) (BDD.or (BDD.and (BDD.var 0) (BDD.var 2)) (BDD.and (BDD.var 1) (BDD.var 2)))).restrict true 0).obdd
--#eval! ((BDD.var 1).not).obdd
--#eval! ((BDD.var 1)).obdd
--#eval! (BDD.or (BDD.and (BDD.var 0) (BDD.var 1)) (BDD.or (BDD.and (BDD.var 0) (BDD.var 2)) (BDD.and (BDD.var 1) (BDD.var 2)))).obdd
--#eval! ((BDD.and (BDD.and (BDD.var 1) (BDD.var 2).not) (BDD.and (BDD.var 3) (BDD.var 4).not)).restrict true ⟨1, by simp⟩).robdd.1
--#eval! ((BDD.and (BDD.and (BDD.var 1) (BDD.var 2).not) (BDD.and (BDD.var 3) (BDD.var 4).not)).restrict false ⟨1, by simp⟩).robdd.1
--#eval! ((BDD.and (BDD.and (BDD.var 1) (BDD.var 2).not) (BDD.and (BDD.var 3) (BDD.var 4).not)).restrict false ⟨2, by simp⟩).robdd.1
-- #eval! BDD.instDecidableSemacticEquiv ((BDD.var 2).or (BDD.var 2).not) ((BDD.var 5).imp (BDD.var 5))
--#eval! BDD.instDecidableSemacticEquiv ((BDD.var 2).or (BDD.var 2).not) (BDD.const true)
--#eval! decide (Nary.DependsOn (((BDD.var 2).or (BDD.var 2).not).denotation (le_refl ..)) ⟨2, by simp⟩)

--#lint
