import Bdd.Basic
import Bdd.Reduce
import Bdd.Apply
import Bdd.Compactify
import Bdd.Relabel
import Bdd.Nary
import Bdd.Choice

lemma Pointer.eq_terminal_of_reachable : Pointer.Reachable w (.terminal b) p → p = (.terminal b) := by
  intro h
  cases Relation.reflTransGen_swap.mp h with
  | refl => rfl
  | tail => contradiction

def ROBdd n m := { O : OBdd n m // O.Reduced }

structure BDD where
  nvars : Nat
  private nheap : Nat
  private robdd : ROBdd nvars nheap

namespace ROBdd

def const : Bool → ROBdd 0 0 := fun b ↦
  ⟨⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩, OBdd.reduced_of_terminal ⟨b, rfl⟩⟩

def var (n : Nat) : ROBdd n.succ 1 :=
  ⟨⟨⟨Vector.singleton ⟨n, .terminal false, .terminal true⟩, .node 0⟩,
  by
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
  ⟩,
  by
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
  ⟩

end ROBdd

open Compactify
open Reduce

namespace BDD

private def zero_vars_to_bool (B : BDD) : B.nvars = 0 → Bool := fun h ↦
  match B.robdd.1.1.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ (Eq.subst h B.robdd.1.1.heap[j].var.2))

private lemma zero_vars_to_bool_spec {B : BDD} (h : B.nvars = 0) : B.robdd.1.1.root = .terminal (B.zero_vars_to_bool h) := by
  simp only [zero_vars_to_bool]
  split
  next => assumption
  next => contradiction

def const : Bool → BDD := fun b ↦ ⟨_, _, ROBdd.const b⟩
def var   : Nat  → BDD := fun n ↦ ⟨_, _, ROBdd.var n⟩

def apply : (Bool → Bool → Bool) → BDD → BDD → BDD := fun op B C ↦
  match h : max B.nvars C.nvars with
  | .zero   => const (op (zero_vars_to_bool B (Nat.max_eq_zero_iff.mp h).1) (zero_vars_to_bool C (Nat.max_eq_zero_iff.mp h).2))
  | .succ _ => ⟨_, _, ⟨⟨compactify' (reduce' (Apply.apply' (by simpa) op B.robdd.1 C.robdd.1)), compactify_ordered⟩, compactify_preserves_reduced reduce'_spec.1⟩⟩

private lemma apply_induction {B C : BDD} {op : Bool → Bool → Bool} {motive : BDD → Prop} :
  (base : (h : B.nvars ⊔ C.nvars = 0) → motive (const (op (zero_vars_to_bool B (Nat.max_eq_zero_iff.mp h).1) (zero_vars_to_bool C (Nat.max_eq_zero_iff.mp h).2)))) →
  (step : ∀ p : Nat, (h : B.nvars ⊔ C.nvars = p.succ) → motive ⟨_, _, ⟨⟨compactify' (reduce' (Apply.apply' (by simpa) op B.robdd.1 C.robdd.1)), compactify_ordered⟩, compactify_preserves_reduced reduce'_spec.1⟩⟩) →
  motive (apply op B C) := by
  intro base step
  simp only [apply]
  split
  next heq => exact base heq
  next p heq => exact step p heq

@[simp]
lemma apply_nvars {B C : BDD} {o} : (apply o B C).nvars = B.nvars ⊔ C.nvars := by
  simp only [apply]
  split
  next heq => simp only [const]; rw [heq]
  next n heq => simp

def and : BDD → BDD → BDD := apply Bool.and
def or  : BDD → BDD → BDD := apply Bool.or
def imp : BDD → BDD → BDD := apply (! · || ·)
def not : BDD → BDD       := fun B ↦ imp B (const false)

def denotation (B : BDD) {n : Nat} (h : B.nvars ≤ n) : Vector Bool n → Bool := (B.robdd.1.lift h).evaluate

lemma nvars_spec {n : Nat} {i : Fin n} {B : BDD} {h1 : B.nvars ≤ n} {h2 : B.nvars ≤ i} :
    Nary.IndependentOf (B.denotation h1) i := by
  rintro b I
  simp only [denotation, OBdd.lift_evaluate]
  suffices s : (I.set i b).take B.nvars = I.take B.nvars by rw [s]
  ext j hj
  rw [Vector.getElem_take]
  rw [Vector.getElem_take]
  rw [Vector.getElem_set_ne]
  omega

@[simp]
lemma const_nvars : (const b).nvars = 0 := rfl

@[simp]
lemma const_denotation : (const b).denotation h = Function.const _ b := by
  simp only [denotation, const, ROBdd.const]
  apply OBdd.evaluate_terminal'
  rw [OBdd.lift_preserves_root]

@[simp]
lemma var_nvars : (var i).nvars = i + 1 := rfl

@[simp]
lemma var_denotation : (var i).denotation h I = I[i] := by
  simp only [denotation, var, ROBdd.var, OBdd.lift_evaluate]
  rw [OBdd.evaluate_node]
  simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.isValue, Fin.getElem_fin,
    Fin.val_eq_zero, List.Vector.getElem_def, List.Vector.toList_singleton, List.Vector.head,
    List.getElem_cons_zero, Fin.val_last, Bdd.Ordered.eq_1, OBdd.evaluate_terminal,
    Function.const_apply, Bool.if_false_right, Bool.decide_eq_true, Bool.and_true]
  simp only [Vector.singleton_def, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, Fin.val_last, OBdd.evaluate_terminal, Function.const_apply,
    Bool.if_false_right, Bool.decide_eq_true, Bool.and_true]
  rename_i n
  rw [var_nvars] at h
  have : (I.take (i + 1))[i] = I[i] := by
    apply Vector.getElem_take
  rw [← this]
  rfl

private lemma apply_spec' {B C : BDD} {op} {I : Vector Bool (B.nvars ⊔ C.nvars)} :
    (apply op B C).denotation (Nat.le_refl _) (apply_nvars ▸ I) =
    (op (B.denotation (Nat.le_max_left ..) I) (C.denotation (Nat.le_max_right ..) I)) := by
  let motive : BDD → Prop :=
    fun D ↦
      ∀ (h : D.nvars = B.nvars ⊔ C.nvars),
        D.denotation (Nat.le_refl _) (h ▸ I) =
        (op (B.denotation (Nat.le_max_left ..) I) (C.denotation (Nat.le_max_right ..) I))
  apply apply_induction (motive := motive) (op := op) (B := B) (C := C)
  · intro heq h
    rw [const_denotation]
    simp only [Function.const_apply]
    have B_root_def := zero_vars_to_bool_spec (B := B) (by omega)
    have C_root_def := zero_vars_to_bool_spec (B := C) (by omega)
    simp [denotation, OBdd.lift_evaluate, OBdd.evaluate_terminal' B_root_def, OBdd.evaluate_terminal' C_root_def]
  · intro p heq h
    conv =>
      lhs
      unfold denotation
    simp only
    rw [OBdd.lift_trivial_eq (h := h)]
    simp only [OBdd.evaluate_cast h]
    rw [compactify_evaluate]
    simp_rw [← reduce'_spec.2]
    rw [← Apply.apply'_spec]
    congr
  · exact apply_nvars

private lemma apply_cast_nvars {B C : BDD} {op} {I : Vector Bool (apply op B C).nvars} :
    (apply op B C).denotation (Nat.le_refl _) I =
    ((apply op B C).denotation (n := B.nvars ⊔ C.nvars) (by rw [apply_nvars]) (apply_nvars ▸ I) ) := by
  simp only [denotation]
  simp only [OBdd.lift_evaluate]
  congr!
  · exact apply_nvars
  · exact HEq.symm (eqRec_heq apply_nvars I)

@[simp]
lemma apply_spec {B C : BDD} {op} {I : Vector Bool (apply op B C).nvars} :
    (apply op B C).denotation (Nat.le_refl _) I =
    (op (B.denotation (Nat.le_max_left ..) (apply_nvars ▸ I)) (C.denotation (Nat.le_max_right ..) (apply_nvars ▸ I))) := by
  rw [apply_cast_nvars]
  convert apply_spec'
  · exact symm apply_nvars
  · exact apply_nvars
  · simp_all only [heq_eqRec_iff_heq, heq_eq_eq]

@[simp]
lemma and_nvars {B C : BDD} : (B.and C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
lemma and_spec {B C : BDD} {I : Vector Bool (B.and C).nvars} :
    (B.and C).denotation (Nat.le_refl _) I =
    ((B.denotation (Nat.le_max_left  ..) (and_nvars ▸ I)) &&
     (C.denotation (Nat.le_max_right ..) (and_nvars ▸ I))) := apply_spec

@[simp]
lemma or_nvars {B C : BDD} : (B.or C).nvars = B.nvars ⊔ C.nvars := apply_nvars

@[simp]
lemma or_spec {B C : BDD} {I : Vector Bool (B.or C).nvars} :
    (B.or C).denotation (Nat.le_refl _) I =
    ((B.denotation (Nat.le_max_left  ..) (apply_nvars ▸ I)) ||
     (C.denotation (Nat.le_max_right ..) (apply_nvars ▸ I))) := apply_spec

@[simp]
lemma imp_spec {B C : BDD} {I : Vector Bool (B.imp C).nvars} :
    (B.imp C).denotation (Nat.le_refl _) I =
    (!(B.denotation (Nat.le_max_left  ..) (apply_nvars ▸ I)) ||
      (C.denotation (Nat.le_max_right ..) (apply_nvars ▸ I))) := by
  simp only [imp, apply_spec]

@[simp]
lemma not_nvars {B : BDD} : B.not.nvars = B.nvars := by
  simp only [not, imp, apply_nvars, const_nvars, zero_le, sup_of_le_left]

@[simp]
lemma not_spec {B : BDD} {I : Vector Bool B.not.nvars} :
    B.not.denotation (Nat.le_refl _) I = ! B.denotation (Nat.le_refl ..) (not_nvars ▸ I) := by
  simp only [not, imp_spec, const_nvars, const_denotation, Function.const_apply, Bool.or_false]
  congr!
  simp [zero_le, sup_of_le_left]

def relabel (B : BDD) (f : Nat → Nat)
    (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
    (h2 : ∀ i i' : Fin B.nvars, i < i' → Nary.DependsOn (B.denotation (le_refl ..)) i → Nary.DependsOn (B.denotation (le_refl ..)) i' → f i < f i') :
    BDD :=
  ⟨f B.nvars, B.nheap,
  ⟨Relabel.orelabel B.robdd.1 h1 (by
    intro i i' hii' hi hi'
    rw [OBdd.usesVar_iff_dependsOn_of_reduced B.robdd.2] at hi
    rw [OBdd.usesVar_iff_dependsOn_of_reduced B.robdd.2] at hi'
    simp only [denotation, OBdd.lift_trivial_eq] at h2
    exact h2 i i' hii' hi hi'),
   Relabel.orelabel_reduced B.robdd.2⟩⟩

@[simp]
lemma relabel_id {B : BDD} : B.relabel id (by simp) (fun _ _ _ _ _ ↦ by simpa) = B := by simp [relabel]

@[simp]
lemma relabel_nvars {B : BDD} {f : Nat → Nat} {hf} {hu} : (relabel B f hf hu).nvars = f B.nvars := rfl

@[simp]
lemma relabel_spec {B : BDD} {f : Nat → Nat} {hf} {hu}  {I : Vector Bool (relabel B f hf hu).nvars} :
    (relabel B f hf hu).denotation (le_refl ..) I = B.denotation (le_refl ..) (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp [denotation, relabel]

def SemanticEquiv : BDD → BDD → Prop := fun B C ↦
  B.denotation (Nat.le_max_left  ..) = C.denotation (Nat.le_max_right ..)

private def SyntacticEquiv : BDD → BDD → Prop := fun B C ↦
  (B.robdd.1.lift (Nat.le_max_left B.nvars C.nvars)).HSimilar (C.robdd.1.lift (Nat.le_max_right B.nvars C.nvars))

private instance instDecidableSyntacticEquiv : DecidableRel SyntacticEquiv
  | _, _ => OBdd.instDecidableHSimilar _ _

private theorem SemanticEquiv_iff_SyntacticEquiv {B C : BDD} :
    B.SemanticEquiv C ↔ B.SyntacticEquiv C := by
  constructor
  · intro h
    exact (OBdd.HCanonicity (OBdd.Reduced_of_lift B.robdd.2) (OBdd.Reduced_of_lift C.robdd.2) h)
  · intro h
    exact (OBdd.Canonicity_reverse (OBdd.Reduced_of_lift B.robdd.2) (OBdd.Reduced_of_lift C.robdd.2) h)

instance instDecidableSemacticEquiv : DecidableRel SemanticEquiv
  | _, _ => decidable_of_iff' _ SemanticEquiv_iff_SyntacticEquiv

def choice {B : BDD} (s : ∃ I, B.denotation (le_refl ..) I) : Vector Bool B.nvars := Choice.choice B.robdd.1 (by simp_all [denotation])

@[simp]
lemma choice_spec {B : BDD} {s : ∃ I, B.denotation (le_refl ..) I} : B.denotation (le_refl ..) (B.choice s) = true := by
  simp [choice, denotation, Choice.choice_spec B.robdd.2 (by simp_all [denotation])]

private lemma find_aux {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool (max B.nvars 0)), B.denotation (by simp) I := by
  intro h
  contrapose h
  simp_all only [not_exists, Bool.not_eq_true, SemanticEquiv, const_nvars, const_denotation, not_not]
  ext x
  simp only [Function.const_apply]
  apply h

private lemma find_aux' {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool B.nvars), B.denotation (by simp) I := by
  intro h
  rcases find_aux h with ⟨I, hI⟩
  use ((show (max B.nvars 0) = B.nvars by simp) ▸ I)
  rw [← hI]
  clear hI
  congr! <;> simp

def find {B : BDD} : Option (Vector Bool B.nvars) :=
  match instDecidableSemacticEquiv B (const false) with
  | isTrue _ => none
  | isFalse hf => some (choice (find_aux' hf))

def find_none {B : BDD} : B.find.isNone → B.SemanticEquiv (const false) := by
  intro h
  simp only [find] at h
  split at h
  next ht _ => exact ht
  next hf _ => contradiction

def find_some {B : BDD} {I : Vector Bool B.nvars} : B.find = some I → B.denotation (le_refl ..) I = true := by
  intro h
  simp only [find] at h
  split at h
  next ht _ => contradiction
  next hf _ => injection h with heq; simp [← heq]

instance instDecidableDependsOn (B : BDD) : DecidablePred (Nary.DependsOn (B.denotation (le_refl ..))) := by
  suffices s : Nary.DependsOn (B.denotation (le_refl ..)) = B.robdd.1.1.usesVar by rw [s]; infer_instance
  simp [denotation]
  ext i
  exact Iff.symm (OBdd.usesVar_iff_dependsOn_of_reduced B.robdd.2)

end BDD

-- #eval (BDD.const true).robdd.1
-- #eval! (BDD.var 3).robdd.1
-- #eval! (BDD.var 3).not.robdd.1
-- #eval! (BDD.and (BDD.and (BDD.var 1) (BDD.var 2).not) (BDD.and (BDD.var 3) (BDD.var 4).not)).find
-- #eval! BDD.instDecidableSemacticEquiv ((BDD.var 2).or (BDD.var 2).not) ((BDD.var 5).imp (BDD.var 5))
--#eval! BDD.instDecidableSemacticEquiv ((BDD.var 2).or (BDD.var 2).not) (BDD.const true)
-- #eval! decide (dependsOn (((BDD.var 2).not.or (BDD.var 2).not).denotation (le_refl ..)) ⟨2, by simp⟩)
