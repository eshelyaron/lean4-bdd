import Bdd.Basic
import Bdd.Reduce
import Bdd.Apply
import Bdd.Compactify
import Bdd.Prime

-- TODO: this is similar to `OBdd.reachable_or_eq_low_high`
lemma Pointer.Reachable_iff {heap : Vector (Node n m) m } : Pointer.Reachable heap root p ↔ (p = root ∨ (∃ j, root = .node j ∧ (Pointer.Reachable heap heap[j].low p ∨ Pointer.Reachable heap heap[j].high p))) := by
  constructor
  · intro h
    cases Relation.reflTransGen_swap.mp h with
    | refl =>
      left
      rfl
    | tail r e =>
      rename_i q
      right
      cases e with
      | low  hh => rename_i j; exact ⟨j, rfl, .inl (by trans q; rw [hh]; left; exact (Relation.reflTransGen_swap.mpr r))⟩
      | high hh => rename_i j; exact ⟨j, rfl, .inr (by trans q; rw [hh]; left; exact (Relation.reflTransGen_swap.mpr r))⟩
  · intro h
    cases h with
    | inl h => rw [h]; left
    | inr h =>
      rcases h with ⟨j, hj, h⟩
      rw [hj]
      cases h with
      | inl h =>
        apply Relation.reflTransGen_swap.mp
        right
        · apply Relation.reflTransGen_swap.mpr; exact h
        · left; rfl
      | inr h =>
        apply Relation.reflTransGen_swap.mp
        right
        · apply Relation.reflTransGen_swap.mpr; exact h
        · right; rfl

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
          simp_rw [hh, hhh]
        | inr hhh =>
          rcases hhh with ⟨j, hj, hhh⟩
          simp only at hj
          injection hj with hj
          simp only at hhh
          rw [← hj] at hhh
          simp at hhh
          rcases hhh with hhh | hhh <;>
          apply Pointer.eq_terminal_of_reachable at hhh <;>
          simp_rw [hh, hhh] at hxy <;>
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
          simp_rw [hh, hhh] at hxy <;>
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
    independentOf (B.denotation h1) i := by
  rintro b I
  simp only [denotation, OBdd.lift_evaluate]
  suffices s : (I.set i b).take B.nvars = I.take B.nvars by rw [s]
  ext j hj
  rw [Vector.getElem_take]
  rw [Vector.getElem_take]
  rw [Vector.getElem_set_ne]
  omega

lemma const_nvars : (const b).nvars = 0 := rfl

lemma const_denotation : (const b).denotation h = Function.const _ b := by
  simp only [denotation, const, ROBdd.const]
  apply OBdd.evaluate_terminal'
  rw [OBdd.lift_preserves_root]

lemma var_nvars : (var i).nvars = i + 1 := rfl

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

lemma apply_spec {B C : BDD} {op} {I : Vector Bool (apply op B C).nvars} :
    (apply op B C).denotation (Nat.le_refl _) I =
    (op (B.denotation (Nat.le_max_left ..) (apply_nvars ▸ I)) (C.denotation (Nat.le_max_right ..) (apply_nvars ▸ I))) := by
  rw [apply_cast_nvars]
  convert apply_spec'
  · exact symm apply_nvars
  · exact apply_nvars
  · simp_all only [heq_eqRec_iff_heq, heq_eq_eq]

lemma and_nvars {B C : BDD} : (B.and C).nvars = B.nvars ⊔ C.nvars := apply_nvars

lemma and_spec {B C : BDD} {I : Vector Bool (B.and C).nvars} :
    (B.and C).denotation (Nat.le_refl _) I =
    ((B.denotation (Nat.le_max_left  ..) (and_nvars ▸ I)) &&
     (C.denotation (Nat.le_max_right ..) (and_nvars ▸ I))) := apply_spec

lemma or_spec {B C : BDD} {I : Vector Bool (B.or C).nvars} :
    (B.or C).denotation (Nat.le_refl _) I =
    ((B.denotation (Nat.le_max_left  ..) (apply_nvars ▸ I)) ||
     (C.denotation (Nat.le_max_right ..) (apply_nvars ▸ I))) := apply_spec

lemma imp_spec {B C : BDD} {I : Vector Bool (B.imp C).nvars} :
    (B.imp C).denotation (Nat.le_refl _) I =
    (!(B.denotation (Nat.le_max_left  ..) (apply_nvars ▸ I)) ||
      (C.denotation (Nat.le_max_right ..) (apply_nvars ▸ I))) := by
  simp only [imp, apply_spec]

lemma not_nvars {B : BDD} : B.not.nvars = B.nvars := by
  simp only [not, imp, apply_nvars, const_nvars, zero_le, sup_of_le_left]

lemma not_spec {B : BDD} {I : Vector Bool B.not.nvars} :
    B.not.denotation (Nat.le_refl _) I = ! B.denotation (Nat.le_refl ..) (not_nvars ▸ I) := by
  simp only [not, imp_spec, const_nvars, const_denotation, Function.const_apply, Bool.or_false]
  congr!
  simp [zero_le, sup_of_le_left]

def relabel (B : BDD) (f : Nat → Nat)
    (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
    (h2 : ∀ i i' : Fin B.nvars, i < i' → dependsOn (B.denotation (le_refl ..)) i → dependsOn (B.denotation (le_refl ..)) i' → f i < f i') :
    BDD :=
  ⟨f B.nvars, B.nheap,
  ⟨Prime.orelabel B.robdd.1 h1 (by
    intro i i' hii' hi hi'
    rw [OBdd.usesVar_iff_dependsOn_of_reduced B.robdd.2] at hi
    rw [OBdd.usesVar_iff_dependsOn_of_reduced B.robdd.2] at hi'
    simp only [denotation, OBdd.lift_trivial_eq] at h2
    exact h2 i i' hii' hi hi'),
   Prime.orelabel_reduced B.robdd.2⟩⟩

lemma relabel_nvars {B : BDD} {f : Nat → Nat} {hf} {hu} : (relabel B f hf hu).nvars = f B.nvars := rfl

lemma relabel_spec {B : BDD} {f : Nat → Nat} {hf} {hu}  {I : Vector Bool (relabel B f hf hu).nvars} :
    (relabel B f hf hu).denotation (le_refl ..) I = B.denotation (le_refl ..) (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp only [denotation, relabel, OBdd.lift_evaluate, Prime.orelabel_evaluate]
  simp

def prime : Nat → BDD → BDD
  | p, B => ⟨B.nvars + p, B.nheap, ⟨Prime.oprime p B.robdd.1, Prime.oprime_reduced B.robdd.2⟩⟩

lemma prime_nvars {B : BDD} : (B.prime p).nvars = B.nvars + p := rfl

lemma prime_spec {B : BDD} {I : Vector Bool (B.prime p).nvars} :
    (B.prime p).denotation (Nat.le_refl _) I = B.denotation (Nat.le_refl ..) (Vector.cast (Eq.symm (Nat.eq_sub_of_add_eq rfl)) (I.drop p)) := by
  simp only [denotation, prime, OBdd.lift_evaluate, Prime.oprime_evaluate]
  simp

def unprime (B : BDD) (p : Fin B.nvars) (h : ∀ i : Fin p, independentOf (B.denotation (Nat.le_refl ..)) ⟨i.1, by omega⟩) : BDD :=
  ⟨B.nvars - p, B.nheap,
    ⟨Prime.ounprime p B.robdd.1 (by apply OBdd.reduced_var_dependent (B.robdd.2); simp only [denotation] at h; simp_all [OBdd.lift_trivial_eq]),
     Prime.ounprime_reduced B.robdd.2⟩⟩

lemma unprime_nvars {B : BDD} {p} {h} : (unprime B p h).nvars = B.nvars - p := rfl

lemma unprime_spec {B : BDD} {p} {h} {I : Vector Bool (unprime B p h).nvars} {J : Vector Bool p} :
    (unprime B p h).denotation (Nat.le_refl _) I = B.denotation (Nat.le_refl ..) (Vector.cast (by rw [unprime_nvars]; omega) (J ++ I)) := by
  simp only [denotation, unprime, OBdd.lift_evaluate, Vector.take_eq_extract, Vector.extract_size, Nat.sub_zero, Vector.cast_cast, Vector.cast_rfl]
  rw [Prime.ounprime_evaluate]

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

end BDD

-- #eval (BDD.const true).robdd.1
-- #eval! (BDD.var 3).robdd.1
-- #eval! (BDD.var 3).not.robdd.1
-- #eval! (BDD.and (BDD.var 3) (BDD.var 4).not).robdd.1
-- #eval! BDD.instDecidableSemacticEquiv ((BDD.var 2).or (BDD.var 2).not) ((BDD.var 5).imp (BDD.var 5))
-- #eval! BDD.instDecidableSemacticEquiv ((BDD.var 2).or (BDD.var 2).not) (BDD.const true)
