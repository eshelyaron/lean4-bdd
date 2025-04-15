-- This module serves as the root of the `Bdd` library.
-- Import modules here that should be built as part of the library.
import Bdd.Basic
import Bdd.Reduce
import Bdd.Apply
import Bdd.Compactify
open List renaming Vector → Vec

-- TODO: this is similar to `OBdd.reachable_or_eq_low_high`
lemma Pointer.Reachable_iff {heap : Vec (Node n m) m } : Pointer.Reachable heap root p ↔ (p = root ∨ (∃ j, root = .node j ∧ (Pointer.Reachable heap heap[j].low p ∨ Pointer.Reachable heap heap[j].high p))) := by
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
  nheap : Nat
  robdd : ROBdd nvars nheap

namespace ROBdd

def const : Bool → ROBdd 0 0 := fun b ↦
  ⟨⟨⟨⟨[], rfl⟩, .terminal b⟩, Bdd.Ordered_of_terminal⟩, OBdd.reduced_of_terminal ⟨b, rfl⟩⟩

def var (n : Nat) : ROBdd n.succ 1 :=
  ⟨⟨⟨⟨[⟨n, .terminal false, .terminal true⟩], rfl⟩, .node 0⟩,
  (Ordered_of_Proper (fun N h ↦
    by
      simp only [Vec.instMembership, Function.comp_apply, List.Vector.toList_singleton, List.Vector.head, List.mem_cons, List.not_mem_nil, or_false] at h
      rw [h]
      intro j hj
      simp only [reduceCtorEq, or_self] at hj))⟩,
  ⟨NoRedundancy_of_RProper (fun N h ↦
    by
      simp only [Vec.instMembership, Function.comp_apply, List.Vector.toList_singleton, List.Vector.head, List.mem_cons, List.not_mem_nil, or_false] at h
      rw [h]
      simp),
    by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      cases Pointer.Reachable_iff.mp hx with
      | inl hh =>
        simp only at hh
        cases Pointer.Reachable_iff.mp hy with
        | inl hhh =>
          simp only at hhh
          simp_rw [hh, hhh]
          simp [InvImage]
        | inr hhh =>
          rcases hhh with ⟨j, hj, hhh⟩
          simp only at hj
          injection hj
          rcases hhh with hhh | hhh <;>
          simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.getElem_fin, Fin.val_eq_zero, Vec.getElem_def, List.Vector.toList_singleton, List.Vector.head, List.getElem_cons_zero] at hhh <;>
          apply Pointer.eq_terminal_of_reachable at hhh <;>
          simp_rw [hh, hhh] at h <;>
          simp only [OBdd.GraphSimilar, OBdd.Similar, InvImage] at h <;>
          unfold OBdd.toTree at h <;>
          simp at h
      | inr hh =>
        simp only at hh
        rcases hh with ⟨j, hj, hh⟩
        injection hj
        simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.getElem_fin, Fin.val_eq_zero, Vec.getElem_def, List.Vector.toList_singleton, List.Vector.head, List.getElem_cons_zero] at hh
        cases Pointer.Reachable_iff.mp hy with
        | inl hhh =>
          simp only at hhh
          rcases hh with hh | hh <;>
          apply Pointer.eq_terminal_of_reachable at hh <;>
          simp_rw [hh, hhh] at h <;>
          simp only [OBdd.GraphSimilar, OBdd.Similar, InvImage] at h <;>
          unfold OBdd.toTree at h <;>
          simp at h
        | inr hhh =>
          simp only at hhh
          rcases hhh with ⟨i, hi, hhh⟩
          injection hi
          simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.getElem_fin, Fin.val_eq_zero, Vec.getElem_def, List.Vector.toList_singleton, List.Vector.head, List.getElem_cons_zero] at hhh
          cases hh with
          | inl hh =>
            cases hhh with
            | inl hhh =>
              apply Pointer.eq_terminal_of_reachable at hh
              apply Pointer.eq_terminal_of_reachable at hhh
              simp [InvImage]
              rw [hh, hhh]
            | inr hhh =>
              apply Pointer.eq_terminal_of_reachable at hh
              apply Pointer.eq_terminal_of_reachable at hhh
              simp_rw [hh, hhh] at h
              simp only [OBdd.GraphSimilar, OBdd.Similar, InvImage] at h
              unfold OBdd.toTree at h
              simp at h
          | inr hh =>
            cases hhh with
            | inl hhh =>
              apply Pointer.eq_terminal_of_reachable at hh
              apply Pointer.eq_terminal_of_reachable at hhh
              simp_rw [hh, hhh] at h
              simp only [OBdd.GraphSimilar, OBdd.Similar, InvImage] at h
              unfold OBdd.toTree at h
              simp at h
            | inr hhh =>
              apply Pointer.eq_terminal_of_reachable at hh
              apply Pointer.eq_terminal_of_reachable at hhh
              simp [InvImage]
              rw [hh, hhh]
          ⟩⟩

end ROBdd

open Compactify
open Reduce
namespace BDD

def zero_vars_to_bool (B : BDD) : B.nvars = 0 → Bool := fun h ↦
  match B.robdd.1.1.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ (Eq.subst h B.robdd.1.1.heap[j].var.2))

def const : Bool → BDD := fun b ↦ ⟨_, _, ROBdd.const b⟩
def var   : Nat  → BDD := fun n ↦ ⟨_, _, ROBdd.var n⟩

def apply : (Bool → Bool → Bool) → BDD → BDD → BDD := fun op B C ↦
  match h : max B.nvars C.nvars with
  | .zero   => const (op (zero_vars_to_bool B (Nat.max_eq_zero_iff.mp h).1) (zero_vars_to_bool C (Nat.max_eq_zero_iff.mp h).2))
  | .succ _ => ⟨_, _, ⟨⟨compactify' (reduce' (Apply.apply' (by simpa) op B.robdd.1 C.robdd.1)), compactify_ordered⟩, compactify_preserves_reduced reduce'_spec.1⟩⟩

def and : BDD → BDD → BDD := apply Bool.and
def or  : BDD → BDD → BDD := apply Bool.or
def imp : BDD → BDD → BDD := apply (¬ · ∨ ·)
def not : BDD → BDD       := fun B ↦ imp B (const false)

end BDD

#eval (BDD.const true).robdd.1
#eval! (BDD.var 3).robdd.1
#eval! (BDD.var 3).not.robdd.1
#eval! (BDD.and (BDD.var 3) (BDD.var 4).not).robdd.1
