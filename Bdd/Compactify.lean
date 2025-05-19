import Bdd.Basic
import Bdd.Size

open Pointer

namespace Compactify

def compactify_helper {n m : Nat} (O : OBdd n m) (S : O.SubBdd) (ids : Vector (Option (Fin (Size.size O))) m) (nid : Fin (Size.size O)) (new : Vector (Node n (Size.size O)) (Size.size O)) : Vector (Option (Fin (Size.size O))) m × Fin (Size.size O) × Vector (Node n (Size.size O)) (Size.size O) × Pointer (Size.size O) :=
  match S_root_def : S.1.1.root with
    | terminal b => ⟨ ids, nid, new, terminal b ⟩
    | node j =>
      match ids.get j with
      | none =>
        let ⟨ ids1, nid1, new1, l ⟩ := compactify_helper O (S.low  S_root_def) ids  nid  new
        let ⟨ ids2, nid2, new2, h ⟩ := compactify_helper O (S.high S_root_def) ids1 nid1 new1
        have : NeZero (Size.size O) := Size.instNeZeroSize S S_root_def
        ⟨ ids2.set j (some nid2), nid2 + 1, new2.set nid2 ⟨O.1.heap[j].var, l, h⟩, node nid2 ⟩
      | some j' => ⟨ ids, nid, new, node j' ⟩
termination_by S.1

def compactify' {n m : Nat} (O : OBdd n m) : Bdd n (Size.size O) :=
  match O_root_def : O.1.root with
  | terminal b =>
    have := Size.isTerminal_iff_size_eq_zero.mpr ⟨b, O_root_def⟩
    ⟨this ▸ Vector.emptyWithCapacity 0, terminal (Size.bool_of_size_eq_zero O this)⟩
  | node j =>
    let ⟨ ids, nid, new, r ⟩ := compactify_helper O O.toSubBdd (Vector.replicate m none) ⟨0, Size.size_gt_zero_of_Sub_root_eq_node (O.toSubBdd) O_root_def⟩ (Vector.replicate (Size.size O) ⟨O.1.heap[j].var, (terminal false), (terminal false)⟩)
    ⟨new, r⟩

lemma compactify_helper_spec'
    (O : OBdd n m) (S : O.SubBdd)
    (ids : Vector (Option (Fin (Size.size O))) m)
    (nid : Fin (Size.size O))
    (new : Vector (Node n (Size.size O)) (Size.size O)) :
    nid = Fintype.card {j // (ids.get j).isSome} →
    ( ∀ j j',
      ids.get j = some j' →
      ∃ (r : Reachable O.1.heap O.1.root (node j)) (o : Bdd.Ordered ⟨new, node j'⟩),
        OBdd.HSimilar ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_reachable r⟩ ⟨⟨new, node j'⟩, o⟩
    ) →
    let ⟨ ids1, nid1, new1, root ⟩ := compactify_helper O S ids nid new
    nid1 = Fintype.card {j // (ids1.get j).isSome} ∧
    (∀ j j',
     ids1.get j = some j' →
     ∃ (r : Reachable O.1.heap O.1.root (node j)) (o : Bdd.Ordered ⟨new1, node j'⟩),
        OBdd.HSimilar ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_reachable r⟩ ⟨⟨new1, node j'⟩, o⟩
      ) ∧ ∃ (o : Bdd.Ordered ⟨new1, root⟩), OBdd.HSimilar S.1 ⟨⟨new1, root⟩, o⟩ := by
  intro h1 h2
  split
  next ids1 nid1 new1 root heq =>
    unfold compactify_helper at heq
    split at heq
    next b heqq =>
      simp_all only [Prod.mk.injEq, true_and, implies_true]
      simp_rw [← heq.2.2.2]
      exact ⟨Bdd.Ordered_of_terminal, OBdd.HSimilar_of_terminal heqq rfl⟩
    next j heqq =>
      split at heq
      next heqqq =>
        split at heq
        next idsl nidl newl rootl heql =>
          split at heq
          next idsr nidr newr rootr heqr =>
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨heq1, heq2, heq3, heq4⟩
            constructor
            · rw [← heq2]
              sorry
            · sorry
      next j' heqqq =>
        simp_all only [Prod.mk.injEq, true_and, implies_true]
        simp_rw [← heq.2.2.2]
        convert (h2 j j' heqqq).2
        simp_rw [← heqq]
        rcases S with ⟨U, o⟩
        simp only at heqq
        simp only
        have : O.1.heap = U.1.heap := sorry --use o
        simp_rw [this]
        rfl

lemma compactify_ordered {n m : Nat} {O : OBdd n m} : (compactify' O).Ordered := by
  unfold compactify'
  split
  next b heq => apply Bdd.Ordered_of_terminal
  next j heq =>
    split
    next x ids nid new root heqq => sorry

lemma compactify_preserves_reduced {O : OBdd n m} :
    OBdd.Reduced O → OBdd.Reduced ⟨(compactify' O), compactify_ordered⟩ := by
  sorry

lemma compactify_evaluate {O : OBdd n m} :
    OBdd.evaluate ⟨(compactify' O), compactify_ordered⟩ = O.evaluate := by
  sorry

end Compactify
