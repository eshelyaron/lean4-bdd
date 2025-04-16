import Bdd.Basic
open List renaming Vector → Vec

open Pointer

namespace Compactify

def compactify_helper {n m : Nat} (O : OBdd n m) (S : O.SubBdd) (ids : Vec (Option (Fin O.numPointers)) m) (nid : Fin O.numPointers) (new : Vec (Node n O.numPointers) O.numPointers) : Vec (Option (Fin O.numPointers)) m × Fin O.numPointers × Vec (Node n O.numPointers) O.numPointers × Pointer O.numPointers :=
  match S_root_def : S.1.1.root with
    | terminal b => ⟨ ids, nid, new, terminal b ⟩
    | node j =>
      match ids.get j with
      | none =>
        let ⟨ ids1, nid1, new1, l ⟩ := compactify_helper O (S.low  S_root_def) ids  nid  new
        let ⟨ ids2, nid2, new2, h ⟩ := compactify_helper O (S.high S_root_def) ids1 nid1 new1
        have : NeZero O.numPointers := OBdd.instNeZeroNumPointers S S_root_def
        ⟨ ids2.set j (some nid2), nid2 + 1, new2.set nid2 ⟨O.1.heap[j].var, l, h⟩, node nid2 ⟩
      | some j' => ⟨ ids, nid, new, node j' ⟩
termination_by S.1

def compactify' {n m : Nat} (O : OBdd n m) : Bdd n O.numPointers :=
  match O_root_def : O.1.root with
  | terminal b =>
    have := isTerminal_iff_numPointer_eq_zero.mpr ⟨b, O_root_def⟩
    ⟨this ▸ Vec.nil, terminal (Bool_of_numPointer_eq_zero O this)⟩
  | node j =>
    let ⟨ ids, nid, new, r ⟩ := compactify_helper O O.toSubBdd (Vec.replicate m none) ⟨0, OBdd.numPointers_gt_zero_of_Sub_root_eq_node (O.toSubBdd) O_root_def⟩ (Vec.replicate O.numPointers ⟨O.1.heap[j].var, (terminal false), (terminal false)⟩)
    ⟨new, r⟩

lemma compactify_helper_spec {n m : Nat}
    (O : OBdd n m) (S : O.SubBdd) (ids : Vec (Option (Fin O.numPointers)) m) (nid : Fin O.numPointers) (new : Vec (Node n O.numPointers) O.numPointers) (hp : Proper new):
    ( ∀ j j',
      ids.get j = some j' →
      ∃ (r : Reachable O.1.heap O.1.root (node j)),
        OBdd.HSimilar ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_relevant O ⟨node j, r⟩⟩ ⟨⟨new, node j'⟩, Ordered_of_Proper hp⟩
    ) →
    let ⟨ ids1, nid1, new1, root ⟩ := compactify_helper O S ids nid new
    ∃ (hp' : Proper new1),
      (∀ j j',
       ids1.get j = some j' →
       ∃ (r : Reachable O.1.heap O.1.root (node j)),
         OBdd.HSimilar ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_relevant O ⟨node j, r⟩⟩ ⟨⟨new1, node j'⟩, Ordered_of_Proper hp'⟩
      ) ∧ OBdd.HSimilar S.1 ⟨⟨new1, root⟩, Ordered_of_Proper hp'⟩ := by
  intro h
  unfold compactify_helper
  split
  next ids2 nid2 new2 root heq =>
    split at heq
    next b heqq =>
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨heq1, heq2, heq3, heq4⟩
      rw [← heq3, ← heq1, ← heq4]
      use hp
      constructor
      · exact h
      · exact OBdd.HSimilar_of_terminal heqq rfl
    next r heqq =>
      split at heq
      next heqqq =>
        split at heq
        next ids0 nid0 new0 lh heqqqq =>
          split at heq
          next ids1 nid1 new1 rh heqqqqq =>
          simp only [Prod.mk.injEq] at heq
          rcases heq with ⟨heq1, heq2, heq3, heq4⟩
          have hp2 : Proper new2 := by
            apply Proper_of_all_indices_RespectsOrder
            intro j
            nth_rw 2 [← heq3]
            cases decEq nid1 j with
            | isFalse hf =>
              rw [Vec.get_set_of_ne' hf]
              sorry
            | isTrue ht =>
              rw [ht, Vec.get_set_same']
              sorry
          sorry
      next j heqqq => sorry
  --     have hp' : Proper new1 := by
  --       sorry
  --     sorry
  -- next b heq =>
  --   constructor
  --   · constructor
  --     · exact h
  --     · exact OBdd.HSimilar_of_terminal heq rfl
  --   · simpa
  -- next j heq =>
  --   constructor
  --   case w =>
  --     split
  --     next heqq =>
  --       simp only
  --       apply Proper_of_all_indices_RespectsOrder
  --       intro i
  --       sorry
  --     next j' heqq => exact hp
  --   case h =>
  --     constructor
  --     · intro jj j' hjj'
  --       sorry
  --     · sorry
    -- · sorry
    -- · constructor
    --   · sorry
    --   · constructor
    --     case w =>
    --       split
    --       next heqq =>
    --         simp only
    --         apply Ordered_of_low_high_ordered
    --         · rw [Vec.get_set_same']
    --           simp only
    --           suffices Bdd.Ordered ⟨(compactify_helper O (S.low heq) ids nid new).2.2.1, (compactify_helper O (S.low heq) ids nid new).2.2.2⟩ by
    --             rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    --             simp only [RelevantEdge, Ordered] at hxy
    --             simp only [Ordered] at hx hy
    --             simp only [RelevantMayPrecede, MayPrecede]
    --             sorry
    --           rcases (compactify_helper_spec O (S.low heq) ids nid new h hp).2 with ⟨hhh, _⟩
    --           exact hhh
    --         · sorry
    --         · sorry
    --         · sorry
    --       next j' heqq =>
    --         exact (h j j' heqq).2.1
    --     case h => sorry
    -- split
    -- next heqq =>
    --   simp only
    --   sorry
    -- next j' heqq => exact h j j' heqq


lemma compactify_ordered {n m : Nat} {O : OBdd n m} : (compactify' O).Ordered := by
  unfold compactify'
  split
  next b heq => apply Bdd.Ordered_of_terminal
  next j heq =>
    split
    next x ids nid new root heqq => sorry

--theorem compactify_spec {n m : Nat} {O : OBdd n m} : O.Similar (compactify O) :=

lemma compactify_preserves_reduced {n m : Nat} {O : OBdd n m} :
    OBdd.Reduced O → OBdd.Reduced ⟨(compactify' O), compactify_ordered⟩ := by
  sorry

end Compactify
-- #eval (example_not_reduced_bdd).numPointers
-- #eval (example_bdd).numPointers

#eval example_bdd
#eval! Compactify.compactify' example_bdd
-- theorem compactify_induction {n m : Nat} {O : OBdd n m} {motive : Bdd n O.numPointers → Prop}
--     (one : (h : O.numPointers = 0) → motive ⟨h ▸ Vec.nil, terminal (Bool_of_numPointer_eq_zero O h)⟩)
--     (two : ∀ (k : Nat), O.numPointers = k.succ → motive (compactify O)) :
--     motive (compactify O) := by
--   cases h : O.numPointers with
--   | zero =>
--     convert one h
--     · unfold compactify
--       simp
--     rw [compactify.]
--   | succ k => sorry

-- def compactify {n m : Nat} (O : OBdd n m) : Bdd n O.numPointers :=
--   match h : O.numPointers with
--   | 0 => ⟨Vec.nil, terminal (Bool_of_numPointer_eq_zero O h)⟩
--   | Nat.succ k =>
--     let ⟨ ids, nid, new, r ⟩ := compactify_helper O O.toSubBdd (Vec.replicate m none) ⟨0, by linarith⟩ (Vec.replicate O.numPointers ⟨(O.1.heap.get ⟨0, lt_of_le_of_lt (show 0 ≤ k by linarith) sorry⟩).var, (terminal false), (terminal false)⟩)
--     h ▸ ⟨new, r⟩
