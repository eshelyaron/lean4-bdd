
import Bdd.Basic

namespace Collect

private def collect_helper (O : OBdd n m) : Vector Bool m × List (Fin m) → Vector Bool m × List (Fin m) :=
  match h : O.1.root with
  | .terminal _ => id
  | .node j =>
    fun I ↦ if I.1.get j then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩)
termination_by O

/-- Return a list of all reachable node indices. -/
def collect (O : OBdd n m) : List (Fin m) := (collect_helper O ⟨Vector.replicate m false, []⟩).2

private lemma collect_helper_terminal {v : Vector (Node n m) m} {h : Bdd.Ordered {heap := v, root := .terminal b}} :
    collect_helper ⟨{heap := v, root := .terminal b}, h⟩ I = I := by
  conv =>
    lhs
    unfold collect_helper
  congr

private lemma collect_helper_terminal' {O : OBdd n m} (h : O.1.root = .terminal b) :
    collect_helper O I = I := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only at h
  have := collect_helper_terminal (h := (show Bdd.Ordered {heap := M, root := .terminal b} by simp_rw [← h]; exact o)) (I := I)
  simp_rw [h]
  assumption

lemma collect_terminal {O : OBdd n m} (h : O.1.root = .terminal b) :
    collect O = [] := by
  simp only [collect, collect_helper_terminal' h]

private lemma collect_helper_node {v : Vector (Node n m) m} {h : Bdd.Ordered {heap := v, root := .node j}} :
    collect_helper ⟨{heap := v, root := .node j}, h⟩ I =
      if I.1[j]
      then I
      else collect_helper ⟨⟨v, v[j].high⟩, Bdd.ordered_of_relevant ⟨⟨v, .node j⟩, h⟩ ⟨v[j].high, Bdd.reachable_of_edge (Edge.high rfl)⟩⟩
                          (collect_helper ⟨{heap := v, root := v[j].low}, Bdd.ordered_of_relevant ⟨{heap := v, root := .node j}, h⟩ ⟨v[j].low, Bdd.reachable_of_edge (Edge.low rfl)⟩⟩
                                          ⟨I.1.set j true, j :: I.2⟩) := by
  conv =>
    lhs
    unfold collect_helper
  congr

private lemma collect_helper_node' (O : OBdd n m) {j : Fin m} (h : O.1.root = .node j) :
    collect_helper O I = if I.1[j] then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩) := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only at h
  have := collect_helper_node (h := (show Bdd.Ordered {heap := M, root := .node j} by simp_rw [← h]; exact o)) (I := I)
  simp_rw [h]
  assumption

private theorem collect_helper_retains_found {O : OBdd n m} {I : Vector Bool m × List (Fin m)} :
    j ∈ I.2 → j ∈ (collect_helper O I).2 := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O_root_def]
    assumption
  | node i =>
    rw [collect_helper_node' O O_root_def]
    cases I.1[i]
    case true  => simpa
    case false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have : j ∈ (collect_helper (O.low O_root_def) (I.1.set i true, i :: I.2)).2 := by
        apply collect_helper_retains_found
        simp only []
        cases decEq j i with
        | isFalse hf => right; assumption
        | isTrue ht => rw [ht]; left
      exact collect_helper_retains_found this
termination_by O

private theorem collect_helper_retains_marked {O : OBdd n m} {I : Vector Bool m × List (Fin m)} {j : Fin m}:
    I.1[j] = true → (collect_helper O I).1[j] = true := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O_root_def]
    assumption
  | node i =>
    rw [collect_helper_node' O O_root_def]
    cases I.1[i]
    case true  => simpa
    case false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have : (collect_helper (O.low O_root_def) (I.1.set i true, i :: I.2)).1[j] = true := by
        apply collect_helper_retains_marked
        simp only []
        cases decEq i j with
        | isFalse hf =>
          have : i.1 ≠ j.1 := by
            exact Fin.val_ne_of_ne hf
          simp only [Fin.getElem_fin]
          rw [Vector.getElem_set_ne _ _ this]
          assumption
        | isTrue ht => rw [ht]; simp
      exact collect_helper_retains_marked this
termination_by O

private theorem collect_helper_only_marks_reachable {j : Fin m} {O : OBdd n m} {I : Vector Bool m × List (Fin m)} :
    I.1[j] = false → (collect_helper O I).1[j] = true → Pointer.Reachable O.1.heap O.1.root (.node j) := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O_root_def, h1] at h2; contradiction
  | node i =>
    cases decEq i j with
    | isTrue ht  => rw [ht]; exact Relation.ReflTransGen.refl
    | isFalse hf =>
      rw [collect_helper_node' O O_root_def] at h2
      cases hh : I.1[i] with
      | true =>
        rw [hh] at h2
        simp only [↓reduceIte] at h2
        rw [h1] at h2
        contradiction
      | false =>
        rw [hh] at h2
        simp at h2
        rw [← O_root_def]
        cases hhh : (collect_helper (O.low O_root_def) (I.1.set i true, i :: I.2)).1[j] with
        | false =>
          have : Pointer.Reachable (O.high O_root_def).1.heap (O.high O_root_def).1.root (.node j) := by
            apply collect_helper_only_marks_reachable (I := (collect_helper (O.low O_root_def) (I.1.set i true, i :: I.2)))
            · assumption
            · assumption
          simp at this
          trans (O.high O_root_def).1.root
          · exact Bdd.reachable_of_edge (Bdd.edge_of_high (h := O_root_def) O.1)
          · assumption
        | true =>
          have : Pointer.Reachable (O.low O_root_def).1.heap (O.low O_root_def).1.root (.node j) := by
            apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
            · have : i.1 ≠ j.1 := by
                exact Fin.val_ne_of_ne hf
              simp only [Fin.getElem_fin]
              rw [Vector.getElem_set_ne _ _ this]
              assumption
            · assumption
          simp at this
          trans (O.low O_root_def).1.root
          · exact Bdd.reachable_of_edge (Bdd.edge_of_low (h := O_root_def) O.1)
          · assumption
termination_by O

private theorem collect_helper_spec {O : OBdd n m} :
    (∀ i, (Pointer.Reachable O.1.heap O.1.root (.node i) → I.1[i] = true → i ∈ I.2)) →
    ∀ i, (Pointer.Reachable O.1.heap O.1.root (.node i) → (collect_helper O I).1[i] → i ∈ (collect_helper O I).2) := by
  intro h j re ma
  cases O_root_def : O.1.root with
  | terminal b =>
    have : (⟨.node j, re⟩ : O.1.RelevantPointer).1  = .terminal b := by
      apply Bdd.eq_terminal_of_relevant
      rw [← O_root_def]
    contradiction
  | node k =>
    rw [collect_helper_node' O O_root_def] at ma
    rw [collect_helper_node' O O_root_def]
    cases hh : I.1[k] with
    | true =>
      rw [hh] at ma
      simp at ma
      simp
      exact h j re ma
    | false =>
      rw [hh] at ma
      simp at ma
      simp
      cases decEq k j with
      | isTrue hht =>
        apply collect_helper_retains_found
        apply collect_helper_retains_found
        rw [hht]
        left
      | isFalse hhf =>
        cases hhh : I.1[j] with
        | true =>
          apply collect_helper_retains_found
          apply collect_helper_retains_found
          right
          apply h <;> assumption
        | false=>
          cases hhhh : (collect_helper (O.low O_root_def) (I.1.set k true, k :: I.2)).1[j] with
          | true =>
            have : j ∈ (collect_helper (O.low O_root_def) (I.1.set k true, k :: I.2)).2 := by
              apply collect_helper_spec
              · intro i' re' ma'
                simp at ma'
                simp at re'
                simp only
                cases decEq k i' with
                | isFalse hff =>
                  rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hff])] at ma'
                  right
                  apply h
                  exact Pointer.Reachable.trans (Bdd.reachable_of_edge (Bdd.edge_of_low (h := O_root_def) O.1)) re'
                  exact ma'
                | isTrue  htt => rw [htt]; left
              · have : (I.1.set k true, k :: I.2).1[j] = false := by
                  simp only [Fin.getElem_fin]
                  rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hhf])]
                  exact hhh
                apply collect_helper_only_marks_reachable this hhhh
              · exact hhhh
            apply collect_helper_retains_found this
          | false=>
            apply collect_helper_spec
            · intro i' re' ma'
              simp at ma' re'
              have := h i' (Pointer.Reachable.trans (Bdd.reachable_of_edge (Bdd.edge_of_high (h := O_root_def) O.1)) re')
              cases hhhhh : I.1[i'] with
              | true =>
                apply this at hhhhh
                have : i' ∈ (I.1.set k true, k :: I.2).2 := by simp only; right; exact hhhhh
                apply collect_helper_retains_found this
              | false=>
                cases decEq k i' with
                | isTrue hhtt =>
                  apply collect_helper_retains_found
                  rw [hhtt]
                  left
                | isFalse hhff =>
                  have that : (I.1.set k true, k :: I.2).1[i'] = false := by
                    simp only [Fin.getElem_fin]
                    rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hhff])]
                    exact hhhhh
                  apply collect_helper_spec
                  · intro i'' re'' ma''
                    simp at ma''
                    simp at re''
                    simp only
                    cases decEq k i'' with
                    | isFalse hfff =>
                      rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hfff])] at ma''
                      right
                      apply h
                      exact Pointer.Reachable.trans (Bdd.reachable_of_edge (Bdd.edge_of_low (h := O_root_def) O.1)) re''
                      exact ma''
                    | isTrue  htt => rw [htt]; left
                  · apply collect_helper_only_marks_reachable that ma'
                  · exact ma'
            · apply collect_helper_only_marks_reachable hhhh ma
            · assumption
termination_by O

private lemma collect_spec' {O : OBdd n m} {j : Fin m} {I : Vector Bool m × List (Fin m)} :
    Pointer.Reachable O.1.heap O.1.root (.node j) →
    (∀ i, (Pointer.Reachable O.1.heap O.1.root (.node i) → Pointer.Reachable O.1.heap (.node i) (.node j) → I.1[i] = false)) →
    (collect_helper O I).1[j] = true := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b =>
    have : (⟨.node j, h1⟩ : O.1.RelevantPointer).1  = .terminal b := by
      apply Bdd.eq_terminal_of_relevant
      rw [← O_root_def]
    contradiction
  | node i =>
    rw [collect_helper_node' O O_root_def]
    have : I.1[i] = false := by
      apply h2 i
      · rw [← O_root_def]
        exact Relation.ReflTransGen.refl
      · rw [← O_root_def]
        exact h1
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases decEq i j with
    | isTrue h =>
      apply collect_helper_retains_marked
      apply collect_helper_retains_marked
      rw [h]
      simp
    | isFalse hij =>
      cases Pointer.instDecidableReachable (O.low O_root_def) (.node j) with
      | isTrue ht  =>
        apply collect_helper_retains_marked
        apply collect_spec'
        · exact ht
        · intro i' re1 re2
          simp only
          cases decEq i i' with
          | isTrue h =>
            exfalso
            apply OBdd.not_oedge_reachable (oedge_of_low (h := O_root_def))
            rw [← h] at re1
            rw [O_root_def]
            exact re1
          | isFalse h =>
            simp only [Fin.getElem_fin]
            rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne h])]
            apply h2
            exact Pointer.Reachable.trans (Bdd.reachable_of_edge (Bdd.edge_of_low (h := O_root_def) O.1)) re1
            exact re2
      | isFalse hf =>
        apply collect_spec'
        · cases (OBdd.reachable_or_eq_low_high (p := .node j) h1) with
        | inl h => rw [O_root_def] at h; simp at h; contradiction
        | inr h =>
          rcases h with ⟨j', h', d⟩
          have same : i = j' := by rw [O_root_def] at h'; simp at h'; assumption
          subst same
          cases d with
          | inl => contradiction
          | inr => assumption
        · intro i' re ma
          contrapose! hf
          simp only [Bool.not_eq_false] at hf
          apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
          simp only [Fin.getElem_fin]
          rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hij])]
          apply h2
          · exact Pointer.Reachable.trans (Bdd.reachable_of_edge (Bdd.edge_of_high (h := O_root_def) O.1)) (Pointer.Reachable.trans re ma)
          · exact Relation.ReflTransGen.refl
          · apply collect_spec'
            · have that : Pointer.Reachable (O.low O_root_def).1.heap (O.low O_root_def).1.root (.node i') := by
                apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
                · cases decEq i i' with
                  | isFalse hff =>
                    simp only [Fin.getElem_fin]
                    rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hff])]
                    apply h2 i' (Pointer.Reachable.trans (Bdd.reachable_of_edge (Bdd.edge_of_high (h := O_root_def) O.1)) re) ma
                  | isTrue htt =>
                    exfalso
                    apply OBdd.not_oedge_reachable (oedge_of_high (h := O_root_def))
                    rw [htt] at O_root_def
                    rw [O_root_def]
                    exact re
                · assumption
              exact Pointer.Reachable.trans that ma
            · intro i'' re1 re2
              simp only
              cases decEq i i'' with
              | isTrue h =>
                rw [← h] at re1
                exfalso
                apply OBdd.not_oedge_reachable (oedge_of_low (h := O_root_def))
                rw [O_root_def]
                exact re1
              | isFalse h =>
                simp only [Fin.getElem_fin]
                rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne h])]
                apply h2
                exact Pointer.Reachable.trans (Bdd.reachable_of_edge (Bdd.edge_of_low (h := O_root_def) O.1)) re1
                exact re2
termination_by O

/-- `collect` is correct. -/
theorem collect_spec {O : OBdd n m} {j : Fin m} : Pointer.Reachable O.1.heap O.1.root (.node j) → j ∈ collect O := by
  intro h
  simp [collect]
  apply collect_helper_spec
  · intro i re ma
    simp only [Fin.getElem_fin] at ma
    rw [Vector.getElem_replicate _] at ma
    contradiction
  · assumption
  · apply collect_spec' h
    intro i re1 re2
    simp only [Fin.getElem_fin, Vector.getElem_replicate]

private theorem collect_helper_spec_reverse (O : OBdd n m) (r : Pointer m) I :
    Pointer.Reachable O.1.heap r O.1.root →
    (∀ i ∈ I.2, Pointer.Reachable O.1.heap r (.node i)) →
    ∀ i ∈ (collect_helper O I).2, Pointer.Reachable O.1.heap r (.node i) := by
  intro h0 h1 i h2
  cases h : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' h] at h2
    exact h1 i h2
  | node j =>
    rw [collect_helper_node' O h] at h2
    split at h2
    next ht =>
      exact h1 i h2
    next hf =>
      cases List.instDecidableMemOfLawfulBEq i (j :: I.2) with
      | isTrue htt =>
        cases htt with
        | head as    => convert h0; symm; assumption
        | tail b hin => exact h1 i hin
      | isFalse hff =>
        cases List.instDecidableMemOfLawfulBEq i (collect_helper (O.low h) (I.1.set j true, j :: I.2)).2 with
        | isFalse hhf =>
          rw [← Bdd.high_heap_eq_heap (h := h)]
          refine collect_helper_spec_reverse (O.high h) r _ ?_ ?_ i h2
          · trans O.1.root
            · exact h0
            · exact Bdd.reachable_of_edge (Bdd.edge_of_high (h := h))
          · intro i' hi'
            simp only [OBdd.high_heap_eq_heap]
            rw [← OBdd.low_heap_eq_heap (h := h)]
            refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i' hi'
            · trans O.1.root
              · exact h0
              · exact Bdd.reachable_of_edge (Bdd.edge_of_low (h := h))
            · intro i'' hi''
              simp only at hi''
              cases hi'' with
              | head as     => simp only [OBdd.low_heap_eq_heap]; convert h0; symm; assumption
              | tail _ hi'' =>
                simp only [OBdd.low_heap_eq_heap]
                exact h1 i'' hi''
        | isTrue hht =>
          rw [← OBdd.low_heap_eq_heap (h := h)]
          refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i hht
          · trans O.1.root
            · exact h0
            · exact OBdd.reachable_of_edge (Bdd.edge_of_low (h := h))
          · intro i' hi'
            simp only at hi'
            cases hi' with
            | head as    => simp only [OBdd.low_heap_eq_heap]; convert h0; symm; assumption
            | tail _ hi' =>
              simp only [OBdd.low_heap_eq_heap]
              exact h1 i' hi'
termination_by O

theorem collect_spec_reverse {O : OBdd n m} {j : Fin m} :
    j ∈ collect O → Pointer.Reachable O.1.heap O.1.root (.node j) := by
  intro h
  simp only [collect] at h
  apply collect_helper_spec_reverse O O.1.root (Vector.replicate m false, []) (Relation.ReflTransGen.refl)
  · simp
  · assumption

private theorem collect_helper_nodup {I : Vector Bool m × List (Fin m)} {O : OBdd n m} :
    (∀ i ∈ I.2, I.1[i] = true) ∧ I.2.Nodup →
    (∀ i ∈ (collect_helper O I).2, (collect_helper O I).1[i] = true) ∧ (collect_helper O I).2.Nodup := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b => simpa [collect_helper_terminal' O_root_def]
  | node     j =>
    rw [collect_helper_node' O O_root_def]
    split
    next heq => assumption
    next heq =>
      apply collect_helper_nodup
      apply collect_helper_nodup
      simp only [List.mem_cons, forall_eq_or_imp, true_and]
      constructor
      · constructor
        · simp
        · intro i hi
          cases decEq j i with
          | isFalse hf =>
            simp only [Fin.getElem_fin]
            rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hf])]
            exact h.1 i hi
          | isTrue  ht => simp_all
      · constructor
        · contrapose heq
          simp_all
        · exact h.2
termination_by O

theorem mem_collect_iff_reachable {O : OBdd n m} {j : Fin m} :
    j ∈ collect O ↔ Pointer.Reachable O.1.heap O.1.root (.node j) := ⟨collect_spec_reverse, collect_spec⟩

theorem collect_nodup {O : OBdd n m} : (collect O).Nodup := by
  simp only [collect]
  exact (collect_helper_nodup (by simp)).2

end Collect
