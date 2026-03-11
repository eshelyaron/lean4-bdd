import Bdd.Basic

open Pointer

/-!
# Decision procedure for `Bdd.Ordered`

This file provides a `DecidablePred` instance for `Bdd.Ordered`.

The decision procedure is a DFS on the BDD graph that:
- Returns `false` immediately upon detecting a back-edge (cycle).
- Checks the variable-ordering condition at each internal node.

Key lemmas:
- `goOrdered_sound`: `goOrdered = true` implies all reachable nodes satisfy ordering.
- `goOrdered_complete`: if the BDD is ordered, `goOrdered` returns `true`.
-/

namespace Bdd

private instance instDecidableMayPrecede {n m} (M : Vector (Node n m) m) (p q : Pointer m) :
    Decidable (MayPrecede M p q) := by
  simp only [MayPrecede]
  infer_instance

private lemma card_insert_lt {m : Nat} {visited : Finset (Fin m)} {j : Fin m}
    (h : j ∉ visited) : m - (insert j visited).card < m - visited.card := by
  have h1 : (insert j visited).card = visited.card + 1 := Finset.card_insert_of_notMem h
  have h2 : visited.card + 1 ≤ m :=
    calc visited.card + 1
        = (insert j visited).card := h1.symm
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
      _ = m := by simp
  omega

private def goOrdered {n m : Nat} (M : Vector (Node n m) m) (p : Pointer m)
    (visited : Finset (Fin m)) : Bool :=
  match p with
  | .terminal _ => true
  | .node j =>
    if j ∈ visited then false
    else
      decide (MayPrecede M (.node j) M[j].low)  &&
      decide (MayPrecede M (.node j) M[j].high) &&
      goOrdered M M[j].low  (insert j visited) &&
      goOrdered M M[j].high (insert j visited)
termination_by m - visited.card
decreasing_by all_goals exact card_insert_lt (by assumption)

private lemma goOrdered_sound {n m : Nat} (M : Vector (Node n m) m) (p : Pointer m)
    (visited : Finset (Fin m))
    (h : goOrdered M p visited = true)
    (k : Fin m) (hk : k ∉ visited) (hr : Reachable M p (.node k)) :
    MayPrecede M (.node k) M[k].low ∧ MayPrecede M (.node k) M[k].high := by
  match p with
  | .terminal b =>
    exact absurd (eq_terminal_of_reachable hr) (by simp)
  | .node j =>
    simp only [goOrdered] at h
    split at h
    · contradiction
    · rename_i h_not_mem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hml, hmh⟩, hgl⟩, hgh⟩ := h
      rw [Pointer.Reachable_iff] at hr
      rcases hr with heq | ⟨j', heq_j, hl_or_h⟩
      · injection heq with heq; subst heq; exact ⟨hml, hmh⟩
      · injection heq_j with heq_j; subst heq_j
        rcases hl_or_h with hrl | hrh
        · by_cases hjk : k = j
          · subst hjk; exact ⟨hml, hmh⟩
          · exact goOrdered_sound M M[j].low (insert j visited) hgl k
              (by simp [Finset.mem_insert, hjk, hk]) hrl
        · by_cases hjk : k = j
          · subst hjk; exact ⟨hml, hmh⟩
          · exact goOrdered_sound M M[j].high (insert j visited) hgh k
              (by simp [Finset.mem_insert, hjk, hk]) hrh
termination_by m - visited.card
decreasing_by all_goals exact card_insert_lt (by assumption)

private lemma goOrdered_complete {n m : Nat} (M : Vector (Node n m) m) (p : Pointer m)
    (visited : Finset (Fin m))
    (ho : Bdd.Ordered {heap := M, root := p})
    (hv : ∀ k ∈ visited, ¬ Reachable M p (.node k)) :
    goOrdered M p visited = true := by
  match p with
  | .terminal _ =>
    simp only [goOrdered]
  | .node j =>
    have hj : j ∉ visited :=
      fun hjv ↦ absurd Relation.ReflTransGen.refl (hv j hjv)
    simp only [goOrdered, if_neg hj, Bool.and_eq_true, decide_eq_true_eq]
    let hO : OBdd n m := ⟨{heap := M, root := .node j}, ho⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact @ho ⟨.node j, .refl⟩ ⟨M[j].low, .tail .refl (Edge.low rfl)⟩ (Edge.low rfl)
    · exact @ho ⟨.node j, .refl⟩ ⟨M[j].high, .tail .refl (Edge.high rfl)⟩ (Edge.high rfl)
    · apply goOrdered_complete M M[j].low (insert j visited)
          (Bdd.ordered_of_edge ho (Edge.low rfl))
      intro k hk hkr
      simp only [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · exact OBdd.not_oedge_reachable (oedge_of_low (O := hO) (h := rfl)) hkr
      · exact hv k hk (.trans (.tail .refl (Edge.low rfl)) hkr)
    · apply goOrdered_complete M M[j].high (insert j visited)
          (Bdd.ordered_of_edge ho (Edge.high rfl))
      intro k hk hkr
      simp only [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · exact OBdd.not_oedge_reachable (oedge_of_high (O := hO) (h := rfl)) hkr
      · exact hv k hk (.trans (.tail .refl (Edge.high rfl)) hkr)
termination_by m - visited.card
decreasing_by all_goals exact card_insert_lt hj

instance instDecidableOrdered {n m : Nat} : DecidablePred (@Bdd.Ordered n m) := fun B ↦ by
  cases h : goOrdered B.heap B.root ∅
  · apply isFalse
    intro ho
    have := goOrdered_complete B.heap B.root ∅ ho (by simp)
    simp [this] at h
  · apply isTrue
    intro x y e
    simp only [Bdd.RelevantMayPrecede]
    obtain ⟨p, hp⟩ := x
    obtain ⟨q, _⟩ := y
    match p with
    | .terminal b =>
      exact absurd e not_terminal_edge
    | .node j =>
      have sound := goOrdered_sound B.heap B.root ∅ h j (Finset.notMem_empty j) hp
      cases e <;> grind

end Bdd
