import Bdd.Basic
import Bdd.DecisionTree

namespace Lift

@[simp]
private def lift (h : n ≤ n') (B : Bdd n m) : Bdd n' m :=
  ⟨ Vector.map
      (fun N ↦ ⟨⟨N.var.1, Fin.val_lt_of_le N.var h⟩, N.low, N.high⟩)
      B.heap,
    B.root
  ⟩

private lemma lift_edge_iff {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    Edge B.heap p q ↔ Edge (lift h B).heap p q := by
  constructor
  · intro e
    cases e with
    | low  _ => left;  simpa
    | high _ => right; simpa
  · intro e
    cases e with
    | low  _ => left;  simp_all
    | high _ => right; simp_all

private lemma lift_reachable_iff {h : n ≤ n'} {B : Bdd n m} {p : Pointer m} :
    Pointer.Reachable B.heap B.root p ↔ Pointer.Reachable (lift h B).heap (lift h B).root p := by
  constructor
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (lift_edge_iff.mp e)
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (lift_edge_iff.mpr e)

private lemma lift_preserves_MayPrecede {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    Pointer.MayPrecede (lift h B).heap p q ↔ Pointer.MayPrecede B.heap p q := by
  constructor
  · intro hm
    cases p with
    | terminal _ =>
      absurd hm
      exact Pointer.not_terminal_MayPrecede
    | node j =>
      cases q with
      | terminal _ =>
        apply Pointer.MayPrecede_node_terminal
      | node j' =>
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, lift, Pointer.toVar_node_eq, Fin.getElem_fin] at hm
        apply (Fin.natCast_lt_natCast (by omega) (by omega)).mp at hm
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin]
        aesop
  · intro hm
    cases p with
    | terminal _ =>
      absurd hm
      exact Pointer.not_terminal_MayPrecede
    | node j =>
      cases q with
      | terminal _ =>
        apply Pointer.MayPrecede_node_terminal
      | node j' =>
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin] at hm
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, lift, Pointer.toVar_node_eq, Fin.getElem_fin]
        simp_all only [Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff, Vector.getElem_map]
        refine (Fin.natCast_lt_natCast ?_ ?_).mpr ?_ <;> omega

private lemma lift_preserves_RelevantEdge {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    ( ∃ (hp : Pointer.Reachable (lift h B).heap (lift h B).root p)
        (hq : Pointer.Reachable (lift h B).heap (lift h B).root q), Bdd.RelevantEdge (lift h B) ⟨p, hp⟩ ⟨q, hq⟩) ↔
    ( ∃ (hp : Pointer.Reachable B.heap B.root p)
        (hq : Pointer.Reachable B.heap B.root q), Bdd.RelevantEdge B ⟨p, hp⟩ ⟨q, hq⟩) := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    use (lift_reachable_iff.mpr hp)
    use (lift_reachable_iff.mpr hq)
    cases hr with
    | low  hl => simp at hl; left ; assumption
    | high hh => simp at hh; right; assumption
  · rintro ⟨hp, hq, hr⟩
    use (lift_reachable_iff.mp hp)
    use (lift_reachable_iff.mp hq)
    cases hr with
    | low  hl => simp at hl; left ; simpa
    | high hh => simp at hh; right; simpa

private lemma lift_ordered {h : n ≤ n'} {B : Bdd n m} : B.Ordered → (lift h B).Ordered := by
  rintro ho ⟨x, hx⟩ ⟨y, hy⟩ e
  apply lift_preserves_MayPrecede.mpr
  exact ho (lift_preserves_RelevantEdge.mp ⟨hx, hy, e⟩).2.2

def olift (h : n ≤ n') (O : OBdd n m) : OBdd n' m := ⟨(lift h O.1), lift_ordered O.2⟩

@[simp]
lemma olift_trivial_eq {h : n = n'} {O : OBdd n m} : (olift (n' := n') (by rw [h]) O) = h ▸ O := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only [olift, lift]
  congr
  · subst h
    simp only
    rcases M with ⟨V, l⟩
    simp [Vector.map, List.map_id_fun', id_eq]
  · subst h
    simp

@[simp]
private lemma olift_preserves_root {h : n ≤ n'} {O : OBdd n m} : (olift h O).1.root = O.1.root := by simp [olift]

private lemma olift_low {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j): (olift h O).low hr = olift h (O.low hr) := by
  simp only [OBdd.low, olift, lift]
  simp_rw [Bdd.low_heap_eq_heap]
  simp_rw [hr]
  simp [Bdd.low]

private lemma olift_high {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j): (olift h O).high hr = olift h (O.high hr) := by
  simp only [OBdd.high, olift, lift]
  simp_rw [Bdd.high_heap_eq_heap]
  simp_rw [hr]
  simp [Bdd.high]

private lemma NoRedundancy_of_olift {h : n ≤ n'} {O : OBdd n m} : O.1.NoRedundancy → (olift h O).1.NoRedundancy := by
  rintro hnr ⟨p, hp⟩ contra
  simp only at contra
  cases p_def : p with
  | terminal _ =>
    cases contra with
    | red _ => contradiction
  | node j =>
    rw [p_def] at contra
    cases contra with
    | red red =>
      simp only [olift, lift, Fin.getElem_fin] at red
      apply hnr ⟨p, (lift_reachable_iff (h := h)).mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all

private lemma olift_preserves_toTree {h : n ≤ n'} {O : OBdd n m} : (olift h O).toTree = DecisionTree.lift h O.toTree := by
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [OBdd.toTree_terminal' O_root_def, DecisionTree.lift, olift, lift]
    simp_rw [O_root_def, OBdd.toTree_terminal]
  | node j =>
    simp only [OBdd.toTree_node O_root_def, DecisionTree.lift]
    rw [← olift_preserves_toTree (h := h) (O := (O.low  O_root_def))]
    rw [← olift_preserves_toTree (h := h) (O := (O.high O_root_def))]
    rw [← olift_preserves_root (h := h)] at O_root_def
    simp only [OBdd.toTree_node O_root_def]
    simp only [DecisionTree.branch.injEq]
    constructor
    · simp [olift]
    · constructor
      · rw [olift_low]
      · rw [olift_high]
termination_by O

@[simp]
lemma olift_evaluate {h : n ≤ n'} {O : OBdd n m} {I : Vector Bool n'} :
    (olift h O).evaluate I = O.evaluate (Vector.cast (by simpa) (I.take n)) := by
  simp only [OBdd.evaluate, Function.comp_apply, olift_preserves_toTree]
  rw [DecisionTree.lift_evaluate]

private lemma olift_SimilarRP {h : n ≤ n'} {O : OBdd n m} {p q : Pointer m}
    {hp : Pointer.Reachable (olift h O).1.heap (olift h O).1.root p}
    {hq : Pointer.Reachable (olift h O).1.heap (olift h O).1.root q} :
    (olift h O).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ →
    O.SimilarRP ⟨p, (lift_reachable_iff (h := h)).mpr hp⟩ ⟨q, (lift_reachable_iff (h := h)).mpr hq⟩ := by
  intro sim
  simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at sim
  have : OBdd.toTree ⟨{heap := (olift h O).1.heap, root := p}, Bdd.ordered_of_reachable hp⟩ = OBdd.toTree (olift h ⟨{heap := O.1.heap, root := p}, Bdd.ordered_of_reachable ((lift_reachable_iff (h := h)).mpr hp)⟩) := by
    rfl
  rw [this] at sim
  have : OBdd.toTree ⟨{heap := (olift h O).1.heap, root := q}, Bdd.ordered_of_reachable hq⟩ = OBdd.toTree (olift h ⟨{heap := O.1.heap, root := q}, Bdd.ordered_of_reachable ((lift_reachable_iff (h := h)).mpr hq)⟩) := by
    rfl
  rw [this] at sim
  rw [olift_preserves_toTree] at sim
  rw [olift_preserves_toTree] at sim
  clear this
  clear this
  simp only [OBdd.SimilarRP, OBdd.Similar,OBdd.HSimilar]
  rw [DecisionTree.lift_injective sim]

lemma olift_reduced {h : n ≤ n'} {O : OBdd n m} : O.Reduced → (olift h O).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact NoRedundancy_of_olift r1
  · rintro _ _ sim; exact r2 (olift_SimilarRP sim)

@[simp]
lemma olift_olift {h1 : n ≤ n'} {h2 : n' ≤ n''} {O : OBdd n m} : olift h2 (olift h1 O) = olift (.trans h1 h2) O := by
  simp only [olift, lift, Vector.map_map]
  congr

end Lift
