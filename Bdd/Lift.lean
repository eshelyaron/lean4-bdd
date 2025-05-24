import Bdd.Basic

namespace Lift


@[simp]
private def lift_node : n ≤ n' → Node n m → Node n' m := fun h N ↦ ⟨⟨N.var.1, by exact Fin.val_lt_of_le N.var h⟩, N.low, N.high⟩

private lemma lift_node_trivial_eq {n n' m : Nat} {h : n = n'} {N : Node n m} : lift_node (n' := n') (by rw [h]) N = h ▸ N := by
  subst h
  simp_all

@[simp]
private def lift_heap : n ≤ n' → Vector (Node n m) m → Vector (Node n' m) m := fun h v ↦ Vector.map (lift_node h) v

@[simp]
def lift : n ≤ n' → Bdd n m → Bdd n' m := fun h B ↦ ⟨lift_heap h B.heap, B.root⟩

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
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, lift, lift_heap, Pointer.toVar_node_eq, Fin.getElem_fin, lift_node] at hm
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
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, lift, lift_heap, Pointer.toVar_node_eq, Fin.getElem_fin, lift_node]
        simp_all only [Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff, Vector.getElem_map, lift_node]
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

lemma lift_ordered {h : n ≤ n'} {B : Bdd n m} : B.Ordered → (lift h B).Ordered := by
  rintro ho ⟨x, hx⟩ ⟨y, hy⟩ e
  apply lift_preserves_MayPrecede.mpr
  exact ho (lift_preserves_RelevantEdge.mp ⟨hx, hy, e⟩).2.2

def olift : n ≤ n' → OBdd n m → OBdd n' m := fun h O ↦ ⟨(lift h O.1), lift_ordered O.2⟩

@[simp]
lemma olift_trivial_eq {h : n = n'} {O : OBdd n m} : (olift (n' := n') (by rw [h]) O) = h ▸ O := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only [olift, lift, lift_heap]
  congr
  · have : (lift_node (Eq.mpr (id (congrArg (fun _a ↦ _a ≤ n') h)) (le_refl n'))) = fun (x : Node n m) ↦ h ▸ x := by
      ext
      exact lift_node_trivial_eq
    rw [this]
    subst h
    simp only
    rcases M with ⟨V, l⟩
    simp [Vector.map, List.map_id_fun', id_eq]
  · subst h
    simp

private lemma lift_preserves_root {h : n ≤ n'} {B : Bdd n m} : (lift h B).root = B.root := by simp

@[simp]
private lemma olift_preserves_root {h : n ≤ n'} {O : OBdd n m} : (olift h O).1.root = O.1.root := lift_preserves_root

private lemma olift_low {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j): (olift h O).low hr = olift h (O.low hr) := by
  simp only [OBdd.low, olift, lift, lift_heap]
  simp_rw [Bdd.low_heap_eq_heap]
  simp_rw [hr]
  simp [Bdd.low]

private lemma olift_high {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j): (olift h O).high hr = olift h (O.high hr) := by
  simp only [OBdd.high, olift, lift, lift_heap]
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
      simp only [olift, lift, lift_heap, Fin.getElem_fin, lift_node] at red
      apply hnr ⟨p, lift_reachable_iff.mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all

-- FIXME: Move to DecisionTree.lean
def tlift : n ≤ n' → DecisionTree n → DecisionTree n'
  | _, .leaf b => .leaf b
  | e, .branch j l h => .branch ⟨j.1, by omega⟩ (tlift e l) (tlift e h)

lemma tlift_injective {n n' : Nat} {h : n ≤ n'} : Function.Injective (tlift h) := by
  intro x y hxy
  cases x with
  | leaf _ =>
    cases y with
    | leaf _ => simp only [tlift] at hxy; simp_all
    | branch _ _ _ => contradiction
  | branch _ _ _ =>
    cases y with
    | leaf _ => contradiction
    | branch _ _ _ =>
      simp only [tlift] at hxy
      injection hxy with a b c
      rw [tlift_injective b, tlift_injective c]
      simp_all only [Fin.mk.injEq, DecisionTree.branch.injEq, and_self, and_true]
      ext
      simp_all only

private lemma olift_preserves_toTree {h : n ≤ n'} {O : OBdd n m} : (olift h O).toTree = tlift h O.toTree := by
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [OBdd.toTree_terminal' O_root_def, tlift, olift, lift]
    simp_rw [O_root_def, OBdd.toTree_terminal]
  | node j =>
    simp only [OBdd.toTree_node O_root_def, tlift]
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

private lemma tlift_evaluate {h : n ≤ n'} {T : DecisionTree n} {I : Vector Bool n'} :
    (tlift h T).evaluate I = T.evaluate (Vector.cast (show (min n n') = n by simpa) (I.take n)) := by
  cases T with
  | leaf => simp [tlift, DecisionTree.evaluate]
  | branch _ _ _ =>
    simp only [tlift, DecisionTree.evaluate]
    rw [tlift_evaluate]
    rw [tlift_evaluate]
    refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
    simp only [eq_iff_iff, Bool.coe_iff_coe, Fin.getElem_fin]
    rename_i a _ _
    have : (I.take n)[a.1] = I[a.1] := by
      apply Vector.getElem_take
    rw [← this]
    rfl

@[simp]
lemma olift_evaluate {h : n ≤ n'} {O : OBdd n m} {I : Vector Bool n'} :
    (olift h O).evaluate I = O.evaluate (Vector.cast (show (min n n') = n by simpa) (I.take n)) := by
  simp only [OBdd.evaluate, Function.comp_apply, olift_preserves_toTree]
  rw [tlift_evaluate]

lemma olift_SimilarRP {h : n ≤ n'} {O : OBdd n m} {p q : Pointer m}
    {hp : Pointer.Reachable (olift h O).1.heap (olift h O).1.root p}
    {hq : Pointer.Reachable (olift h O).1.heap (olift h O).1.root q} :
    (olift h O).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ →
    O.SimilarRP ⟨p, (lift_reachable_iff (h := h)).mpr hp⟩ ⟨q, (lift_reachable_iff (h := h)).mpr hq⟩ := by
  intro sim
  simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at sim
  have : OBdd.toTree ⟨{heap := (olift h O).1.heap, root := p}, Bdd.ordered_of_reachable hp⟩ = OBdd.toTree (olift h ⟨{heap := O.1.heap, root := p}, Bdd.ordered_of_reachable (lift_reachable_iff.mpr hp)⟩) := by
    rfl
  rw [this] at sim
  have : OBdd.toTree ⟨{heap := (olift h O).1.heap, root := q}, Bdd.ordered_of_reachable hq⟩ = OBdd.toTree (olift h ⟨{heap := O.1.heap, root := q}, Bdd.ordered_of_reachable (lift_reachable_iff.mpr hq)⟩) := by
    rfl
  rw [this] at sim
  rw [olift_preserves_toTree] at sim
  rw [olift_preserves_toTree] at sim
  clear this
  clear this
  simp only [OBdd.SimilarRP, OBdd.Similar,OBdd.HSimilar]
  rw [tlift_injective sim]

lemma olift_reduced {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} : O.Reduced → (olift h O).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact NoRedundancy_of_olift r1
  · rintro _ _ sim; exact r2 (olift_SimilarRP sim)

end Lift
