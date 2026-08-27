module

public import Bdd.Basic

namespace Lift

def lift {n n' m} (h : n ≤ n') (B : Bdd n m) : Bdd n' m :=
  ⟨ Vector.map
      (fun N ↦ ⟨⟨N.var.1, Fin.val_lt_of_le N.var h⟩, N.low, N.high⟩)
      B.heap,
    B.root
  ⟩

lemma lift_root {n n' m} {h : n ≤ n'} {B : Bdd n m} : (lift h B).root = B.root := (rfl)

lemma lift_edge {n n' m} {h : n ≤ n'} {B : Bdd n m} : Edge (lift h B).heap = Edge B.heap := by
  ext p q
  simp_all only [edge_iff, Fin.getElem_fin, lift, Vector.getElem_map]

lemma lift_reachable_iff {n n' m} (h : n ≤ n') {B : Bdd n m} {p : Pointer m} :
    Pointer.Reachable (lift h B).heap (lift h B).root p ↔ Pointer.Reachable B.heap B.root p := by
  rw [lift_root]
  rw [Pointer.Reachable.eq_of_eq_edge lift_edge]

lemma lift_preserves_MayPrecede {n n' m} {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    (lift h B).MayPrecede p q ↔ B.MayPrecede p q := by
  simp only [Bdd.mayPrecede_iff, Fin.getElem_fin]
  grind only [lift, Vector.getElem_map, Fin.lt_def]

lemma lift_ordered {n n' m} {h : n ≤ n'} {B : Bdd n m} : B.Ordered → (lift h B).Ordered := by
  simp only [Bdd.ordered_iff]
  intro h1 p q h2 e
  apply lift_preserves_MayPrecede.mpr
  rw [lift_edge] at e
  rw [lift_reachable_iff] at h2
  exact h1 p q h2 e

public def olift {n n' m} (h : n ≤ n') (O : OBdd n m) : OBdd n' m :=
  ⟨(lift h O.1), lift_ordered O.2⟩

@[simp]
public lemma olift_trivial_eq {n n' m} {h : n = n'} {O : OBdd n m} :
    (olift (n' := n') (by rw [h]) O) = h ▸ O := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only [olift, lift]
  congr
  · subst h
    simp only
    rcases M with ⟨V, l⟩
    simp [Vector.map, id_eq]
  · subst h
    simp

@[simp]
public lemma olift_preserves_root {n n' m} {h : n ≤ n'} {O : OBdd n m} :
    (olift h O).1.root = O.1.root := by
  simp [olift, lift_root]

public lemma olift_low {n n' m} {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j):
    (olift h O).low (olift_preserves_root ▸ hr) = olift h (O.low hr) := by
  simp only [olift, lift]
  simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, Fin.getElem_fin, OBdd.eq_iff_bdd_eq,
    Vector.getElem_map, and_self]

public lemma olift_high {n n' m} {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j):
    (olift h O).high (olift_preserves_root ▸ hr) = olift h (O.high hr) := by
  simp only [olift, lift]
  simp only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high, Fin.getElem_fin, OBdd.eq_iff_bdd_eq,
    Vector.getElem_map, and_self]

lemma toTree_subBdd_olift {n n' m} {h : n ≤ n'} {O : OBdd n m} {p} :
    ((olift h O).subBdd p).toTree =
    (olift h (O.subBdd ⟨p.1, (lift_reachable_iff h).mp p.2⟩)).toTree := by
  simp only [OBdd.subBdd_eq]
  rfl

lemma NoRedundancy_of_olift {n n' m} {h : n ≤ n'} {O : OBdd n m} :
    O.1.NoRedundancy → (olift h O).1.NoRedundancy := by
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
      apply hnr ⟨p, (lift_reachable_iff h).mp hp⟩
      simp_rw [p_def]
      constructor
      simp_all

lemma olift_preserves_toTree {n n' m} {h : n ≤ n'} {O : OBdd n m} :
    (olift h O).toTree = DecisionTree.lift h O.toTree := by
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [OBdd.toTree_terminal O_root_def, DecisionTree.lift]
    have h1 : (olift h O).bdd.root = Pointer.terminal b := by
      rw [olift_preserves_root, O_root_def]
    rw [OBdd.toTree_terminal h1]
  | node j =>
    simp only [OBdd.toTree_node O_root_def, DecisionTree.lift]
    rw [← olift_preserves_toTree (h := h) (O := (O.low  O_root_def))]
    rw [← olift_preserves_toTree (h := h) (O := (O.high O_root_def))]
    rw [← olift_preserves_root (h := h)] at O_root_def
    simp only [OBdd.toTree_node O_root_def]
    simp only [DecisionTree.branch.injEq]
    constructor
    · simp [olift, lift]
    · constructor
      · rw [olift_low]
      · rw [olift_high]
termination_by O

@[simp]
public lemma olift_evaluate {n n' m} {h : n ≤ n'} {O : OBdd n m} {I : Vector Bool n'} :
    (olift h O).evaluate I = O.evaluate (Vector.cast (by simpa) (I.take n)) := by
  simp only [OBdd.evaluate_def, olift_preserves_toTree]
  rw [DecisionTree.lift_evaluate]

lemma olift_SimilarRP {n n' m} {h : n ≤ n'} {O : OBdd n m} {p q : Pointer m}
    {hp : Pointer.Reachable (olift h O).1.heap (olift h O).1.root p}
    {hq : Pointer.Reachable (olift h O).1.heap (olift h O).1.root q} :
    (olift h O).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ →
    O.SimilarRP ⟨p, (lift_reachable_iff h).mp hp⟩ ⟨q, (lift_reachable_iff h).mp hq⟩ := by
  intro sim
  simp only [OBdd.similarRP_iff] at ⊢ sim
  simp only [toTree_subBdd_olift] at sim
  simp only [olift_preserves_toTree] at sim
  rw [DecisionTree.lift_injective sim]

public lemma olift_reduced {n n' m} {h : n ≤ n'} {O : OBdd n m} : O.Reduced → (olift h O).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact NoRedundancy_of_olift r1
  · rintro _ _ sim; exact r2 (olift_SimilarRP sim)

@[simp]
public lemma olift_olift {n n' n'' m} {h1 : n ≤ n'} {h2 : n' ≤ n''} {O : OBdd n m} :
    olift h2 (olift h1 O) = olift (.trans h1 h2) O := by
  simp only [olift, lift, Vector.map_map]
  congr

end Lift
