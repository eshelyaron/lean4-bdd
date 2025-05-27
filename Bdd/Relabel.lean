import Bdd.Basic
import Bdd.DecisionTree

namespace Relabel

private def relabel_node {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : Node n m → Node (f n) m
  | ⟨var, low, high⟩ => ⟨⟨f var.1, hf _⟩, low, high⟩

private def relabel_heap {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) :
    Vector (Node n m) m → Vector (Node (f n) m) m := Vector.map (relabel_node hf)

private def relabel {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : Bdd n m → Bdd (f n) m
  | ⟨heap, root⟩ => ⟨relabel_heap hf heap, root⟩

private lemma relabel_edge_iff {B : Bdd n m} {x y : Pointer m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} :
    Edge B.heap x y ↔ Edge (relabel hf B).heap x y := by
  constructor
  · intro e
    cases e with
    | low  _ => left;  simpa [relabel, relabel_heap]
    | high _ => right; simpa [relabel, relabel_heap]
  · intro e
    cases e with
    | low  _ => left;  simp_all [relabel, relabel_heap, relabel_node]; assumption
    | high _ => right; simp_all [relabel, relabel_heap, relabel_node]; assumption

private lemma relabel_reachable_iff {B : Bdd n m} : Pointer.Reachable B.heap B.root x ↔ Pointer.Reachable (relabel h B).heap (relabel h B).root x := by
  constructor
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (relabel_edge_iff.mp e)
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (relabel_edge_iff.mpr e)

private lemma relabel_relevantMayPrecede {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i'}
    {x y : Pointer m}
    {hx : Pointer.Reachable (relabel hf B).heap (relabel hf B).root x}
    {hy : Pointer.Reachable (relabel hf B).heap (relabel hf B).root y} :
    B.RelevantMayPrecede ⟨x, relabel_reachable_iff.mpr hx⟩ ⟨y, relabel_reachable_iff.mpr hy⟩ → (relabel hf B).RelevantMayPrecede ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro h
  simp only [Bdd.RelevantMayPrecede] at h
  simp only [Bdd.RelevantMayPrecede]
  cases x with
  | terminal _ => absurd h; exact Pointer.not_terminal_MayPrecede
  | node j =>
    cases y with
    | terminal _ => apply Pointer.MayPrecede_node_terminal
    | node j' =>
      simp only [Pointer.MayPrecede, relabel, relabel_heap, Pointer.toVar] at h
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff] at h
      simp only [Pointer.MayPrecede, relabel, relabel_heap, Pointer.toVar]
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_map, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff]
      simp only [relabel_node]
      simp only [Fin.eta, Fin.mk_lt_mk, add_lt_add_iff_right, Fin.val_fin_lt]
      apply hu
      · exact h
      · use j
        constructor
        · exact relabel_reachable_iff.mpr hx
        · rfl
      · use j'
        constructor
        · exact relabel_reachable_iff.mpr hy
        · rfl

private lemma relabel_relevantEdge {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {x y : Pointer m}
    {hx : Pointer.Reachable (relabel hf B).heap (relabel hf B).root x}
    {hy : Pointer.Reachable (relabel hf B).heap (relabel hf B).root y} :
    (relabel hf B).RelevantEdge ⟨x, hx⟩ ⟨y, hy⟩ → B.RelevantEdge ⟨x, relabel_reachable_iff.mpr hx⟩ ⟨y, relabel_reachable_iff.mpr hy⟩ := by
  intro h
  simp_all only [Bdd.RelevantEdge, relabel, relabel_heap]
  cases h with
  | low _ =>
    left
    simp_all [relabel_node]
    assumption
  | high _ =>
    right
    simp_all [relabel_node]
    assumption

private lemma relabel_preserves_ordered {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} :
    (∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') → Bdd.Ordered B → Bdd.Ordered (relabel hf B) := by
  intro hu ho
  rintro _ _ hxy
  apply relabel_relevantMayPrecede
  exact hu
  apply ho
  exact relabel_relevantEdge hxy

def orelabel (O : OBdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') : OBdd (f n) m :=
    ⟨(relabel hf O.1), relabel_preserves_ordered hu O.2⟩

private lemma orelabel_low {O : OBdd n m} {h : O.1.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    (OBdd.low (orelabel O hf hu) h) = orelabel (O.low h) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')) := by
  rcases O with ⟨B, o⟩
  simp only [OBdd.low]
  congr
  simp only [orelabel, relabel, relabel_heap, Bdd.low_heap_eq_heap]
  simp only at h
  simp_rw [h]
  simp only [Bdd.low]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

private lemma orelabel_high {O : OBdd n m} {h : O.1.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    (OBdd.high (orelabel O hf hu) h) = orelabel (O.high h) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')) := by
  rcases O with ⟨B, o⟩
  simp only [OBdd.high]
  congr
  simp only [orelabel, relabel, relabel_heap, Bdd.high_heap_eq_heap]
  simp only at h
  simp_rw [h]
  simp only [Bdd.high]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

private lemma brelabel_low {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    (OBdd.low ⟨relabel hf B, relabel_preserves_ordered hu o⟩ h) =
      ⟨relabel hf (OBdd.low ⟨B, o⟩ h).1, relabel_preserves_ordered (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')) (OBdd.low ⟨B, o⟩ h).2⟩ := by
  exact orelabel_low (O := ⟨B, o⟩) hf hu

private lemma brelabel_high {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    (OBdd.high ⟨relabel hf B, relabel_preserves_ordered hu o⟩ h) =
      ⟨relabel hf (OBdd.high ⟨B, o⟩ h).1, relabel_preserves_ordered (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')) (OBdd.high ⟨B, o⟩ h).2⟩ := by
  exact orelabel_high (O := ⟨B, o⟩) hf hu

@[simp]
theorem orelabel_evaluate (O : OBdd n m) {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'} {I : Vector Bool (f n)} :
    OBdd.evaluate (orelabel O hf hu) I = O.evaluate (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp only [orelabel]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [relabel]
    rw [OBdd.evaluate_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.evaluate_terminal]
    simp
  | node j =>
    rw [OBdd.evaluate_node'' O_root_def]
    have that : (⟨(relabel hf O.1), relabel_preserves_ordered hu O.2⟩ : OBdd _ _).1.root = Pointer.node j := O_root_def
    rw [OBdd.evaluate_node'' that]
    simp only
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      simp only [relabel, relabel_heap, Fin.getElem_fin, Vector.getElem_map, relabel_node]
      simp only [Fin.eta]
      simp_all only [Vector.getElem_ofFn]
      rfl
    · have := orelabel_evaluate
        (hu := (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')))
        (hf := hf)
        (O.high O_root_def) (I := I)
      rw [← this]
      rw [← orelabel_high hf hu]
      rfl
    · have := orelabel_evaluate
        (hu := (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')))
        (hf := hf)
        (O.low O_root_def) (I := I)
      rw [← this]
      rw [← orelabel_low hf hu]
      rfl
termination_by O

private lemma relabel_preserves_noRedundancy {B : Bdd n m} : B.NoRedundancy → (relabel hf B).NoRedundancy := by
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
      simp only [relabel, relabel_heap, Fin.getElem_fin, relabel_node] at red
      apply hnr ⟨p, relabel_reachable_iff.mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all only [Vector.getElem_map, Fin.getElem_fin]
      simp only [relabel, relabel_heap, Fin.getElem_fin, relabel_node] at red
      exact red

private lemma relabel_toTree_relabel (O : OBdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    OBdd.toTree (orelabel O hf hu) = DecisionTree.relabel hf (OBdd.toTree O) := by
  simp only [orelabel]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [relabel]
    rw [OBdd.toTree_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.toTree_terminal]
    simp [DecisionTree.relabel]
  | node _ =>
    rw [OBdd.toTree_node O_root_def]
    rw [OBdd.toTree_node (by trans O.1.root; rfl; exact O_root_def)]
    simp only [Fin.getElem_fin]
    congr 1
    · simp only [relabel, relabel_heap, Vector.getElem_map, relabel_node, Fin.eta, Bdd.Ordered.eq_1, Fin.mk.injEq, Nat.add_right_cancel_iff]
      rfl
    · have := relabel_toTree_relabel (O := (O.low O_root_def)) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi'))
      rw [← orelabel_low] at this
      exact this
    · have := relabel_toTree_relabel (O := (O.high O_root_def)) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi'))
      rw [← orelabel_high] at this
      exact this
termination_by O

private lemma relabel_toTree_relabel' {B : Bdd n m} {o : B.Ordered} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    OBdd.toTree ⟨relabel hf B, relabel_preserves_ordered hu o⟩ = DecisionTree.relabel hf (OBdd.toTree ⟨B, o⟩) := relabel_toTree_relabel ⟨B, o⟩ hf hu

private lemma orelabel_preserves_similarRP {O : OBdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'}
    {p q : Pointer m}
    {hp : Pointer.Reachable (orelabel O hf hu).1.heap (orelabel O hf hu).1.root p}
    {hq : Pointer.Reachable (orelabel O hf hu).1.heap (orelabel O hf hu).1.root q} :
    (orelabel O hf hu).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ → O.SimilarRP ⟨p, relabel_reachable_iff.mpr hp⟩ ⟨q, relabel_reachable_iff.mpr hq⟩ := by
  intro sim
  simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at sim
  simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar]
  cases p with
  | terminal _ =>
    cases q with
    | terminal _ => simp_all
    | node _ =>
      simp only [OBdd.toTree_terminal] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
  | node j =>
    cases q with
    | terminal _ =>
      simp only [OBdd.toTree_terminal] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
    | node i =>
      conv at sim =>
        lhs
        rw [OBdd.toTree_node rfl]
      conv at sim =>
        rhs
        rw [OBdd.toTree_node rfl]
      injection sim with ha hb hc
      simp only [Fin.getElem_fin] at ha
      simp only [orelabel, relabel, relabel_heap, Vector.getElem_map, relabel_node, Fin.eta, Fin.mk.injEq, Nat.add_right_cancel_iff] at ha
      conv =>
        lhs
        rw [OBdd.toTree_node rfl]
      conv =>
        rhs
        rw [OBdd.toTree_node rfl]
      have help1 : ∀ x, Bdd.usesVar { heap := O.1.heap, root := Pointer.node j } x → O.1.usesVar x := by
          rintro x ⟨jj, h1, h2⟩
          use jj
          constructor
          · trans Pointer.node j
            · exact relabel_reachable_iff.mpr hp
            · exact h1
          · exact h2
      have help2 : ∀ x, Bdd.usesVar { heap := O.1.heap, root := Pointer.node i } x → O.1.usesVar x := by
          rintro x ⟨jj, h1, h2⟩
          use jj
          constructor
          · trans Pointer.node i
            · exact relabel_reachable_iff.mpr hq
            · exact h1
          · exact h2
      congr 1
      · simp only
        by_contra c
        apply ne_iff_lt_or_gt.mp at c
        cases c with
        | inl h => exact (ne_iff_lt_or_gt.mpr (.inl (hu O.1.heap[j].var O.1.heap[i].var h ⟨j, relabel_reachable_iff.mpr hp, rfl⟩ ⟨i, relabel_reachable_iff.mpr hq, rfl⟩))) ha
        | inr h => exact (ne_iff_lt_or_gt.mpr (.inr (hu O.1.heap[i].var O.1.heap[j].var h ⟨i, relabel_reachable_iff.mpr hq, rfl⟩ ⟨j, relabel_reachable_iff.mpr hp, rfl⟩))) ha
      · simp only [orelabel] at hb
        simp only [relabel] at hb
        simp_rw [← relabel.eq_1] at hb
        conv at hb =>
          lhs
          rw [brelabel_low (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp)) hf (by simp_all)]
        conv at hb =>
          rhs
          rw [brelabel_low (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq)) hf (by simp_all)]
        simp only [OBdd.low] at hb
        simp only [OBdd.low]
        have helplj : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node j } : Bdd n m).low rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help1
          apply Bdd.usesVar_of_low_usesVar hx
        have helpli : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node i } : Bdd n m).low rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help2
          apply Bdd.usesVar_of_low_usesVar hx
        conv at hb =>
          lhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp))) hf (by simp_all)]
        conv at hb =>
          rhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq))) hf (by simp_all)]
        rw [DecisionTree.relabel_injective hb]
        intro ii ii' hii hii' hfi
        rw [← OBdd.toTree_usesVar] at hii hii'
        contrapose hfi
        apply ne_iff_lt_or_gt.mpr
        cases ne_iff_lt_or_gt.mp hfi with
        | inl hfi =>
          left
          apply hu
          · exact hfi
          · apply help1
            apply Bdd.usesVar_of_low_usesVar
            exact hii
            rfl
          · apply help2
            apply Bdd.usesVar_of_low_usesVar
            exact hii'
            rfl
        | inr hfi =>
          right
          apply hu
          · exact hfi
          · apply help2
            apply Bdd.usesVar_of_low_usesVar
            exact hii'
            rfl
          · apply help1
            apply Bdd.usesVar_of_low_usesVar
            exact hii
            rfl
      · simp only [orelabel] at hc
        simp only [relabel] at hc
        simp_rw [← relabel.eq_1] at hc
        conv at hc =>
          lhs
          rw [brelabel_high (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp)) hf (by simp_all)]
        conv at hc =>
          rhs
          rw [brelabel_high (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq)) hf (by simp_all)]
        simp only [OBdd.high] at hc
        simp only [OBdd.high]
        have helphj : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node j } : Bdd n m).high rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help1
          apply Bdd.usesVar_of_high_usesVar hx
        have helphi : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node i } : Bdd n m).high rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help2
          apply Bdd.usesVar_of_high_usesVar hx
        conv at hc =>
          lhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp))) hf (by simp_all)]
        conv at hc =>
          rhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq))) hf (by simp_all)]
        rw [DecisionTree.relabel_injective hc]
        intro ii ii' hii hii' hfi
        rw [← OBdd.toTree_usesVar] at hii hii'
        contrapose hfi
        apply ne_iff_lt_or_gt.mpr
        cases ne_iff_lt_or_gt.mp hfi with
        | inl hfi =>
          left
          apply hu
          · exact hfi
          · apply help1
            apply Bdd.usesVar_of_high_usesVar
            exact hii
            rfl
          · apply help2
            apply Bdd.usesVar_of_high_usesVar
            exact hii'
            rfl
        | inr hfi =>
          right
          apply hu
          · exact hfi
          · apply help2
            apply Bdd.usesVar_of_high_usesVar
            exact hii'
            rfl
          · apply help1
            apply Bdd.usesVar_of_high_usesVar
            exact hii
            rfl

lemma orelabel_reduced {O : OBdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'} :
    O.Reduced → (orelabel O hf hu).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact relabel_preserves_noRedundancy r1
  · rintro _ _ sim
    exact r2 (orelabel_preserves_similarRP sim)

@[simp]
private lemma relabel_id {B : Bdd n m} : relabel (f := id) (by simp) B = B := by
  simp only [id_eq, relabel, relabel_heap]
  congr
  ext i hi
  simp only [Vector.getElem_map, relabel_node, id_eq, Fin.eta]
  rfl

@[simp]
lemma orelabel_id {O : OBdd n m} : orelabel O (f := id) (by simp) (fun _ _ _ _ _ ↦ by simpa) = O := by simp [orelabel]

end Relabel
