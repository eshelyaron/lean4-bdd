module

public import Bdd.Basic

namespace Relabel

def relabel_node {n m} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : Node n m → Node (f n) m
  | ⟨var, low, high⟩ => ⟨⟨f var.1, hf _⟩, low, high⟩

def relabel_heap {n m} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) :
    Vector (Node n m) m → Vector (Node (f n) m) m := Vector.map (relabel_node hf)

def relabel {n m} {f : ℕ → ℕ} (hf : ∀ i : Fin n, f i < f n) : Bdd n m → Bdd (f n) m
  | ⟨heap, root⟩ => ⟨relabel_heap hf heap, root⟩

lemma relabel_root {n m} {f : ℕ → ℕ} {hf : ∀ i : Fin n, f i < f n} {B : Bdd n m} :
    (relabel hf B).root = B.root := (rfl)

lemma relabel_edge {n m} (B : Bdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) :
    Edge (relabel hf B).heap = Edge B.heap := by
  ext p q
  simp only [edge_iff, Fin.getElem_fin, relabel, relabel_heap, Vector.getElem_map, relabel_node]

lemma relabel_reachable_iff {n m : ℕ} {f : ℕ → ℕ} {h : ∀ (i : Fin n), f i < f n} {x} {B : Bdd n m} :
    Pointer.Reachable (relabel h B).heap (relabel h B).root x ↔
    Pointer.Reachable B.heap B.root x := by
  rw [relabel_root]
  rw [Pointer.Reachable.eq_of_eq_edge (relabel_edge B h)]

lemma relabel_MayPrecede {n m} {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i')
    {x y : Pointer m}
    (hx : Pointer.Reachable (relabel hf B).heap (relabel hf B).root x)
    (hy : Pointer.Reachable (relabel hf B).heap (relabel hf B).root y) :
    B.MayPrecede x y → (relabel hf B).MayPrecede x y := by
  simp only [Bdd.mayPrecede_iff, forall_exists_index, and_imp]
  intro j rfl h1
  use j, rfl
  intro j' rfl
  simp only [relabel, relabel_heap, Fin.lt_def]
  simp only [Fin.getElem_fin, Vector.getElem_map, relabel_node]
  apply hu
  · exact h1 j' rfl
  · use j
    constructor
    · exact relabel_reachable_iff.mp hx
    · rfl
  · use j'
    constructor
    · exact relabel_reachable_iff.mp hy
    · rfl

lemma relabel_ordered {n m} {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} :
    (∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') → Bdd.Ordered B → Bdd.Ordered (relabel hf B) := by
  simp only [Bdd.ordered_iff]
  intro hu ho p q hp e
  have h : B.MayPrecede p q := by
    rw [relabel_reachable_iff] at hp
    rw [relabel_edge] at e
    exact ho p q hp e
  exact relabel_MayPrecede hu hp (Pointer.Reachable.snoc hp e) h

public def orelabel {n m} (O : OBdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') : OBdd (f n) m :=
    ⟨(relabel hf O.1), relabel_ordered hu O.2⟩

lemma orelabel_reachable_iff {n m} {O : OBdd n m} {f : ℕ → ℕ} {hf : ∀ i : Fin n, f i < f n} {hu x} :
    Pointer.Reachable (orelabel O hf hu).bdd.heap (orelabel O hf hu).bdd.root x ↔
    Pointer.Reachable O.bdd.heap O.bdd.root x :=
  relabel_reachable_iff

lemma orelabel_low {n m} {O : OBdd n m} {j} {h : O.1.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    (OBdd.low (orelabel O hf hu) h) = orelabel (O.low h) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')) := by
  rw [OBdd.eq_iff_bdd_eq]
  simp only [orelabel, relabel, relabel_heap, OBdd.low_heap_eq_heap, OBdd.low_root_eq_low,
    Fin.getElem_fin, Vector.getElem_map, true_and]
  rfl

lemma orelabel_high {O : OBdd n m} {h : O.1.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    (OBdd.high (orelabel O hf hu) h) = orelabel (O.high h) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')) := by
  rw [OBdd.eq_iff_bdd_eq]
  simp only [orelabel, relabel, relabel_heap, OBdd.high_heap_eq_heap, OBdd.high_root_eq_high,
    Fin.getElem_fin, Vector.getElem_map, true_and]
  rfl

lemma brelabel_low {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    (OBdd.low ⟨relabel hf B, relabel_ordered hu o⟩ h) =
      ⟨relabel hf (OBdd.low ⟨B, o⟩ h).1, relabel_ordered (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')) (OBdd.low ⟨B, o⟩ h).2⟩ := by
  exact orelabel_low (O := ⟨B, o⟩) hf hu

lemma brelabel_high {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    (OBdd.high ⟨relabel hf B, relabel_ordered hu o⟩ h) =
      ⟨relabel hf (OBdd.high ⟨B, o⟩ h).1, relabel_ordered (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')) (OBdd.high ⟨B, o⟩ h).2⟩ := by
  exact orelabel_high (O := ⟨B, o⟩) hf hu

@[simp]
public theorem orelabel_evaluate (O : OBdd n m) {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'} {I : Vector Bool (f n)} :
    OBdd.evaluate (orelabel O hf hu) I = O.evaluate (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp only [orelabel]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [relabel, O_root_def]
    rw [OBdd.evaluate_terminal O_root_def]
    rw [OBdd.evaluate_terminal rfl]
  | node j =>
    rw [OBdd.evaluate_node' O_root_def]
    have that : (⟨(relabel hf O.1), relabel_ordered hu O.2⟩ : OBdd _ _).1.root = Pointer.node j := O_root_def
    rw [OBdd.evaluate_node' that]
    simp only
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      simp only [relabel, relabel_heap, Fin.getElem_fin, Vector.getElem_map, relabel_node]
      simp_all only [Vector.getElem_ofFn]
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

lemma relabel_preserves_noRedundancy {B : Bdd n m} : B.NoRedundancy → (relabel hf B).NoRedundancy := by
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
      simp only [relabel, relabel_heap, Fin.getElem_fin] at red
      apply hnr ⟨p, relabel_reachable_iff.mp hp⟩
      simp_rw [p_def]
      constructor
      simp_all only [Vector.getElem_map, Fin.getElem_fin]
      simp only [relabel_node] at red
      exact red

lemma relabel_toTree_relabel (O : OBdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    OBdd.toTree (orelabel O hf hu) = DecisionTree.relabel hf (OBdd.toTree O) := by
  simp only [orelabel]
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [relabel]
    rw [OBdd.toTree_terminal O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.toTree_terminal rfl]
    simp [DecisionTree.relabel]
  | node _ =>
    rw [OBdd.toTree_node O_root_def]
    rw [OBdd.toTree_node (by trans O.1.root; rfl; exact O_root_def)]
    simp only [Fin.getElem_fin]
    congr 1
    · simp only [relabel, relabel_heap, Vector.getElem_map, relabel_node]
    · have := relabel_toTree_relabel (O := (O.low O_root_def)) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi'))
      rw [← orelabel_low] at this
      exact this
    · have := relabel_toTree_relabel (O := (O.high O_root_def)) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi'))
      rw [← orelabel_high] at this
      exact this
termination_by O

lemma relabel_toTree_relabel' {n m} {B : Bdd n m} {o : B.Ordered} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    OBdd.toTree ⟨relabel hf B, relabel_ordered hu o⟩ = DecisionTree.relabel hf (OBdd.toTree ⟨B, o⟩) := relabel_toTree_relabel ⟨B, o⟩ hf hu

lemma orelabel_preserves_similarRP {n m} {O : OBdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'}
    {p q : Pointer m}
    {hp : Pointer.Reachable (orelabel O hf hu).1.heap (orelabel O hf hu).1.root p}
    {hq : Pointer.Reachable (orelabel O hf hu).1.heap (orelabel O hf hu).1.root q} :
    (orelabel O hf hu).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ → O.SimilarRP ⟨p, orelabel_reachable_iff.mp hp⟩ ⟨q, orelabel_reachable_iff.mp hq⟩ := by
  intro sim
  simp only [OBdd.similarRP_iff] at ⊢ sim
  cases p with
  | terminal _ =>
    cases q with
    | terminal _ =>
      simp_all only [OBdd.subBdd_eq, Pointer.terminal.injEq, OBdd.toTree_terminal,
        DecisionTree.leaf.injEq]
    | node _ =>
      simp only [Pointer.terminal.injEq, OBdd.toTree_terminal, OBdd.subBdd_eq] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
  | node j =>
    cases q with
    | terminal _ =>
      simp only [Pointer.terminal.injEq, OBdd.toTree_terminal, OBdd.subBdd_eq] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
    | node i =>
      rw [OBdd.toTree_node (OBdd.root_subBdd ⟨Pointer.node j, _⟩)] at sim ⊢
      rw [OBdd.toTree_node (OBdd.root_subBdd ⟨Pointer.node i, _⟩)] at sim ⊢
      injection sim with ha hb hc
      simp only [Fin.getElem_fin] at ha
      simp only [orelabel, relabel, relabel_heap, Vector.getElem_map, relabel_node,
        Fin.mk.injEq, OBdd.heap_subBdd] at ha
      have help1 : ∀ x, Bdd.usesVar { heap := O.1.heap, root := Pointer.node j } x → O.1.usesVar x := by
          rintro x ⟨jj, h1, h2⟩
          use jj
          constructor
          · trans Pointer.node j
            · exact relabel_reachable_iff.mp hp
            · exact h1
          · exact h2
      have help2 : ∀ x, Bdd.usesVar { heap := O.1.heap, root := Pointer.node i } x → O.1.usesVar x := by
          rintro x ⟨jj, h1, h2⟩
          use jj
          constructor
          · trans Pointer.node i
            · exact relabel_reachable_iff.mp hq
            · exact h1
          · exact h2
      simp only [DecisionTree.branch.injEq, OBdd.subBdd_eq]
      split_ands
      · by_contra c
        apply ne_iff_lt_or_gt.mp at c
        cases c with
        | inl h => exact (ne_iff_lt_or_gt.mpr (.inl (hu O.1.heap[j].var O.1.heap[i].var h ⟨j, relabel_reachable_iff.mp hp, rfl⟩ ⟨i, relabel_reachable_iff.mp hq, rfl⟩))) ha
        | inr h => exact (ne_iff_lt_or_gt.mpr (.inr (hu O.1.heap[i].var O.1.heap[j].var h ⟨i, relabel_reachable_iff.mp hq, rfl⟩ ⟨j, relabel_reachable_iff.mp hp, rfl⟩))) ha
      · simp only [orelabel, relabel, OBdd.subBdd_eq] at hb
        simp_rw [← relabel.eq_1] at hb
        rw [brelabel_low (o := OBdd.ordered_of_reachable (relabel_reachable_iff.mp hp)) hf (by simp_all)] at hb
        rw [brelabel_low (o := OBdd.ordered_of_reachable (relabel_reachable_iff.mp hq)) hf (by simp_all)] at hb
        simp only [OBdd.low_eq] at hb ⊢
        have helplj : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node j } : Bdd n m).low rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help1
          apply Bdd.usesVar_of_low_usesVar hx
        have helpli : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node i } : Bdd n m).low rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help2
          apply Bdd.usesVar_of_low_usesVar hx
        rw [relabel_toTree_relabel' (o := Bdd.low_ordered _ (O.ordered_of_reachable (relabel_reachable_iff.mp hp))) hf (by simp_all)] at hb
        rw [relabel_toTree_relabel' (o := Bdd.low_ordered _ (O.ordered_of_reachable (relabel_reachable_iff.mp hq))) hf (by simp_all)] at hb
        rw [DecisionTree.relabel_injective hb]
        intro ii ii' hii hii' hfi
        rw [← OBdd.toTree_usesVar] at hii hii'
        contrapose hfi
        cases ne_iff_lt_or_gt.mp hfi <;> grind only
      · simp only [orelabel, relabel, OBdd.subBdd_eq] at hc
        simp_rw [← relabel.eq_1] at hc
        rw [brelabel_high (o := O.ordered_of_reachable (relabel_reachable_iff.mp hp)) hf (by simp_all)] at hc
        rw [brelabel_high (o := O.ordered_of_reachable (relabel_reachable_iff.mp hq)) hf (by simp_all)] at hc
        simp only [OBdd.high_eq] at hc ⊢
        have helphj : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node j } : Bdd n m).high rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help1
          apply Bdd.usesVar_of_high_usesVar hx
        have helphi : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node i } : Bdd n m).high rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help2
          apply Bdd.usesVar_of_high_usesVar hx
        rw [relabel_toTree_relabel' (o := Bdd.high_ordered _ (O.ordered_of_reachable (relabel_reachable_iff.mp hp))) hf (by simp_all)] at hc
        rw [relabel_toTree_relabel' (o := Bdd.high_ordered _ (O.ordered_of_reachable (relabel_reachable_iff.mp hq))) hf (by simp_all)] at hc
        rw [DecisionTree.relabel_injective hc]
        intro ii ii' hii hii' hfi
        rw [← OBdd.toTree_usesVar] at hii hii'
        contrapose hfi
        cases ne_iff_lt_or_gt.mp hfi <;>
        grind only

public lemma orelabel_reduced {O : OBdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'} :
    O.Reduced → (orelabel O hf hu).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact relabel_preserves_noRedundancy r1
  · rintro _ _ sim
    exact r2 (orelabel_preserves_similarRP sim)

@[simp]
lemma relabel_id {B : Bdd n m} : relabel (f := id) (by simp) B = B := by
  simp only [id_eq, relabel, relabel_heap]
  congr
  ext i hi
  simp only [Vector.getElem_map, relabel_node, id_eq, Fin.eta]

@[simp]
public lemma orelabel_id {O : OBdd n m} : orelabel O (f := id) (by simp) (fun _ _ _ _ _ ↦ by simpa) = O := by
  simp [orelabel]

end Relabel
