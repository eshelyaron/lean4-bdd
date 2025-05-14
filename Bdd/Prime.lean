import Bdd.Basic

namespace Prime

def prime_node (p : Nat): Node n m → Node (n + p) m
  | ⟨var, low, high⟩ => ⟨⟨var.1 + p, (add_lt_add_iff_right p).mpr (Fin.is_lt var)⟩, low, high⟩

def prime_heap (p : Nat): Vector (Node n m) m → Vector (Node (n + p) m) m := Vector.map (prime_node p)

def prime (p : Nat) : Bdd n m → Bdd (n + p) m
  | ⟨heap, root⟩ => ⟨prime_heap p heap, root⟩

lemma prime_edge_iff {B : Bdd n m} {x y : Pointer m} : Edge B.heap x y ↔ Edge (prime p B).heap x y := by
  constructor
  · intro e
    cases e with
    | low  _ => left;  simpa [prime, prime_heap, prime_node]
    | high _ => right; simpa [prime, prime_heap, prime_node]
  · intro e
    cases e with
    | low  _ => left;  simp_all [prime, prime_heap, prime_node]; assumption
    | high _ => right; simp_all [prime, prime_heap, prime_node]; assumption

lemma prime_reachable_iff {B : Bdd n m} : Pointer.Reachable B.heap B.root x ↔ Pointer.Reachable (prime p B).heap (prime p B).root x := by
  constructor
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (prime_edge_iff.mp e)
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (prime_edge_iff.mpr e)

lemma prime_mayPrecede_iff {B : Bdd n m} {x y : Pointer m}: Pointer.MayPrecede B.heap x y ↔ Pointer.MayPrecede (prime p B).heap x y := by
  constructor
  · intro h
    cases x with
    | terminal _ => absurd h; exact Pointer.not_terminal_MayPrecede
    | node _ =>
      cases y with
      | terminal _ => apply Pointer.MayPrecede_node_terminal
      | node _ =>
        simp only [Pointer.MayPrecede, prime, prime_heap, Pointer.toVar] at h
        simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff] at h
        simp only [Pointer.MayPrecede, prime, prime_heap, Pointer.toVar]
        simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_map, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff]
        simp only [prime_node]
        simp only [Fin.eta, Fin.mk_lt_mk, add_lt_add_iff_right, Fin.val_fin_lt]
        exact h
  · intro h
    cases x with
    | terminal _ => absurd h; exact Pointer.not_terminal_MayPrecede
    | node _ =>
      cases y with
      | terminal _ => apply Pointer.MayPrecede_node_terminal
      | node _ =>
        simp only [Pointer.MayPrecede, prime, prime_heap, Pointer.toVar]
        simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff]
        simp only [Pointer.MayPrecede, prime, prime_heap, Pointer.toVar] at h
        simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_map, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff] at h
        simp only [prime_node] at h
        simp only [Fin.eta, Fin.mk_lt_mk, add_lt_add_iff_right, Fin.val_fin_lt] at h
        exact h

lemma prime_relevantMayPrecede {B : Bdd n m} {x y : Pointer m} {hx : Pointer.Reachable (prime p B).heap (prime p B).root x} {hy : Pointer.Reachable (prime p B).heap (prime p B).root y} :
    B.RelevantMayPrecede ⟨x, prime_reachable_iff.mpr hx⟩ ⟨y, prime_reachable_iff.mpr hy⟩ → (prime p B).RelevantMayPrecede ⟨x, hx⟩ ⟨y, hy⟩ := prime_mayPrecede_iff.mp

lemma prime_relevantEdge {B : Bdd n m} {x y : Pointer m} {hx : Pointer.Reachable (prime p B).heap (prime p B).root x} {hy : Pointer.Reachable (prime p B).heap (prime p B).root y} :
    (prime p B).RelevantEdge ⟨x, hx⟩ ⟨y, hy⟩ → B.RelevantEdge ⟨x, prime_reachable_iff.mpr hx⟩ ⟨y, prime_reachable_iff.mpr hy⟩ := by
  intro h
  simp_all only [Bdd.RelevantEdge, prime, prime_heap]
  cases h with
  | low _ =>
    left
    simp_all [prime_node]
    assumption
  | high _ =>
    right
    simp_all [prime_node]
    assumption

lemma prime_preserves_ordered : Bdd.Ordered B → Bdd.Ordered (prime p B) := by
  intro ho
  rintro _ _ hxy
  apply prime_relevantMayPrecede
  apply ho
  exact prime_relevantEdge hxy

def oprime p : OBdd n m → OBdd (n + p) m
  | O => ⟨prime p O.1, prime_preserves_ordered O.2⟩

lemma oprime_low {n m j p} {O : OBdd n m} {h : O.1.root = .node j} : (OBdd.low (oprime p O) h) = oprime p (O.low h) := by
  rcases O with ⟨B, o⟩
  simp only [OBdd.low]
  congr
  simp only [oprime, prime, prime_heap, Bdd.low_heap_eq_heap]
  simp only at h
  simp_rw [h]
  simp only [Bdd.low]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma oprime_high {n m j p} {O : OBdd n m} {h : O.1.root = .node j} : (OBdd.high (oprime p O) h) = oprime p (O.high h) := by
  rcases O with ⟨B, o⟩
  simp only [OBdd.high]
  congr
  simp only [oprime, prime, prime_heap, Bdd.high_heap_eq_heap]
  simp only at h
  simp_rw [h]
  simp only [Bdd.high]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma bprime_low {n m j p} {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} : (OBdd.low ⟨prime p B, prime_preserves_ordered o⟩ h) = ⟨prime p (OBdd.low ⟨B, o⟩ h).1, prime_preserves_ordered (OBdd.low ⟨B, o⟩ h).2⟩ := by
  simp only [OBdd.low]
  congr
  simp only [prime, prime_heap, Bdd.low_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.low]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma bprime_high {n m j p} {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} : (OBdd.high ⟨prime p B, prime_preserves_ordered o⟩ h) = ⟨prime p (OBdd.high ⟨B, o⟩ h).1, prime_preserves_ordered (OBdd.high ⟨B, o⟩ h).2⟩ := by
  simp only [OBdd.high]
  congr
  simp only [prime, prime_heap, Bdd.high_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.high]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma prime_low {n m j p} {O : OBdd n m} {h : O.1.root = .node j} : (OBdd.low ⟨prime p O.1, prime_preserves_ordered O.2⟩ h) = ⟨prime p (O.low h).1, prime_preserves_ordered (O.low h).2⟩ := by
  simp only [OBdd.low]
  congr
  simp only [prime, prime_heap, Bdd.low_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.low]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma prime_high {n m j p} {O : OBdd n m} {h : O.1.root = .node j} : (OBdd.high ⟨prime p O.1, prime_preserves_ordered O.2⟩ h) = ⟨prime p (O.high h).1, prime_preserves_ordered (O.high h).2⟩ := by
  simp only [OBdd.high]
  congr
  simp only [prime, prime_heap, Bdd.high_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.high]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

theorem oprime_evaluate (O : OBdd n m) : OBdd.evaluate (oprime p O) I = O.evaluate (Vector.cast (show n + p - p = n from Eq.symm (Nat.eq_sub_of_add_eq rfl)) (I.drop p)) := by
  simp only [oprime]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [prime]
    rw [OBdd.evaluate_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.evaluate_terminal]
    simp
  | node j =>
    rw [OBdd.evaluate_node'' O_root_def]
    have that : (⟨(prime p O.1), prime_preserves_ordered O.2⟩ : OBdd _ _).1.root = Pointer.node j := O_root_def
    rw [OBdd.evaluate_node'' that]
    simp only
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      simp only [prime, prime_heap, Fin.getElem_fin, Vector.getElem_map, prime_node]
      simp only [Fin.eta]
      rw [Vector.getElem_cast]
      symm
      simp_rw [add_comm]
      apply Vector.getElem_drop
    · have := oprime_evaluate (O.high O_root_def) (I := I)
      rw [← this]
      rw [← oprime_high]
      rfl
    · have := oprime_evaluate (O.low O_root_def) (I := I)
      rw [← this]
      rw [← oprime_low]
      rfl
termination_by O

theorem prime_evaluate (O : OBdd n m) : OBdd.evaluate ⟨prime p O.1, prime_preserves_ordered O.2⟩ I = O.evaluate (Vector.cast (show n + p - p = n from Eq.symm (Nat.eq_sub_of_add_eq rfl)) (I.drop p)) := by
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [prime]
    rw [OBdd.evaluate_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.evaluate_terminal]
    simp
  | node j =>
    rw [OBdd.evaluate_node'' O_root_def]
    have that : (⟨(prime p O.1), prime_preserves_ordered O.2⟩ : OBdd _ _).1.root = Pointer.node j := O_root_def
    rw [OBdd.evaluate_node'' that]
    simp only
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      simp only [prime, prime_heap, Fin.getElem_fin, Vector.getElem_map, prime_node]
      simp only [Fin.eta]
      rw [Vector.getElem_cast]
      symm
      simp_rw [add_comm]
      apply Vector.getElem_drop
    · have := prime_evaluate (O.high O_root_def) (I := I)
      rw [← this]
      rw [← prime_high]
    · have := prime_evaluate (O.low O_root_def) (I := I)
      rw [← this]
      rw [← prime_low]
termination_by O

lemma prime_preserves_noRedundancy {B : Bdd n m} : B.NoRedundancy → (prime p B).NoRedundancy := by
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
      simp only [prime, prime_heap, Fin.getElem_fin, prime_node] at red
      apply hnr ⟨p, prime_reachable_iff.mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all only [Vector.getElem_map, Fin.getElem_fin]
      simp only [prime, prime_heap, Fin.getElem_fin, prime_node] at red
      exact red

def tprime p : DecisionTree n → DecisionTree (n + p)
  | .leaf b => .leaf b
  | .branch i l h => .branch ⟨i.1 + p, by omega⟩ (tprime p l) (tprime p h)

lemma tprime_injective : Function.Injective (tprime (n := n) p) := by
  intro x y hxy
  cases x with
  | leaf _ =>
    cases y with
    | leaf _ => simp only [tprime] at hxy; simp_all
    | branch _ _ _ => contradiction
  | branch _ _ _ =>
    cases y with
    | leaf _ => contradiction
    | branch _ _ _ =>
      simp only [tprime] at hxy
      injection hxy with a b c
      rw [tprime_injective b, tprime_injective c]
      aesop

lemma prime_toTree_tprime' {O : OBdd n m} :
    OBdd.toTree ⟨prime p O.1, prime_preserves_ordered O.2⟩ = tprime p (OBdd.toTree O) := by
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [prime]
    rw [OBdd.toTree_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.toTree_terminal]
    simp [tprime]
  | node _ =>
    -- simp only [prime]
    rw [OBdd.toTree_node O_root_def]
    rw [OBdd.toTree_node (by trans O.1.root; rfl; exact O_root_def)]
    simp only [Fin.getElem_fin]
    congr 1
    · simp only [prime, prime_heap, Vector.getElem_map, prime_node, Fin.eta, Bdd.Ordered.eq_1, Fin.mk.injEq, Nat.add_right_cancel_iff]
      rfl
    · have := prime_toTree_tprime' (O := (O.low O_root_def)) (p := p)
      rw [← prime_low] at this
      exact this
    · have := prime_toTree_tprime' (O := (O.high O_root_def)) (p := p)
      rw [← prime_high] at this
      exact this
termination_by O

lemma prime_toTree_tprime {B : Bdd n m} {o : B.Ordered} :
    OBdd.toTree ⟨prime p B, prime_preserves_ordered o⟩ = tprime p (OBdd.toTree ⟨B, o⟩) := by
  let O : OBdd n m := ⟨B, o⟩
  have : B = O.1 := rfl
  simp_rw [this]
  exact prime_toTree_tprime'

lemma oprime_preserves_similarRP {O : OBdd n m} {p q : Pointer m} {hp : Pointer.Reachable (oprime x O).1.heap (oprime x O).1.root p} {hq : Pointer.Reachable (oprime x O).1.heap (oprime x O).1.root q} :
    (oprime x O).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ → O.SimilarRP ⟨p, prime_reachable_iff.mpr hp⟩ ⟨q, prime_reachable_iff.mpr hq⟩ := by
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
      simp only [oprime, prime, prime_heap, Vector.getElem_map, prime_node, Fin.eta, Fin.mk.injEq, Nat.add_right_cancel_iff] at ha
      conv =>
        lhs
        rw [OBdd.toTree_node rfl]
      conv =>
        rhs
        rw [OBdd.toTree_node rfl]
      congr 1
      · simp only
        exact Fin.eq_of_val_eq ha
      · simp only [oprime] at hb
        simp only [prime] at hb
        simp_rw [← prime.eq_1] at hb
        conv at hb =>
          lhs
          rw [bprime_low (h := rfl) (o := Bdd.ordered_of_reachable (prime_reachable_iff.mpr hp))]
        conv at hb =>
          rhs
          rw [bprime_low (h := rfl) (o := Bdd.ordered_of_reachable (prime_reachable_iff.mpr hq))]
        simp only [OBdd.low] at hb
        simp only [OBdd.low]
        conv at hb =>
          lhs
          rw [prime_toTree_tprime (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (prime_reachable_iff.mpr hp)))]
        conv at hb =>
          rhs
          rw [prime_toTree_tprime (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (prime_reachable_iff.mpr hq)))]
        rw [tprime_injective hb]
      · simp only [oprime] at hc
        simp only [prime] at hc
        simp_rw [← prime.eq_1] at hc
        conv at hc =>
          lhs
          rw [bprime_high (h := rfl) (o := Bdd.ordered_of_reachable (prime_reachable_iff.mpr hp))]
        conv at hc =>
          rhs
          rw [bprime_high (h := rfl) (o := Bdd.ordered_of_reachable (prime_reachable_iff.mpr hq))]
        simp only [OBdd.high] at hc
        simp only [OBdd.high]
        conv at hc =>
          lhs
          rw [prime_toTree_tprime (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (prime_reachable_iff.mpr hp)))]
        conv at hc =>
          rhs
          rw [prime_toTree_tprime (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (prime_reachable_iff.mpr hq)))]
        rw [tprime_injective hc]

lemma oprime_reduced {O : OBdd n m} : O.Reduced → (oprime p O).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact prime_preserves_noRedundancy r1
  · rintro _ _ sim; exact r2 (oprime_preserves_similarRP sim)

end Prime
