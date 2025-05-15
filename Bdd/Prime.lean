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
    | low  _ => left;  simpa [prime, prime_heap]
    | high _ => right; simpa [prime, prime_heap]
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

def unprime_node (p : Fin n) : Node n m → Node (n - p) m
  | ⟨var, low, high⟩ => ⟨⟨var.1 - p.1, by omega⟩, low, high⟩

def unprime_heap (p : Fin n) : Vector (Node n m) m → Vector (Node (n - p) m) m := Vector.map (unprime_node p)

def unprime (p : Fin n) : Bdd n m → Bdd (n - p) m
  | ⟨heap, root⟩ => ⟨unprime_heap p heap, root⟩

lemma unprime_edge_iff {B : Bdd n m} {x y : Pointer m} : Edge B.heap x y ↔ Edge (unprime p B).heap x y := by
  constructor
  · intro e
    cases e with
    | low  _ => left;  simpa [unprime, unprime_heap]
    | high _ => right; simpa [unprime, unprime_heap]
  · intro e
    cases e with
    | low  _ => left;  simp_all [unprime, unprime_heap]; assumption
    | high _ => right; simp_all [unprime, unprime_heap]; assumption

lemma unprime_reachable_iff {B : Bdd n m} : Pointer.Reachable B.heap B.root x ↔ Pointer.Reachable (unprime p B).heap (unprime p B).root x := by
  constructor
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (unprime_edge_iff.mp e)
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (unprime_edge_iff.mpr e)

lemma unprime_mayPrecede {B : Bdd n m} {x y : Pointer m} {p : Fin n} : p ≤ x.toVar B.heap → Pointer.MayPrecede B.heap x y → Pointer.MayPrecede (unprime p B).heap x y := by
  intro hp h
  cases x with
  | terminal _ => absurd h; exact Pointer.not_terminal_MayPrecede
  | node _ =>
    cases y with
    | terminal _ => apply Pointer.MayPrecede_node_terminal
    | node _ =>
      simp only [Pointer.MayPrecede, unprime, unprime_heap, Pointer.toVar] at h
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff] at h
      simp only [Pointer.MayPrecede, unprime, unprime_heap, Pointer.toVar]
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_map, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff]
      simp only [unprime_node]
      simp only [Fin.eta, Fin.mk_lt_mk, add_lt_add_iff_right, Fin.val_fin_lt]
      refine Nat.sub_lt_sub_right ?_ h
      simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Pointer.toVar_node_eq, Fin.getElem_fin, Fin.castSucc_le_castSucc_iff] at hp
      exact hp

lemma unprime_relevantMayPrecede {B : Bdd n m} {x y : Pointer m} {hx : Pointer.Reachable (unprime p B).heap (unprime p B).root x} {hy : Pointer.Reachable (unprime p B).heap (unprime p B).root y} :
    p ≤ x.toVar B.heap → B.RelevantMayPrecede ⟨x, unprime_reachable_iff.mpr hx⟩ ⟨y, unprime_reachable_iff.mpr hy⟩ → (unprime p B).RelevantMayPrecede ⟨x, hx⟩ ⟨y, hy⟩ := unprime_mayPrecede

lemma unprime_relevantEdge {B : Bdd n m} {x y : Pointer m} {hx : Pointer.Reachable (unprime p B).heap (unprime p B).root x} {hy : Pointer.Reachable (unprime p B).heap (unprime p B).root y} :
    (unprime p B).RelevantEdge ⟨x, hx⟩ ⟨y, hy⟩ → B.RelevantEdge ⟨x, unprime_reachable_iff.mpr hx⟩ ⟨y, unprime_reachable_iff.mpr hy⟩ := by
  intro h
  simp_all only [Bdd.RelevantEdge, unprime, unprime_heap]
  cases h with
  | low _ =>
    left
    simp_all [unprime_node]
    assumption
  | high _ =>
    right
    simp_all [unprime_node]
    assumption

lemma unprime_preserves_ordered {B : Bdd n m} {p : Fin n} : p ≤ B.var → Bdd.Ordered B → Bdd.Ordered (unprime p B) := by
  intro hp ho
  rintro ⟨x, hx⟩ _ hxy
  apply unprime_relevantMayPrecede
  · simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hp
    simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc]
    trans Pointer.toVar B.heap B.root
    exact hp
    apply Pointer.mayPrecede_of_reachable ho (unprime_reachable_iff.mpr hx)
  · apply ho
    exact unprime_relevantEdge hxy

def ounprime (p : Fin n) (O : OBdd n m) : p ≤ O.1.var → OBdd (n - p) m
  | hp => ⟨unprime p O.1, unprime_preserves_ordered hp O.2⟩

lemma ounprime_low {O : OBdd n m} {h : O.1.root = .node j} {p: Fin n} {hp : p ≤ O.1.var} :
    (OBdd.low (ounprime p O hp) h) = ounprime p (O.low h) (by trans O.1.var; exact hp; apply le_of_lt OBdd.var_lt_low_var) := by
  rcases O with ⟨B, o⟩
  simp only [OBdd.low]
  congr
  simp only [ounprime, unprime, unprime_heap, Bdd.low_heap_eq_heap]
  simp only at h
  simp_rw [h]
  simp only [Bdd.low]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma ounprime_high {O : OBdd n m} {h : O.1.root = .node j} {p: Fin n} {hp : p ≤ O.1.var} :
    (OBdd.high (ounprime p O hp) h) = ounprime p (O.high h) (by trans O.1.var; exact hp; apply le_of_lt OBdd.var_lt_high_var) := by
  rcases O with ⟨B, o⟩
  simp only [OBdd.high]
  congr
  simp only [ounprime, unprime, unprime_heap, Bdd.high_heap_eq_heap]
  simp only at h
  simp_rw [h]
  simp only [Bdd.high]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma bunprime_low {n m j} {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {p: Fin n} {hp : p ≤ B.var} :
    (OBdd.low ⟨unprime p B, unprime_preserves_ordered hp o⟩ h) =
    ⟨unprime p (OBdd.low ⟨B, o⟩ h).1,
     unprime_preserves_ordered
      (by trans B.var; exact hp; apply le_of_lt; rw [show B.var = (⟨B, o⟩ : OBdd n m).1.var by rfl]; apply OBdd.var_lt_low_var)
      (OBdd.low ⟨B, o⟩ h).2⟩ := by
  simp only [OBdd.low]
  congr
  simp only [unprime, unprime_heap, Bdd.low_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.low]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma bunprime_high {n m j} {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {p: Fin n} {hp : p ≤ B.var} :
    (OBdd.high ⟨unprime p B, unprime_preserves_ordered hp o⟩ h) =
    ⟨unprime p (OBdd.high ⟨B, o⟩ h).1,
     unprime_preserves_ordered
      (by trans B.var; exact hp; apply le_of_lt; rw [show B.var = (⟨B, o⟩ : OBdd n m).1.var by rfl]; apply OBdd.var_lt_high_var)
      (OBdd.high ⟨B, o⟩ h).2⟩ := by
  simp only [OBdd.high]
  congr
  simp only [unprime, unprime_heap, Bdd.high_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.high]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

theorem ounprime_evaluate (O : OBdd n m) {p : Fin n} (hp : p ≤ O.1.var) {I : Vector Bool (n - p)} {J : Vector Bool p} : OBdd.evaluate (ounprime p O hp) I = O.evaluate (Vector.cast (by omega) (J ++ I)) := by
  simp only [ounprime]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [unprime]
    rw [OBdd.evaluate_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.evaluate_terminal]
    simp
  | node j =>
    rw [OBdd.evaluate_node'' O_root_def]
    have that : (⟨(unprime p O.1), unprime_preserves_ordered hp O.2⟩ : OBdd _ _).1.root = Pointer.node j := O_root_def
    rw [OBdd.evaluate_node'' that]
    simp only
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      simp only [unprime, unprime_heap, Fin.getElem_fin, Vector.getElem_map, unprime_node]
      simp only [Fin.eta]
      rw [Vector.getElem_cast]
      rw [Vector.getElem_append]
      split
      next contra =>
        absurd contra
        simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hp
        rw [O_root_def] at hp
        simp at hp
        omega
      next => rfl
    · have := ounprime_evaluate (O.high O_root_def) (I := I) (J := J)
      rw [← this]
      rw [← ounprime_high (hp := hp)]
      rfl
    · have := ounprime_evaluate (O.low O_root_def) (I := I) (J := J)
      rw [← this]
      rw [← ounprime_low (hp := hp)]
      rfl
termination_by O

def tunprime (p : Fin n) (T : DecisionTree n) : T.lowerBoundedBy p → DecisionTree (n - p) := fun r ↦
  match T with
  | .leaf b => .leaf b
  | .branch i l h => .branch ⟨i.1 - p, by omega⟩ (tunprime p l (DecisionTree.lowerBoundedBy_low r)) (tunprime p h (DecisionTree.lowerBoundedBy_high r))

lemma tunprime_injective : tunprime x T1 h1 = tunprime x T2 h2 → T1 = T2 := by
  intro h
  cases T1 with
  | leaf _ =>
    cases T2 with
    | leaf _ => simp only [tunprime] at h; simp_all
    | branch _ _ _ => contradiction
  | branch v1 l1 r1 =>
    cases T2 with
    | leaf _ => contradiction
    | branch v2 l2 r2 =>
      simp only [tunprime] at h
      injection h with a b c
      rw [tunprime_injective b, tunprime_injective c]
      simp_all only [Fin.mk.injEq, DecisionTree.branch.injEq, and_self, and_true]
      have : x.1 ≤ v1.1 := by
        cases h1 with
        | node _ _ _ => assumption
      have : x.1 ≤ v2.1 := by
        cases h2 with
        | node _ _ _ => assumption
      omega

lemma unprime_low {O : OBdd n m} {h : O.1.root = .node j} {p : Fin n} {hp : p ≤ O.1.var} :
   (OBdd.low ⟨unprime p O.1, unprime_preserves_ordered hp O.2⟩ h) = ⟨unprime p (O.low h).1, unprime_preserves_ordered (by trans O.1.var; exact hp; apply le_of_lt; apply OBdd.var_lt_low_var) (O.low h).2⟩ := by
  simp only [OBdd.low]
  congr
  simp only [unprime, unprime_heap, Bdd.low_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.low]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma unprime_high {O : OBdd n m} {h : O.1.root = .node j} {p : Fin n} {hp : p ≤ O.1.var} :
   (OBdd.high ⟨unprime p O.1, unprime_preserves_ordered hp O.2⟩ h) = ⟨unprime p (O.high h).1, unprime_preserves_ordered (by trans O.1.var; exact hp; apply le_of_lt; apply OBdd.var_lt_high_var) (O.high h).2⟩ := by
  simp only [OBdd.high]
  congr
  simp only [unprime, unprime_heap, Bdd.high_heap_eq_heap]
  simp_rw [h]
  simp only [Bdd.high]
  congr 1
  simp_all only [Fin.getElem_fin, Vector.getElem_map]
  rfl

lemma unprime_toTree_tunprime' {O : OBdd n m} {p : Fin n} {hp : p ≤ O.1.var} :
    OBdd.toTree ⟨unprime p O.1, unprime_preserves_ordered hp O.2⟩ = tunprime p (OBdd.toTree O) (OBdd.toTree_lowerBoundedBy_var hp) := by
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [unprime]
    simp_rw [OBdd.toTree_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.toTree_terminal]
    simp [tunprime]
  | node _ =>
    simp_rw [OBdd.toTree_node O_root_def]
    rw [OBdd.toTree_node (by trans O.1.root; rfl; exact O_root_def)]
    simp only [Fin.getElem_fin]
    congr 1
    · simp only [unprime, unprime_heap, Vector.getElem_map, unprime_node, Fin.eta, Bdd.Ordered.eq_1, Fin.mk.injEq, Nat.add_right_cancel_iff]
      rfl
    · have := unprime_toTree_tunprime' (O := (O.low O_root_def)) (p := p) (hp := (by trans O.1.var; exact hp; apply le_of_lt OBdd.var_lt_low_var))
      rw [← unprime_low (hp := hp)] at this
      exact this
    · have := unprime_toTree_tunprime' (O := (O.high O_root_def)) (p := p) (hp := (by trans O.1.var; exact hp; apply le_of_lt OBdd.var_lt_high_var))
      rw [← unprime_high (hp := hp)] at this
      exact this
termination_by O

lemma unprime_toTree_tunprime {B : Bdd n m} {o : B.Ordered} {p : Fin n} {hp : p ≤ B.var} :
    OBdd.toTree ⟨unprime p B, unprime_preserves_ordered hp o⟩ = tunprime p (OBdd.toTree ⟨B, o⟩) (OBdd.toTree_lowerBoundedBy_var hp) := by
  let O : OBdd n m := ⟨B, o⟩
  have : B = O.1 := rfl
  simp_rw [this]
  exact unprime_toTree_tunprime' (hp := hp)

lemma unprime_preserves_noRedundancy {B : Bdd n m} : B.NoRedundancy → (unprime p B).NoRedundancy := by
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
      simp only [unprime, unprime_heap, Fin.getElem_fin, unprime_node] at red
      apply hnr ⟨p, unprime_reachable_iff.mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all only [Vector.getElem_map, Fin.getElem_fin]
      simp only [unprime, unprime_heap, Fin.getElem_fin, unprime_node] at red
      exact red

lemma ounprime_preserves_similarRP {O : OBdd n m} {p q : Pointer m} {hx}
    {hp : Pointer.Reachable (ounprime x O hx).1.heap (ounprime x O hx).1.root p} {hq : Pointer.Reachable (ounprime x O hx).1.heap (ounprime x O hx).1.root q} :
    (ounprime x O hx).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ → O.SimilarRP ⟨p, unprime_reachable_iff.mpr hp⟩ ⟨q, unprime_reachable_iff.mpr hq⟩ := by
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
      simp only [ounprime, unprime, unprime_heap, Vector.getElem_map, unprime_node, Fin.eta, Fin.mk.injEq, Nat.add_right_cancel_iff] at ha
      conv =>
        lhs
        rw [OBdd.toTree_node rfl]
      conv =>
        rhs
        rw [OBdd.toTree_node rfl]
      have this : x ≤ O.1.heap[j].var := by
        apply Fin.le_iff_val_le_val.mpr
        trans O.1.var.1
        · simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hx
          simp only [Nat.succ_eq_add_one, Bdd.var]
          exact hx
        · have := Pointer.mayPrecede_of_reachable O.2 (unprime_reachable_iff.mpr hp)
          simp only [Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc] at this
          simp only [Nat.succ_eq_add_one, Bdd.var, Fin.getElem_fin, ge_iff_le]
          exact this
      have that : x ≤ O.1.heap[i].var := by
        apply Fin.le_iff_val_le_val.mpr
        trans O.1.var.1
        · simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hx
          simp only [Nat.succ_eq_add_one, Bdd.var]
          exact hx
        · have := Pointer.mayPrecede_of_reachable O.2 (unprime_reachable_iff.mpr hq)
          simp only [Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc] at this
          simp only [Nat.succ_eq_add_one, Bdd.var, Fin.getElem_fin, ge_iff_le]
          exact this
      congr 1
      · simp only
        simp_all only [Fin.getElem_fin]
        suffices s : O.1.heap[j.1].var - x.1 = O.1.heap[i.1].var - x.1 by omega
        exact ha
      · simp only [ounprime] at hb
        simp only [unprime] at hb
        simp_rw [← unprime.eq_1] at hb
        conv at hb =>
          lhs
          rw [bunprime_low (h := rfl) (hp := (by simp; exact this)) (o := Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hp))]
        conv at hb =>
          rhs
          rw [bunprime_low (h := rfl) (hp := (by simp; exact that)) (o := Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hq))]
        simp only [OBdd.low] at hb
        simp only [OBdd.low]
        have this : x ≤ Pointer.toVar O.1.heap O.1.heap[j].low := by
          apply Fin.le_iff_val_le_val.mpr
          trans O.1.var.1
          · simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hx
            simp only [Nat.succ_eq_add_one, Bdd.var]
            simp_all
            exact hx
          · have := Pointer.mayPrecede_of_reachable O.2 (unprime_reachable_iff.mpr hp)
            simp only [Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc] at this
            simp only [Nat.succ_eq_add_one, Bdd.var, Fin.getElem_fin, ge_iff_le]
            simp_all
            apply Pointer.mayPrecede_of_reachable O.2
            trans .node j
            exact (unprime_reachable_iff.mpr hp)
            apply Bdd.reachable_of_edge
            left
            rfl
        have that : x ≤ Pointer.toVar O.1.heap O.1.heap[i].low := by
          apply Fin.le_iff_val_le_val.mpr
          trans O.1.var.1
          · simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hx
            simp only [Nat.succ_eq_add_one, Bdd.var]
            simp_all
            exact hx
          · have := Pointer.mayPrecede_of_reachable O.2 (unprime_reachable_iff.mpr hq)
            simp only [Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc] at this
            simp only [Nat.succ_eq_add_one, Bdd.var, Fin.getElem_fin, ge_iff_le]
            simp_all
            apply Pointer.mayPrecede_of_reachable O.2
            trans .node i
            exact (unprime_reachable_iff.mpr hq)
            apply Bdd.reachable_of_edge
            left
            rfl
        conv at hb =>
          lhs
          rw [unprime_toTree_tunprime (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hp)))
                                      (hp := (by exact this))]
        conv at hb =>
          rhs
          rw [unprime_toTree_tunprime (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hq)))
                                      (hp := (by exact that))]
        rw [tunprime_injective hb]
      · simp only [ounprime] at hc
        simp only [unprime] at hc
        simp_rw [← unprime.eq_1] at hc
        conv at hc =>
          lhs
          rw [bunprime_high (h := rfl) (hp := (by simp; exact this)) (o := Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hp))]
        conv at hc =>
          rhs
          rw [bunprime_high (h := rfl) (hp := (by simp; exact that)) (o := Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hq))]
        simp only [OBdd.high] at hc
        simp only [OBdd.high]
        have this : x ≤ Pointer.toVar O.1.heap O.1.heap[j].high := by
          apply Fin.le_iff_val_le_val.mpr
          trans O.1.var.1
          · simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hx
            simp only [Nat.succ_eq_add_one, Bdd.var]
            simp_all
            exact hx
          · have := Pointer.mayPrecede_of_reachable O.2 (unprime_reachable_iff.mpr hp)
            simp only [Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc] at this
            simp only [Nat.succ_eq_add_one, Bdd.var, Fin.getElem_fin, ge_iff_le]
            simp_all
            apply Pointer.mayPrecede_of_reachable O.2
            trans .node j
            exact (unprime_reachable_iff.mpr hp)
            apply Bdd.reachable_of_edge
            right
            rfl
        have that : x ≤ Pointer.toVar O.1.heap O.1.heap[i].high := by
          apply Fin.le_iff_val_le_val.mpr
          trans O.1.var.1
          · simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var] at hx
            simp only [Nat.succ_eq_add_one, Bdd.var]
            simp_all
            exact hx
          · have := Pointer.mayPrecede_of_reachable O.2 (unprime_reachable_iff.mpr hq)
            simp only [Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc] at this
            simp only [Nat.succ_eq_add_one, Bdd.var, Fin.getElem_fin, ge_iff_le]
            simp_all
            apply Pointer.mayPrecede_of_reachable O.2
            trans .node i
            exact (unprime_reachable_iff.mpr hq)
            apply Bdd.reachable_of_edge
            right
            rfl
        conv at hc =>
          lhs
          rw [unprime_toTree_tunprime (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hp)))
                                      (hp := (by exact this))]
        conv at hc =>
          rhs
          rw [unprime_toTree_tunprime (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (unprime_reachable_iff.mpr hq)))
                                      (hp := (by exact that))]
        rw [tunprime_injective hc]

lemma ounprime_reduced {O : OBdd n m} {p : Fin n} {hp : p ≤ O.1.var} : O.Reduced → (ounprime p O hp).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact unprime_preserves_noRedundancy r1
  · rintro _ _ sim; exact r2 (ounprime_preserves_similarRP sim)

end Prime
