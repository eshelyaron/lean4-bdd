import Bdd.Basic
import Bdd.Lift
import Std.Data.HashMap.Lemmas

namespace Apply

private def RawPointer := Bool ⊕ Nat

private structure RawNode (n) where
  va : Fin n
  lo : RawPointer
  hi : RawPointer

private def RawPointer.Bounded (m : Nat) (p : RawPointer) := ∀ {i}, p = .inr i → i < m

private def RawPointer.bounded_of_le {p : RawPointer} (hm : p.Bounded m) (h : m ≤ m') : p.Bounded m' := by
  intro i hi
  cases hp : p with
  | inl val => simp_all
  | inr val =>
    have := hm hp
    simp_all
    injection hi with heq
    subst heq
    omega

private def RawPointer.cook (p : RawPointer) (h : p.Bounded m) : Pointer m :=
  match p with
  | .inl b => .terminal b
  | .inr i => .node ⟨i, h rfl⟩

private lemma RawPointer.cook_equiv {h1 : Apply.RawPointer.Bounded m1 p} {h2 : Apply.RawPointer.Bounded m2 p} : Pointer.equiv (RawPointer.cook p h1) (RawPointer.cook p h2) := by
  simp only [Pointer.equiv]
  constructor
  · intro b hb
    cases p <;> simp_all [RawPointer.cook]
  · intro j hj
    cases p with
    | inl val => contradiction
    | inr val =>
      simp only [Bounded] at h1 h2
      simp only [cook, Pointer.node.injEq] at hj
      rw [Fin.eq_mk_iff_val_eq] at hj
      simp only at hj
      subst hj
      use ⟨j.1, h2 rfl⟩
      simp [RawPointer.cook]

private def RawPointer.fromPointer : Pointer m → RawPointer
  | .terminal b => .inl b
  | .node j => .inr j.1

private def RawNode.Bounded (m : Nat) (N : RawNode n) := N.lo.Bounded m ∧ N.hi.Bounded m

private def RawNode.bounded_of_le {N : RawNode n} (hm : N.Bounded m) (h : m ≤ m') : N.Bounded m' :=
  ⟨RawPointer.bounded_of_le hm.1 h, RawPointer.bounded_of_le hm.2 h⟩

private def RawNode.cook (N : RawNode n) (h : N.Bounded m) : Node n m := ⟨N.va, N.lo.cook h.1, N.hi.cook h.2⟩

private lemma RawNode.cook_equiv : Node.equiv (RawNode.cook N h1) (RawNode.cook N h2) := by
  simp only [Node.equiv]
  constructor
  · rfl
  · rcases h1 with ⟨h11, h12⟩
    rcases h2 with ⟨h21, h22⟩
    constructor
    · apply RawPointer.cook_equiv <;> assumption
    · apply RawPointer.cook_equiv <;> assumption

private def cook_heap {n c} (heap : Vector (RawNode n) c) (hh : ∀ i : Fin c, RawNode.Bounded i heap[i]) : Vector (Node n c) c :=
  Vector.ofFn (fun i ↦ heap[i].cook (RawNode.bounded_of_le (hh i) (by omega)))

private structure State (n) (n') (m) (m') where
  size : Nat
  heap : Vector (RawNode (max n n')) size
  cache : Std.HashMap (Pointer m × Pointer m') RawPointer

private def initial : State n n' m m' := ⟨_, (Vector.emptyWithCapacity 0), Std.HashMap.emptyWithCapacity⟩

def toVar_or (M : Vector (Node n m) m) : Pointer m → Nat → Nat
  | .terminal _, i => i
  | .node j, _     => M[j].var

@[simp]
lemma toVar_or_terminal_eq {n m} (w : Vector (Node n m) m) : toVar_or w (.terminal b) i = i := rfl

@[simp]
lemma toVar_or_node_eq {n m} (w : Vector (Node n m) m) {j} : toVar_or w (.node j) i = w[j].var := rfl

private def Invariant (op : Bool → Bool → Bool) (O : OBdd n m) (U : OBdd n' m') (r : State n n' m m') :=
  ∃ hh : (∀ i : Fin r.size, RawNode.Bounded i r.heap[i]),
    ∀ (k : (Pointer m × Pointer m')) (p : RawPointer),
      r.cache[k]? = some p →
      (∀ j h, p = .inr j → (r.heap[j]'h).va.1 =
        (toVar_or O.1.heap k.1 (n ⊔ n')) ⊓ (toVar_or U.1.heap k.2 (n ⊔ n'))) ∧
      ∃ hk1 : Bdd.Ordered ⟨O.1.heap, k.1⟩,
        ∃ hk2 : Bdd.Ordered ⟨U.1.heap, k.2⟩,
          ∃ hp : p.Bounded r.size,
            ∃ o : Bdd.Ordered ⟨cook_heap r.heap hh, p.cook hp⟩,
              ∀ I,
                OBdd.evaluate ⟨⟨cook_heap r.heap hh, p.cook hp⟩, o⟩ I =
                op
                  (OBdd.evaluate ⟨⟨O.1.heap, k.1⟩, hk1⟩ (Vector.cast (by simp) (I.take n)))
                  (OBdd.evaluate ⟨⟨U.1.heap, k.2⟩, hk2⟩ (Vector.cast (by simp) (I.take n')))

private lemma inv_initial {op} {O : OBdd n m} {U : OBdd n' m'} : Invariant op O U initial := by
  constructor
  · intro k p hp
    simp only [initial, Std.HashMap.getElem?_emptyWithCapacity, reduceCtorEq] at hp
  · rintro ⟨_, c⟩
    simp only [initial, not_lt_zero'] at c

private def cache_get (O_root : Pointer m) (U_root : Pointer m') (s : (State n n' m m')) : (Option RawPointer) :=
  s.cache[(⟨O_root, U_root⟩ : (Pointer m × Pointer m'))]?

private lemma cook_low {rn : RawNode n} {h1} {h2} : rn.lo.cook (m := m) h1 = (rn.cook h2).low := rfl

private lemma cook_high {rn : RawNode n} {h1} {h2} : rn.hi.cook (m := m) h1 = (rn.cook h2).high := rfl

private lemma cook_inj {p q : RawPointer} {hp} {hq} : p.cook (m := m) hp = q.cook hq → p = q := by
  intro h
  cases p <;> cases q <;> simp_all [RawPointer.cook]

private lemma cook_aux {p : RawPointer} {h1} {h2} : p.cook h1 = .node j → p.cook h2 = .node ⟨j, hj⟩ := by
  intro h
  cases p with
  | inl val => simp_all [RawPointer.cook]
  | inr val =>
    simp_all [RawPointer.cook]
    rw [Fin.eq_mk_iff_val_eq] at h
    exact h

private lemma push_ordered_aux {v : Vector (RawNode n) m} {h0} {h2} : Pointer.Reachable (cook_heap (v.push N) h2) (RawPointer.cook p h3) q → ∀ j, q = .node j → ∃ hj : j.1 < m, Pointer.Reachable (cook_heap v h0) (p.cook h1) (.node ⟨j.1, hj⟩) := by
  intro h
  induction h with
  | refl =>
    intro i hi
    cases p with
    | inl val => contradiction
    | inr val =>
      simp [RawPointer.cook] at hi
      subst hi
      simp only
      use h1 rfl
      simp [RawPointer.cook]
      left
  | tail r e ih =>
    intro j hj
    rename_i b c
    cases e with
    | low heq =>
      rename_i jb
      have := h2 jb
      simp only [RawNode.Bounded] at this
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn] at heq
      subst hj
      have that : (v.push N)[jb].lo = .inr j.1 := by
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) _ by rfl] at heq
        rw [← cook_low] at heq
        exact cook_inj heq
        apply RawPointer.bounded_of_le this.1
        omega
        simp [RawPointer.Bounded]
        intro i hi
        injection hi with heq
        rw [← heq]
        omega
      have : Apply.RawPointer.Bounded (↑jb) (v.push N)[jb].lo := this.1
      have := this that
      use lt_of_lt_of_le this (Nat.le_of_lt_succ jb.2)
      rcases (ih jb rfl) with ⟨r1, r2⟩
      trans .node ⟨jb.1, r1⟩
      · exact r2
      · simp_rw [Vector.getElem_push_lt r1] at heq
        right
        left
        left
        simp [cook_heap, RawNode.cook]
        simp [cook_heap, RawNode.cook] at heq
        exact cook_aux heq
    | high heq =>
      rename_i jb
      have := h2 jb
      simp only [RawNode.Bounded] at this
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn] at heq
      subst hj
      have that : (v.push N)[jb].hi = .inr j.1 := by
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) _ by rfl] at heq
        rw [← cook_high] at heq
        exact cook_inj heq
        apply RawPointer.bounded_of_le this.2
        omega
        simp [RawPointer.Bounded]
        intro i hi
        injection hi with heq
        rw [← heq]
        omega
      have : Apply.RawPointer.Bounded (↑jb) (v.push N)[jb].hi := this.2
      have := this that
      use lt_of_lt_of_le this (Nat.le_of_lt_succ jb.2)
      rcases (ih jb rfl) with ⟨r1, r2⟩
      trans .node ⟨jb.1, r1⟩
      · exact r2
      · simp_rw [Vector.getElem_push_lt r1] at heq
        right
        left
        right
        simp [cook_heap, RawNode.cook]
        simp [cook_heap, RawNode.cook] at heq
        exact cook_aux heq

private lemma push_ordered : Bdd.Ordered ⟨cook_heap v h0, RawPointer.cook p h1⟩ → Bdd.Ordered ⟨cook_heap (v.push N) h2, RawPointer.cook p h3⟩ := by
  intro h
  apply Bdd.ordered_of_ordered_heap_all_reachable_eq ⟨⟨cook_heap v h0, RawPointer.cook p h1⟩, h⟩
  · intro j hj
    rcases (push_ordered_aux hj (h2 := h2) (h1 := h1) (h0 := h0) j rfl) with ⟨r1, r2⟩
    use r1
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_lt r1,
      RawNode.cook_equiv]
  · intro j hj
    simp_all only
    simp [RawPointer.cook] at hj
    split at hj
    next heq => contradiction
    next heq =>
      simp only [Pointer.node.injEq] at hj
      subst hj
      use h1 rfl
      simp [RawPointer.cook]

private lemma push_evaluate {v : Vector _ _} {h0} {h1} {ho : Bdd.Ordered _} {hu : Bdd.Ordered ⟨cook_heap v h1, RawPointer.cook p hq⟩} :
    OBdd.evaluate ⟨⟨cook_heap (v.push N) h0, RawPointer.cook p hp⟩, ho⟩ =
    OBdd.evaluate ⟨⟨cook_heap v h1, RawPointer.cook p hq⟩, hu⟩ := by
  apply OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
  · simp only [Fin.getElem_fin]
    intro j hj
    use (by omega)
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Fin.is_lt, Vector.getElem_push_lt]
    exact RawNode.cook_equiv
  · exact RawPointer.cook_equiv (h2 := hp)

private lemma heap_push_aux (s : (State n n' m m')) (inv : Invariant op O U s)
    (hNl : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.hi)
    (hNv : N.va.1 = (toVar_or O.1.heap O.1.root (n ⊔ n')) ⊓ (toVar_or U.1.heap U.1.root (n ⊔ n')))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _) (I : Vector Bool (max n n')),
            OBdd.evaluate ⟨{ heap := Apply.cook_heap (s.heap.push N) h0, root := Pointer.node ⟨s.size, by simp⟩ }, h1⟩ I =
            op (O.evaluate (Vector.cast (by omega) (I.extract 0 n))) (U.evaluate (Vector.cast (by omega) (I.extract 0 n')))) :
    Invariant op O U
      { size := s.size + 1, heap := s.heap.push N, cache := s.cache.insert (O.1.root, U.1.root) (Sum.inr s.size) } := by
  rcases hNl with ⟨kl, hkl⟩
  rcases hNh with ⟨kh, hkh⟩
  have hN : RawNode.Bounded s.size N := by
    simp only [RawNode.Bounded]
    constructor
    · exact (inv.2 kl N.lo hkl).2.2.2.1
    · exact (inv.2 kh N.hi hkh).2.2.2.1
  have : ∀ (i : Fin (s.size + 1)), Apply.RawNode.Bounded (↑i) (s.heap.push N)[i] := by
    intro i
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_push]
    split
    next hi => exact inv.1 ⟨i.1, hi⟩
    next hi =>
      have : i.1 = s.size := by omega
      rw [this]
      exact hN
  use this
  intro k p
  simp only
  intro hp
  rw [Std.HashMap.getElem?_insert] at hp
  simp only [beq_iff_eq, Vector.take_eq_extract] at hp
  split at hp
  next heq =>
    subst heq
    simp only
    constructor
    · intro j hs hj
      rw [Vector.getElem_push]
      split
      next heqq =>
        injection hp with hpp
        rw [hj] at hpp
        injection hpp with hppp
        rw [hppp] at heqq
        absurd heqq
        simp only [lt_self_iff_false, not_false_eq_true]
      next heqq =>
        exact hNv
    use O.2, U.2
    injection hp with hpe
    subst hpe
    have hb : Apply.RawPointer.Bounded (s.size + 1) (Sum.inr s.size) := by intro i hi; injection hi with hie; subst hie; simp
    use hb
    have hoo : Bdd.Ordered ⟨Apply.cook_heap (s.heap.push N) this, Apply.RawPointer.cook (Sum.inr s.size) hb⟩ := by
      apply Bdd.ordered_of_low_high_ordered rfl
      · simp only [Bdd.low, cook_heap]
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
        rw [← cook_low]
        swap; apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        rcases (inv.2 kl N.lo hkl).2.2.2 with that
        apply push_ordered
        · exact this
        · exact that.2.1
      ·
        simp [Nat.succ_eq_add_one, Bdd.var, gt_iff_lt, cook_heap, Bdd.low, RawPointer.cook]
        cases heq : N.lo with
        | inl val =>
          rw [← cook_low]
          simp_rw [heq]
          simp only [RawPointer.cook, Pointer.toVar_terminal_eq, Nat.succ_eq_add_one,
            Fin.natCast_eq_last, Fin.castSucc_lt_last]
          apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        | inr val =>
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1 .refl heq
          rw [← cook_low]
          simp_rw [heq]
          simp only [RawNode.cook, RawPointer.cook, Pointer.toVar_node_eq, Nat.succ_eq_add_one,
            Fin.getElem_fin, Vector.getElem_ofFn, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff]
          rw [Vector.getElem_push_lt]
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1 .refl heq
          exact hxl _ hvs heq
          exact hvs
          apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
      · simp only [Bdd.high, cook_heap]
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
        rw [← cook_high]
        swap; apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        rcases (inv.2 kh N.hi hkh).2.2.2 with that
        apply push_ordered
        · exact this
        · exact that.2.1
      ·
        simp [Nat.succ_eq_add_one, Bdd.var, gt_iff_lt, cook_heap, Bdd.high, RawPointer.cook]
        cases heq : N.hi with
        | inl val =>
          rw [← cook_high]
          simp_rw [heq]
          simp only [RawPointer.cook, Pointer.toVar_terminal_eq, Nat.succ_eq_add_one,
            Fin.natCast_eq_last, Fin.castSucc_lt_last]
          apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        | inr val =>
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 _ _ hkh).2.2.2.1 .refl heq
          rw [← cook_high]
          simp_rw [heq]
          simp only [RawNode.cook, RawPointer.cook, Pointer.toVar_node_eq, Nat.succ_eq_add_one,
            Fin.getElem_fin, Vector.getElem_ofFn, Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff]
          rw [Vector.getElem_push_lt]
          exact hxh _ hvs heq
          apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
    use hoo
    rw [show ⟨{ heap := U.1.heap, root := U.1.root }, _⟩ =  U by rfl]
    rw [show ⟨{ heap := O.1.heap, root := O.1.root }, _⟩ =  O by rfl]
    simp only [RawPointer.cook]
    intro I
    apply hh _ hoo
  next heq =>
    constructor
    · intro j hs hj
      rw [hj] at hp
      rcases (inv.2 k _ hp) with ⟨inv1, inv2⟩
      have := inv1 j (inv2.2.2.1 rfl) rfl
      rw [Vector.getElem_push_lt (inv2.2.2.1 rfl)]
      exact this
    rcases (inv.2 k p hp) with that
    use that.2.1
    use that.2.2.1
    have hb : ∀ {i}, p = Sum.inr i → i < s.size + 1 :=
      RawPointer.bounded_of_le that.2.2.2.1 (by simp only [le_add_iff_nonneg_right, zero_le])
    use hb
    have ho : Bdd.Ordered { heap := Apply.cook_heap (s.heap.push N) this, root := p.cook hb } := push_ordered that.2.2.2.2.1
    use ho
    intro I
    calc _
      _ = OBdd.evaluate ⟨{ heap := Apply.cook_heap (s.heap) inv.1, root := p.cook that.2.2.2.1 }, that.2.2.2.2.1⟩ I := by
        rw [OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq]
        · simp only [Fin.getElem_fin]
          intro j hj
          use (by omega)
          simp [cook_heap]
          exact RawNode.cook_equiv
        · simp only [RawPointer.cook_equiv]
    exact that.2.2.2.2.2 I

private def heap_push (N : RawNode (n ⊔ n')) (s : (State n n' m m')) (inv : Invariant op O U s)
    (hNl : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.hi)
    (hNv : N.va.1 = (toVar_or O.1.heap O.1.root (n ⊔ n')) ⊓ (toVar_or U.1.heap U.1.root (n ⊔ n')))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _) (I : Vector Bool (max n n')),
            OBdd.evaluate ⟨{ heap := Apply.cook_heap (s.heap.push N) h0, root := Pointer.node ⟨s.size, by simp⟩ }, h1⟩ I =
            op (O.evaluate (Vector.cast (by omega) (I.extract 0 n))) (U.evaluate (Vector.cast (by omega) (I.extract 0 n'))))
            (hc : s.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = none ) :
    { r : State n n' m m' × RawPointer //
      (Invariant op O U r.1) ∧
      (r.1.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some r.2) ∧
      s.size ≤ r.1.size ∧
      (∀ (k : Pointer m × Pointer m'),
        (∀ p, s.cache[k]? = some p → r.1.cache[k]? = some p) ∧
        (r.1.cache[k]? = none → s.cache[k]? = none) ∧
        (s.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k.1 ∧ Pointer.Reachable U.1.heap U.1.root k.2)) ∧
      (∀ j h, r.2 = .inr j → (r.1.heap[j]'h).va.1 = (toVar_or O.1.heap O.1.root (n ⊔ n')) ⊓ (toVar_or U.1.heap U.1.root (n ⊔ n')))
    } :=
  ⟨⟨⟨s.size + 1, s.heap.push N, s.cache.insert ⟨O.1.root, U.1.root⟩ (.inr s.size)⟩, .inr s.size⟩, by
    simp only [Prod.exists]
    constructor
    · exact heap_push_aux s inv hNl hNh hNv hxl hxh hh
    · constructor
      · simp only [Std.HashMap.getElem?_insert_self]
      · constructor
        · simp only [le_add_iff_nonneg_right, zero_le]
        · constructor
          swap
          · intro j hj1 hj2
            injection hj2 with hji
            subst hji
            simp only [Vector.getElem_push_eq]
            exact hNv
          intro k
          constructor
          · intro p hkp
            rw [← hkp]
            simp only [Std.HashMap.getElem?_insert, beq_iff_eq, ite_eq_right_iff]
            intro contra
            rw [← contra] at hkp
            rw [hkp] at hc
            contradiction
          · constructor
            · simp only [getElem?_eq_none_iff, Std.HashMap.mem_insert, beq_iff_eq, not_or,
                and_imp, imp_self, implies_true]
            · rintro hk ⟨q, hq⟩
              simp only [Std.HashMap.getElem?_insert, beq_iff_eq, ite_eq_right_iff] at hq
              split at hq
              next heqq => subst heqq; constructor <;> left
              next heqq => rw [hk] at hq; contradiction
  ⟩

private lemma insert_terminal_invariant (s0 : State n n' m m') (inv : Invariant op O U s0) (ho : O.1.root = .terminal b) (hu : U.1.root = .terminal b'):
    Invariant op O U { size := s0.size, heap := s0.heap, cache := s0.cache.insert (O.1.root, U.1.root) (Sum.inl (op b b')) } := by
  constructor
  intro k p hp
  simp only at hp
  simp only
  rw [Std.HashMap.getElem?_insert] at hp
  simp only [beq_iff_eq] at hp
  split at hp
  next heq =>
    rw [← heq]
    constructor
    · intro j hj hjp
      subst hjp
      injection hp with hpp
      contradiction
    use O.2, U.2
    injection hp with hpe
    subst hpe
    use (fun contra ↦ by contradiction)
    simp [RawPointer.cook, ho, hu, Bdd.Ordered_of_terminal]
  next =>
    constructor
    · exact (inv.2 _ _ hp).1
    exact (inv.2 _ _ hp).2

private lemma op_if1 (op : Bool → Bool → Bool) {c l rt rf : Bool} :
    op l (if c then rt else rf) = if c then (op l rt) else (op l rf) :=
      apply_ite (op l) (c = true) rt rf

private lemma op_if2 (op : Bool → Bool → Bool) {c lt lf r : Bool} :
    op  (if c then lt else lf) r = if c then (op lt r) else (op lf r) := by
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only [Bool.not_eq_true]

private lemma op_if3 (op : Bool → Bool → Bool) {c lt lf rt rf : Bool} :
    op (if c then lt else lf) (if c then rt else rf) = if c then (op lt rt) else (op lf rf) := by
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only [Bool.not_eq_true]

private lemma aux_lt1_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .terminal b) (U_root_def : U.1.root = .node j') :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.low U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt1_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .terminal b) (U_root_def : U.1.root = .node j') :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.high U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt2_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .terminal b') :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.low O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt2_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .terminal b') :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.high O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt3_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hleq : O.1.heap[j].var.1 < U.1.heap[j'].var.1) :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.low O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt3_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hleq : O.1.heap[j].var.1 < U.1.heap[j'].var.1) :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.high O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt4_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.low U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt4_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.high U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all

private lemma aux_lt5_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap (O.low O_root_def).1.root (max n n'))
        (toVar_or U.1.heap (U.low U_root_def).1.root (max n n')) := by
  have h1 := OBdd.var_lt_low_var (h := O_root_def)
  have h2 := OBdd.var_lt_high_var (h := O_root_def)
  have h3 := OBdd.var_lt_low_var (h := U_root_def)
  have h4 := OBdd.var_lt_high_var (h := U_root_def)
  have h5 : U.1.heap[↑j'].var.1 < n + 1 := by omega
  simp_all [OBdd.var, toVar_or, heeq]
  split
  next heq =>
    split
    next heqq => simp_all
    next heqq => simp_all
  next heq =>
    split
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all

private lemma aux_lt5_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap (O.high O_root_def).1.root (max n n'))
        (toVar_or U.1.heap (U.high U_root_def).1.root (max n n')) := by
  have h2 := OBdd.var_lt_high_var (h := O_root_def)
  have h3 := OBdd.var_lt_low_var (h := U_root_def)
  have h4 := OBdd.var_lt_high_var (h := U_root_def)
  have h5 : U.1.heap[↑j'].var.1 < n + 1 := by omega
  simp_all [OBdd.var, toVar_or, heeq]
  split
  next heq =>
    split
    next heqq => simp_all
    next heqq => simp_all
  next heq =>
    split
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all

private def apply_helper (op : (Bool → Bool → Bool)) (O : OBdd n m) (U : OBdd n' m') (s0 : State n n' m m') (inv : Invariant op O U s0) :
    { r : State n n' m m' × RawPointer //
      (Invariant op O U r.1) ∧
      (r.1.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some r.2) ∧
      (s0.size ≤ r.1.size) ∧
      (∀ (k : Pointer m × Pointer m'),
        (∀ p, s0.cache[k]? = some p → r.1.cache[k]? = some p) ∧
        (r.1.cache[k]? = none → s0.cache[k]? = none) ∧
        (s0.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k.1 ∧ Pointer.Reachable U.1.heap U.1.root k.2)) ∧
      (∀ j h, r.2 = .inr j → (r.1.heap[j]'h).va.1 = (toVar_or O.1.heap O.1.root (n ⊔ n')) ⊓ (toVar_or U.1.heap U.1.root (n ⊔ n')))
    } :=
  match hc : cache_get O.1.root U.1.root s0 with
  | some root =>
    ⟨ ⟨s0, root⟩, ⟨inv, hc, .refl,
      by
        intro k
        constructor
        · intro p h
          exact h
        · constructor
          · intro h
            exact h
          · rintro h ⟨_, c⟩
            rw [h] at c
            contradiction,
      by
        simp only [Nat.succ_eq_add_one, Bdd.var]
        intro j hj1 hj2
        simp only [cache_get] at hc
        rw [hj2] at hc
        exact (inv.2 _ _ hc).1 _ _ rfl
      ⟩
    ⟩
  | none =>
    match O_root_def : O.1.root with
    | .terminal b =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        ⟨⟨⟨s0.size, s0.heap, s0.cache.insert ⟨O.1.root, U.1.root⟩ (.inl (op b b'))⟩, .inl (op b b')⟩, by
          simp only [Prod.exists]
          constructor
          · exact insert_terminal_invariant s0 inv O_root_def U_root_def
          · constructor
            · simp only [O_root_def, U_root_def, Std.HashMap.getElem?_insert_self]
            · constructor
              · exact .refl
              · constructor
                intro k
                constructor
                · intro p hp
                  simp only [cache_get] at hc
                  rw [← hp]
                  simp only [Std.HashMap.getElem?_insert, beq_iff_eq, ite_eq_right_iff]
                  intro contra
                  subst contra
                  rw [hc] at hp
                  contradiction
                · constructor
                  · simp only [getElem?_eq_none_iff, Std.HashMap.mem_insert, beq_iff_eq, not_or,
                      and_imp, imp_self, implies_true]
                  · rintro h1 ⟨p, hp⟩
                    simp only [Std.HashMap.getElem?_insert,beq_iff_eq] at hp
                    split at hp
                    next heq =>
                      subst heq
                      simp only [O_root_def, U_root_def]
                      constructor
                      · left
                      · left
                    next heq => rw [h1] at hp; contradiction
                · intro _ _ _; contradiction
        ⟩
      | .node j' =>
        let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op O (U.low U_root_def) s0 inv
        let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op O (U.high U_root_def) sl invl
        let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
          heap_push (O := O) (U := U)
            ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh invh
            (by
              use ⟨O.1.root, ((U.low U_root_def).1.root)⟩
              simp only
              exact (hhp.1 _).1 _ hl
            )
            ⟨_, hh⟩
            (by
              simp only
              rw [O_root_def, U_root_def]
              simp only [Fin.getElem_fin, toVar_or, le_sup_iff, Fin.is_le', or_true,
                inf_of_le_right]
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := (hhp.1 _).1 _ hl
              simp only at this
              rw [hj2] at this
              have that := (invh.2 _ (.inr j) this).1 _ hj1 rfl
              simp only at that
              rw [that]
              exact aux_lt1_low O_root_def U_root_def
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := hhp.2 _ hj1 hj2
              rw [this]
              exact aux_lt1_high O_root_def U_root_def
            )
            (by
              intro h0 h1 I
              symm
              rw [OBdd.evaluate_node'' U_root_def]
              simp only
              rw [op_if1 op]
              simp only [OBdd.evaluate_node]
              congr 1
              · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                  RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                  Bool.coe_iff_coe]
                have := Vector.getElem_extract (as := I) (start := 0) (stop := n') (i := U.1.heap[j'.1].var.1) (by omega)
                simp only [Nat.sub_zero, zero_add] at this
                exact this
              · conv =>
                  rhs
                  congr
                  congr
                  congr
                  rfl
                  simp [cook_heap, RawNode.cook]
                  rfl
                  rfl
                symm
                have := (invh.2 ⟨O.1.root, (U.high U_root_def).1.root⟩ rh hh).2
                calc _
                  _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rh.cook _⟩, _⟩ I := by
                    rw [push_evaluate]
                    · exact this.2.2.1
                    · exact push_ordered this.2.2.2.1
                    · exact this.2.2.2.1
                  _ = _ := by
                    have := this.2.2.2.2 I
                    simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                    exact this
              · conv =>
                  rhs
                  congr
                  congr
                  congr
                  rfl
                  simp [cook_heap, RawNode.cook]
                  rfl
                  rfl
                symm
                have : sh.cache[(⟨O.1.root, (U.low U_root_def).1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                  apply (hhp.1 _).1
                  exact hl
                have := invh.2 ⟨O.1.root, (U.low U_root_def).1.root⟩ rl this
                calc _
                  _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rl.cook _⟩, _⟩ I := by
                    rw [push_evaluate]
                    · exact this.2.2.2.1
                    · exact push_ordered this.2.2.2.2.1
                    · exact this.2.2.2.2.1
                  _ = _ := by
                    have := this.2.2.2.2.2 I
                    simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                    exact this
            )
            (by
              simp only [cache_get] at hc
              cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
              | none => rfl
              | some val =>
                cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                | none =>
                  have := ((hhp.1 _).2.2 heqq ⟨val, heq⟩).2
                  simp only [OBdd.high_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_high
                | some val =>
                  have := ((hlp.1 _).2.2 hc ⟨_, heqq⟩).2
                  simp only [OBdd.low_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_low
            )
        ⟨ r,
          invv,
          (by rw [O_root_def, U_root_def] at hv; exact hv),
          .trans hsl (.trans hsh hsv),
          by
            constructor
            swap
            · rw [← O_root_def, ← U_root_def]
              exact hvp.2
            intro k
            constructor
            · intro p hp
              apply (hvp.1 _).1
              apply (hhp.1 _).1
              apply (hlp.1 _).1
              exact hp
            · constructor
              · intro hk
                apply (hlp.1 _).2.1
                apply (hhp.1 _).2.1
                apply (hvp.1 _).2.1
                exact hk
              · intro hk hkp
                rw [← O_root_def, ← U_root_def]
                cases heq : sh.cache[k]? with
                | none =>
                  apply (hvp.1 _).2.2 heq hkp
                | some w =>
                  cases heqq : sl.cache[k]? with
                  | none =>
                    have := (hhp.1 _).2.2 heqq ⟨_, heq⟩
                    constructor
                    · exact this.1
                    · trans (U.high U_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_high.2
                      · exact this.2
                  | some ww =>
                    have := (hlp.1 _).2.2 hk ⟨_, heqq⟩
                    constructor
                    · exact this.1
                    · trans (U.low U_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_low.2
                      · exact this.2
        ⟩
    | .node j =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op (O.low O_root_def) U s0 inv
        let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op (O.high O_root_def) U sl invl
        let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
          heap_push (O := O) (U := U)
            ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh invh
            ⟨_, (hhp.1 _).1 _ hl⟩
            ⟨_, hh⟩
            (by
              simp only
              rw [O_root_def, U_root_def]
              simp only [Fin.getElem_fin, toVar_or, le_sup_iff, Fin.is_le', or_true, true_or,
                inf_of_le_right, inf_of_le_left]
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := (hhp.1 _).1 _ hl
              simp only at this
              rw [hj2] at this
              have that := (invh.2 _ (.inr j) this).1 _ hj1 rfl
              simp only at that
              rw [that]
              exact aux_lt2_low O_root_def U_root_def
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := hhp.2 _ hj1 hj2
              rw [this]
              exact aux_lt2_high O_root_def U_root_def
            )
            (by
              intro h0 h1 I
              symm
              rw [OBdd.evaluate_node'' O_root_def]
              simp only
              rw [op_if2 op]
              simp only [OBdd.evaluate_node]
              congr 1
              · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                  RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                  Bool.coe_iff_coe]
                have := Vector.getElem_extract (as := I) (start := 0) (stop := n) (i := O.1.heap[j.1].var.1) (by omega)
                simp only [Nat.sub_zero, zero_add] at this
                exact this
              · conv =>
                  rhs
                  congr
                  congr
                  congr
                  rfl
                  simp [cook_heap, RawNode.cook]
                  rfl
                  rfl
                symm
                have := (invh.2 ⟨(O.high O_root_def).1.root, U.1.root⟩ rh hh).2
                calc _
                  _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rh.cook _⟩, _⟩ I := by
                    rw [push_evaluate]
                    · exact this.2.2.1
                    · exact push_ordered this.2.2.2.1
                    · exact this.2.2.2.1
                  _ = _ := by
                    have := this.2.2.2.2 I
                    simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                    exact this
              · conv =>
                  rhs
                  congr
                  congr
                  congr
                  rfl
                  simp [cook_heap, RawNode.cook]
                  rfl
                  rfl
                symm
                have : sh.cache[(⟨(O.low O_root_def).1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                  apply (hhp.1 _).1
                  exact hl
                have := invh.2 ⟨(O.low O_root_def).1.root, U.1.root⟩ rl this
                calc _
                  _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rl.cook _⟩, _⟩ I := by
                    rw [push_evaluate]
                    · exact this.2.2.2.1
                    · exact push_ordered this.2.2.2.2.1
                    · exact this.2.2.2.2.1
                  _ = _ := by
                    have := this.2.2.2.2.2 I
                    simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                    exact this
            )
            (by
              simp only [cache_get] at hc
              cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
              | none => rfl
              | some val =>
                cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                | none =>
                  have := ((hhp.1 _).2.2 heqq ⟨val, heq⟩).1
                  simp only [OBdd.high_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_high
                | some val =>
                  have := ((hlp.1 _).2.2 hc ⟨_, heqq⟩).1
                  simp only [OBdd.low_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_low
            )
        ⟨ r,
          invv,
          (by rw [O_root_def, U_root_def] at hv; exact hv),
          .trans hsl (.trans hsh hsv),
          by
            constructor
            swap
            · rw [← O_root_def, ← U_root_def]
              exact hvp.2
            intro k
            constructor
            · intro p hp
              apply (hvp.1 _).1
              apply (hhp.1 _).1
              apply (hlp.1 _).1
              exact hp
            · constructor
              · intro hk
                apply (hlp.1 _).2.1
                apply (hhp.1 _).2.1
                apply (hvp.1 _).2.1
                exact hk
              · intro hk hkp
                rw [← O_root_def, ← U_root_def]
                cases heq : sh.cache[k]? with
                | none =>
                  apply (hvp.1 _).2.2 heq hkp
                | some w =>
                  cases heqq : sl.cache[k]? with
                  | none =>
                    have := (hhp.1 _).2.2 heqq ⟨_, heq⟩
                    constructor
                    · trans (O.high O_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_high.2
                      · exact this.1
                    · exact this.2
                  | some ww =>
                    have := (hlp.1 _).2.2 hk ⟨_, heqq⟩
                    constructor
                    · trans (O.low O_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_low.2
                      · exact this.1
                    · exact this.2
        ⟩
      | .node j' =>
        if hleq : O.1.heap[j].var.1 < U.1.heap[j'].var.1
        then
          let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op (O.low O_root_def) U s0 inv
          let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op (O.high O_root_def) U sl invl
          let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
            heap_push (O := O) (U := U)
              ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh invh
              ⟨_, (hhp.1 _).1 _ hl⟩
              ⟨_, hh⟩
              (by
                simp only
                rw [O_root_def, U_root_def]
                simp only [Fin.getElem_fin, toVar_or, le_sup_iff, Fin.is_le', or_true, true_or,
                  inf_of_le_right, inf_of_le_left]
                exact Eq.symm (min_eq_left_of_lt hleq)
              )
              (by
                intro j'' hj1
                simp only [Fin.getElem_fin]
                intro hj2
                have := (hhp.1 _).1 _ hl
                simp only at this
                rw [hj2] at this
                have that := (invh.2 _ _ this).1 _ hj1 rfl
                simp only at that
                rw [that]
                exact aux_lt3_low O_root_def U_root_def hleq
              )
              (by
                intro j'' hj1
                simp only [Fin.getElem_fin]
                intro hj2
                have := hhp.2 _ hj1 hj2
                rw [this]
                exact aux_lt3_high O_root_def U_root_def hleq
              )
              (by
                intro h0 h1 I
                symm
                rw [OBdd.evaluate_node'' O_root_def]
                simp only
                rw [op_if2 op]
                simp only [OBdd.evaluate_node]
                congr 1
                · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                    RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                    Bool.coe_iff_coe]
                  have := Vector.getElem_extract (as := I) (start := 0) (stop := n) (i := O.1.heap[j.1].var.1) (by omega)
                  simp only [Nat.sub_zero, zero_add] at this
                  exact this
                · conv =>
                    rhs
                    congr
                    congr
                    congr
                    rfl
                    simp [cook_heap, RawNode.cook]
                    rfl
                    rfl
                  symm
                  have := (invh.2 ⟨(O.high O_root_def).1.root, U.1.root⟩ rh hh).2
                  calc _
                    _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rh.cook _⟩, _⟩ I := by
                      rw [push_evaluate]
                      · exact this.2.2.1
                      · exact push_ordered this.2.2.2.1
                      · exact this.2.2.2.1
                    _ = _ := by
                      have := this.2.2.2.2 I
                      simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                      exact this
                · conv =>
                    rhs
                    congr
                    congr
                    congr
                    rfl
                    simp [cook_heap, RawNode.cook]
                    rfl
                    rfl
                  symm
                  have : sh.cache[(⟨(O.low O_root_def).1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                    apply (hhp.1 _).1
                    exact hl
                  have := invh.2 ⟨(O.low O_root_def).1.root, U.1.root⟩ rl this
                  calc _
                    _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rl.cook _⟩, _⟩ I := by
                      rw [push_evaluate]
                      · exact this.2.2.2.1
                      · exact push_ordered this.2.2.2.2.1
                      · exact this.2.2.2.2.1
                    _ = _ := by
                      have := this.2.2.2.2.2 I
                      simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                      exact this
              )
              (by
                simp only [cache_get] at hc
                cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                | none => rfl
                | some val =>
                  cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                  | none =>
                    have := ((hhp.1 _).2.2 heqq ⟨val, heq⟩).1
                    simp only [OBdd.high_heap_eq_heap] at this
                    absurd this
                    apply OBdd.not_oedge_reachable
                    exact oedge_of_high
                  | some val =>
                    have := ((hlp.1 _).2.2 hc ⟨_, heqq⟩).1
                    simp only [OBdd.low_heap_eq_heap] at this
                    absurd this
                    apply OBdd.not_oedge_reachable
                    exact oedge_of_low
              )
          ⟨ r,
            invv,
            (by rw [O_root_def, U_root_def] at hv; exact hv),
            .trans hsl (.trans hsh hsv),
            by
              constructor
              swap
              · rw [← O_root_def, ← U_root_def]
                exact hvp.2
              intro k
              constructor
              · intro p hp
                apply (hvp.1 _).1
                apply (hhp.1 _).1
                apply (hlp.1 _).1
                exact hp
              · constructor
                · intro hk
                  apply (hlp.1 _).2.1
                  apply (hhp.1 _).2.1
                  apply (hvp.1 _).2.1
                  exact hk
                · intro hk hkp
                  rw [← O_root_def, ← U_root_def]
                  cases heq : sh.cache[k]? with
                  | none =>
                    apply (hvp.1 _).2.2 heq hkp
                  | some w =>
                    cases heqq : sl.cache[k]? with
                    | none =>
                      have := (hhp.1 _).2.2 heqq ⟨_, heq⟩
                      constructor
                      · trans (O.high O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_high.2
                        · exact this.1
                      · exact this.2
                    | some ww =>
                      have := (hlp.1 _).2.2 hk ⟨_, heqq⟩
                      constructor
                      · trans (O.low O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_low.2
                        · exact this.1
                      · exact this.2
          ⟩
        else
          if hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1
          then
            let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op O (U.low U_root_def) s0 inv
            let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op O (U.high U_root_def) sl invl
            let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
              heap_push (O := O) (U := U)
                ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh invh
                ⟨_, (hhp.1 _).1 _ hl⟩
                ⟨_, hh⟩
                (by
                  simp only
                  rw [O_root_def, U_root_def]
                  simp only [Fin.getElem_fin, toVar_or, le_sup_iff, Fin.is_le', or_true, true_or,
                    inf_of_le_right, inf_of_le_left]
                  exact Eq.symm (min_eq_right_of_lt hgeq)
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := (hhp.1 _).1 _ hl
                  simp only at this
                  rw [hj2] at this
                  have that := (invh.2 _ _ this).1 _ hj1 rfl
                  simp only at that
                  rw [that]
                  exact aux_lt4_low O_root_def U_root_def hgeq
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := hhp.2 _ hj1 hj2
                  rw [this]
                  exact aux_lt4_high O_root_def U_root_def hgeq
                )
                (by
                  intro h0 h1 I
                  symm
                  rw [OBdd.evaluate_node'' U_root_def]
                  simp only
                  rw [op_if1 op]
                  simp only [OBdd.evaluate_node]
                  congr 1
                  · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                      RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                      Bool.coe_iff_coe]
                    have := Vector.getElem_extract (as := I) (start := 0) (stop := n') (i := U.1.heap[j'.1].var.1) (by omega)
                    simp only [Nat.sub_zero, zero_add] at this
                    exact this
                  · conv =>
                      rhs
                      congr
                      congr
                      congr
                      rfl
                      simp [cook_heap, RawNode.cook]
                      rfl
                      rfl
                    symm
                    have := (invh.2 ⟨O.1.root, (U.high U_root_def).1.root⟩ rh hh).2
                    calc _
                      _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rh.cook _⟩, _⟩ I := by
                        rw [push_evaluate]
                        · exact this.2.2.1
                        · exact push_ordered this.2.2.2.1
                        · exact this.2.2.2.1
                      _ = _ := by
                        have := this.2.2.2.2 I
                        simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                        exact this
                  · conv =>
                      rhs
                      congr
                      congr
                      congr
                      rfl
                      simp [cook_heap, RawNode.cook]
                      rfl
                      rfl
                    symm
                    have : sh.cache[(⟨O.1.root, (U.low U_root_def).1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                      apply (hhp.1 _).1
                      exact hl
                    have := invh.2 ⟨O.1.root, (U.low U_root_def).1.root⟩ rl this
                    calc _
                      _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rl.cook _⟩, _⟩ I := by
                        rw [push_evaluate]
                        · exact this.2.2.2.1
                        · exact push_ordered this.2.2.2.2.1
                        · exact this.2.2.2.2.1
                      _ = _ := by
                        have := this.2.2.2.2.2 I
                        simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                        exact this
                )
                (by
                  simp only [cache_get] at hc
                  cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                  | none => rfl
                  | some val =>
                    cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                    | none =>
                      have := ((hhp.1 _).2.2 heqq ⟨val, heq⟩).2
                      simp only [OBdd.high_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_high
                    | some val =>
                      have := ((hlp.1 _).2.2 hc ⟨_, heqq⟩).2
                      simp only [OBdd.low_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_low
                )
            ⟨ r,
              invv,
              (by rw [O_root_def, U_root_def] at hv; exact hv),
              .trans hsl (.trans hsh hsv),
              by
                constructor
                swap
                · rw [← O_root_def, ← U_root_def]
                  exact hvp.2
                intro k
                constructor
                · intro p hp
                  apply (hvp.1 _).1
                  apply (hhp.1 _).1
                  apply (hlp.1 _).1
                  exact hp
                · constructor
                  · intro hk
                    apply (hlp.1 _).2.1
                    apply (hhp.1 _).2.1
                    apply (hvp.1 _).2.1
                    exact hk
                  · intro hk hkp
                    rw [← O_root_def, ← U_root_def]
                    cases heq : sh.cache[k]? with
                    | none =>
                      apply (hvp.1 _).2.2 heq hkp
                    | some w =>
                      cases heqq : sl.cache[k]? with
                      | none =>
                        have := (hhp.1 _).2.2 heqq ⟨_, heq⟩
                        constructor
                        · exact this.1
                        · trans (U.high U_root_def).1.root
                          · apply OBdd.reachable_of_edge
                            exact oedge_of_high.2
                          · exact this.2
                      | some ww =>
                        have := (hlp.1 _).2.2 hk ⟨_, heqq⟩
                        constructor
                        · exact this.1
                        · trans (U.low U_root_def).1.root
                          · apply OBdd.reachable_of_edge
                            exact oedge_of_low.2
                          · exact this.2
            ⟩
          else
            let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op (O.low O_root_def) (U.low U_root_def) s0 inv
            let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op (O.high O_root_def) (U.high U_root_def) sl invl
            let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
              heap_push (O := O) (U := U)
                ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh invh
                ⟨_, (hhp.1 _).1 _ hl⟩
                ⟨_, hh⟩
                (by
                  simp only
                  rw [O_root_def, U_root_def]
                  simp only [Fin.getElem_fin, toVar_or, le_sup_iff, Fin.is_le', or_true, true_or,
                    inf_of_le_right, inf_of_le_left]
                  have heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1 := by omega
                  simp only [Fin.getElem_fin] at heeq
                  rw [heeq]
                  simp only [min_self]
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := (hhp.1 _).1 _ hl
                  simp only at this
                  rw [hj2] at this
                  have that := (invh.2 _ _ this).1 _ hj1 rfl
                  simp only at that
                  rw [that]
                  exact aux_lt5_low O_root_def U_root_def (by omega)
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := hhp.2 _ hj1 hj2
                  rw [this]
                  exact aux_lt5_high O_root_def U_root_def (by omega)
                )
                (by
                  intro h0 h1 I
                  symm
                  rw [OBdd.evaluate_node'' U_root_def]
                  rw [OBdd.evaluate_node'' O_root_def]
                  simp only
                  have heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1 := by omega
                  have heo := Vector.getElem_extract (as := I) (start := 0) (stop := n) (i := O.1.heap[j.1].var.1) (by omega)
                  have heu := Vector.getElem_extract (as := I) (start := 0) (stop := n') (i := U.1.heap[j'.1].var.1) (by omega)
                  have : (Vector.cast (m := n') (by omega) (I.extract 0 n'))[U.1.heap[j'].var] = (Vector.cast (m := n) (by omega) (I.extract 0 n))[O.1.heap[j].var] := by
                    simp only [Fin.getElem_fin]
                    rw [Vector.getElem_cast]
                    rw [Vector.getElem_cast]
                    rw [heo]
                    rw [heu]
                    simp only [zero_add]
                    congr 1
                    symm
                    exact heeq
                  rw [this]
                  rw [op_if3 op]
                  simp only [OBdd.evaluate_node]
                  congr 1
                  ·
                    simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                      RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                      Bool.coe_iff_coe]
                    simp only [zero_add] at heo
                    simp_all only [getElem?_eq_none_iff, OBdd.low_heap_eq_heap, forall_exists_index,
                      Prod.forall, OBdd.high_heap_eq_heap, Fin.getElem_fin, Nat.sub_zero, zero_add,
                      Vector.getElem_cast]
                  ·
                    conv =>
                      rhs
                      congr
                      congr
                      congr
                      rfl
                      simp [cook_heap, RawNode.cook]
                      rfl
                      rfl
                    symm
                    have := (invh.2 ⟨(O.high O_root_def).1.root, (U.high U_root_def).1.root⟩ rh hh).2.2
                    calc _
                      _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rh.cook _⟩, _⟩ I := by
                        rw [push_evaluate]
                        · exact this.2.1
                        · exact push_ordered this.2.2.1
                        · exact this.2.2.1
                      _ = _ := by
                        have := this.2.2.2 I
                        simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                        exact this
                  ·
                    conv =>
                      rhs
                      congr
                      congr
                      congr
                      rfl
                      simp [cook_heap, RawNode.cook]
                      rfl
                      rfl
                    symm
                    have : sh.cache[(⟨(O.low O_root_def).1.root, (U.low U_root_def).1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                      apply (hhp.1 _).1
                      exact hl
                    have := invh.2 ⟨(O.low O_root_def).1.root, (U.low U_root_def).1.root⟩ rl this
                    calc _
                      _ = OBdd.evaluate ⟨⟨cook_heap sh.heap _, rl.cook _⟩, _⟩ I := by
                        rw [push_evaluate]
                        · exact this.2.2.2.1
                        · exact push_ordered this.2.2.2.2.1
                        · exact this.2.2.2.2.1
                      _ = _ := by
                        have := this.2.2.2.2.2 I
                        simp only [Vector.take_eq_extract, OBdd.high_heap_eq_heap] at this
                        exact this
                )
                (by
                  simp only [cache_get] at hc
                  cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                  | none => rfl
                  | some val =>
                    cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                    | none =>
                      have := ((hhp.1 _).2.2 heqq ⟨val, heq⟩).2
                      simp only [OBdd.high_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_high
                    | some val =>
                      have := ((hlp.1 _).2.2 hc ⟨_, heqq⟩).2
                      simp only [OBdd.low_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_low
                )
          ⟨ r,
            invv,
            (by rw [O_root_def, U_root_def] at hv; exact hv),
            .trans hsl (.trans hsh hsv),
            by
              constructor
              swap
              · rw [← O_root_def, ← U_root_def]
                exact hvp.2
              intro k
              constructor
              · intro p hp
                apply (hvp.1 _).1
                apply (hhp.1 _).1
                apply (hlp.1 _).1
                exact hp
              · constructor
                · intro hk
                  apply (hlp.1 _).2.1
                  apply (hhp.1 _).2.1
                  apply (hvp.1 _).2.1
                  exact hk
                · intro hk hkp
                  rw [← O_root_def, ← U_root_def]
                  cases heq : sh.cache[k]? with
                  | none =>
                    apply (hvp.1 _).2.2 heq hkp
                  | some w =>
                    cases heqq : sl.cache[k]? with
                    | none =>
                      have := (hhp.1 _).2.2 heqq ⟨_, heq⟩
                      constructor
                      · trans (O.high O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_high.2
                        · exact this.1
                      · trans (U.high U_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_high.2
                        · exact this.2
                    | some ww =>
                      have := (hlp.1 _).2.2 hk ⟨_, heqq⟩
                      constructor
                      · trans (O.low O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_low.2
                        · exact this.1
                      · trans (U.low U_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_low.2
                        · exact this.2
          ⟩
termination_by (O, U)
decreasing_by
  · right; exact oedge_of_low
  · right; exact oedge_of_high
  · left;  exact oedge_of_low
  · left;  exact oedge_of_high
  · left;  exact oedge_of_low
  · left;  exact oedge_of_high
  · right; exact oedge_of_low
  · right; exact oedge_of_high
  · left; exact oedge_of_low
  · left; exact oedge_of_high

def oapply (op : Bool → Bool → Bool) (O : OBdd n m) (U : OBdd n' m') :
    (s : Nat) ×
    { OU : OBdd (n ⊔ n') s //
      ∀ I,
        OBdd.evaluate OU I =
        (op
          (OBdd.evaluate O (Vector.cast (by simp) (I.take n)))
          (OBdd.evaluate U (Vector.cast (by simp) (I.take n'))))
    } :=
  let ⟨⟨state, root⟩, inv, ps⟩ := apply_helper op O U initial inv_initial
  ⟨ state.size,
    ⟨⟨cook_heap state.heap inv.1,
    root.cook (inv.2 _ root ps.1).2.2.2.1⟩,
    (inv.2 _ root ps.1).2.2.2.2.1⟩,
    (inv.2 _ root ps.1).2.2.2.2.2
  ⟩

end Apply
