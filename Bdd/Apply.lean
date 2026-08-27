module

public import Bdd.Basic
import Std.Data.HashMap.Lemmas

namespace Apply

open RawBdd

structure State n n' m m' where
  size : Nat
  heap : Vector (RawNode (max n n')) size
  cache : Std.HashMap (Pointer m × Pointer m') RawPointer

def initial {n n' m m'} : State n n' m m' :=
  ⟨_, (Vector.emptyWithCapacity (m ⊔ m')), Std.HashMap.emptyWithCapacity (m ⊔ m')⟩

def Invariant {n m n' m'} (op : Bool → Bool → Bool) (O_heap : Vector (Node n m) m)
    (U_heap : Vector (Node n' m') m') (r : State n n' m m') :=
  ∃ hh : (∀ i : Fin r.size, RawNode.Bounded i r.heap[i]),
    ∀ (k : (Pointer m × Pointer m')) (p : RawPointer),
      r.cache[k]? = some p →
      (∀ j h, p = .inr j → (r.heap[j]'h).va.1 =
        (k.1.toVarD O_heap (n ⊔ n')) ⊓ (k.2.toVarD U_heap (n ⊔ n'))) ∧
      ∃ hk1 : Bdd.Ordered ⟨O_heap, k.1⟩,
        ∃ hk2 : Bdd.Ordered ⟨U_heap, k.2⟩,
          ∃ hp : p.Bounded r.size,
            ∃ o : Bdd.Ordered ⟨cook_heap r.heap hh, p.cook hp⟩,
              ∀ I,
                OBdd.evaluate ⟨⟨cook_heap r.heap hh, p.cook hp⟩, o⟩ I =
                op
                  (OBdd.evaluate ⟨⟨O_heap, k.1⟩, hk1⟩ (Vector.cast (by simp) (I.take n)))
                  (OBdd.evaluate ⟨⟨U_heap, k.2⟩, hk2⟩ (Vector.cast (by simp) (I.take n')))

lemma inv_initial {n m n' m' op} {O : OBdd n m} {U : OBdd n' m'} : Invariant op O.bdd.heap U.bdd.heap initial := by
  constructor
  · intro k p hp
    simp only [initial, Std.HashMap.getElem?_emptyWithCapacity, reduceCtorEq] at hp
  · rintro ⟨_, c⟩
    simp only [initial, Nat.not_lt_zero] at c

def cache_get {m m' n n'} (O_root : Pointer m) (U_root : Pointer m') (s : (State n n' m m')) : (Option RawPointer) :=
  s.cache[(⟨O_root, U_root⟩ : (Pointer m × Pointer m'))]?

def heap_push {n n' m m'} (O : OBdd n m) (U : OBdd n' m') (N : RawNode (n ⊔ n'))
    (s : State n n' m m') : State n n' m m' × RawPointer :=
  ⟨⟨s.size + 1, s.heap.push N, s.cache.insert ⟨O.1.root, U.1.root⟩ (.inr s.size)⟩, .inr s.size⟩

lemma heap_push_aux {n n' m m' op} {O : OBdd n m} {U : OBdd n' m'} {N} (s : (State n n' m m'))
    (inv : Invariant op O.bdd.heap U.bdd.heap s)
    (hNl : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.hi)
    (hNv : N.va.1 = O.bdd.root.toVarD O.1.heap (n ⊔ n') ⊓ U.bdd.root.toVarD U.1.heap (n ⊔ n'))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _) (I : Vector Bool (max n n')),
      OBdd.evaluate ⟨{ heap := cook_heap (s.heap.push N) h0, root := Pointer.node ⟨s.size, by simp⟩ }, h1⟩ I =
      op (O.evaluate (Vector.cast (by omega) (I.extract 0 n))) (U.evaluate (Vector.cast (by omega) (I.extract 0 n')))) :
    Invariant op O.bdd.heap U.bdd.heap (heap_push O U N s).1 := by
  rcases hNl with ⟨kl, hkl⟩
  rcases hNh with ⟨kh, hkh⟩
  obtain ⟨_, _, _, hb_lo, ho_lo, _⟩ := inv.2 kl N.lo hkl
  obtain ⟨_, _, _, hb_hi, ho_hi, _⟩ := inv.2 kh N.hi hkh
  have hN : RawNode.Bounded s.size N := ⟨hb_lo, hb_hi⟩
  have : ∀ (i : Fin (s.size + 1)), RawNode.Bounded (↑i) (s.heap.push N)[i] := by
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
  have hb : RawPointer.Bounded (s.size + 1) (Sum.inr s.size) := by
    simp only [RawPointer.bounded_inr_iff, Nat.lt_add_one]
  simp only [heap_push]
  intro k p hp
  rw [Std.HashMap.getElem?_insert] at hp
  simp only [beq_iff_eq] at hp
  split at hp
  next heq =>
    subst heq
    simp only
    constructor
    · grind only [= Vector.getElem_push]
    · use O.2, U.2
      injection hp with hpe
      subst hpe
      use hb
      have hoo : Bdd.Ordered ⟨cook_heap (s.heap.push N) this, RawPointer.cook (Sum.inr s.size) hb⟩ := by
        apply Bdd.ordered_of_low_high_ordered (by rw [RawPointer.cook_inr, Pointer.node.injEq])
        · simp only [Bdd.low_eq, cook_heap_eq]
          simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
          rw [cook_low]
          convert push_ordered ho_lo
          rw [cook_heap_eq (hh := this)]; rfl
        · simp [Nat.succ_eq_add_one, Bdd.var_eq, cook_heap_eq, Bdd.low_eq, RawPointer.cook_inr]
          cases heq : N.lo with
          | inl val =>
            rw [cook_low]
            simp_rw [heq]
            simp only [RawNode.cook_eq, RawPointer.cook_inl, Pointer.toVar_terminal,
              Nat.succ_eq_add_one, Fin.lt_def, Pointer.toVar_node, Fin.getElem_fin,
              Vector.getElem_ofFn, Vector.getElem_push_eq, lt_sup_iff]
            omega
          | inr val =>
            rw [heq, RawPointer.bounded_inr_iff] at hb_lo
            rw [cook_low]
            simp_rw [heq]
            simp only [RawNode.cook_eq, RawPointer.cook_inr, Fin.lt_def, Nat.succ_eq_add_one,
              Pointer.toVar_node, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
            rw [Vector.getElem_push_lt]
            exact hxl _ hb_lo heq
        · simp only [Bdd.high_eq, cook_heap_eq]
          simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
          rw [cook_high]
          convert push_ordered ho_hi
          rw [cook_heap_eq (hh := this)]; rfl
        · simp [Nat.succ_eq_add_one, Bdd.var_eq, cook_heap_eq, Bdd.high_eq, RawPointer.cook_inr]
          cases heq : N.hi with
          | inl val =>
            rw [cook_high]
            simp_rw [heq]
            simp only [RawPointer.cook_inl, Fin.lt_def, Nat.succ_eq_add_one, Pointer.toVar_node]
            simp only [RawNode.cook_eq, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq,
              Pointer.toVar_terminal, Nat.succ_eq_add_one, lt_sup_iff]
            omega
          | inr val =>
            rw [heq, RawPointer.bounded_inr_iff] at hb_hi
            rw [cook_high]
            simp_rw [heq]
            simp only [RawNode.cook_eq, RawPointer.cook_inr]
            simp_rw [Fin.lt_def, Nat.succ_eq_add_one, Pointer.toVar_node, Fin.getElem_fin,
              Vector.getElem_ofFn, Vector.getElem_push_eq]
            rw [Vector.getElem_push_lt]
            exact hxh _ hb_hi heq
      use hoo
      simp only [OBdd.mk_eq_self, RawPointer.cook_inr] at ⊢ hoo
      intro I
      apply hh _ hoo
  next heq =>
    obtain ⟨inv1, hok, huk, hbp, hop, heval⟩ := inv.2 k p hp
    have hbp' : RawPointer.Bounded (s.size + 1) p :=
        RawPointer.bounded_of_le hbp (by omega)
    constructor
    · intro j hs hj
      rw [hj] at hp
      rw [RawPointer.bounded_iff] at hbp
      rw [Vector.getElem_push_lt (hbp hj)]
      exact inv1 j (hbp hj) hj
    use hok, huk, hbp', push_ordered hop
    intro I
    calc _
      _ = OBdd.evaluate ⟨{ heap := cook_heap (s.heap) inv.1, root := p.cook hbp }, hop⟩ I := by
        rw [OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq]
        · simp only [Fin.getElem_fin]
          intro j hj
          use (by omega)
          simp [cook_heap_eq]
          exact RawNode.cook_equiv
        · simp only [RawPointer.cook_equiv]
    exact heval I

lemma heap_push_correct {n n' m m' op} {O : OBdd n m} {U : OBdd n' m'} (N : RawNode (n ⊔ n'))
    {s : State n n' m m'} {r} (heq : r = heap_push O U N s)
    (inv : Invariant op O.bdd.heap U.bdd.heap s)
    (hNl : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.hi)
    (hNv : N.va.1 = O.bdd.root.toVarD O.1.heap (n ⊔ n') ⊓ U.bdd.root.toVarD U.1.heap (n ⊔ n'))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _) (I : Vector Bool (max n n')),
            OBdd.evaluate ⟨{ heap := cook_heap (s.heap.push N) h0, root := Pointer.node ⟨s.size, by simp⟩ }, h1⟩ I =
            op (O.evaluate (Vector.cast (by omega) (I.extract 0 n))) (U.evaluate (Vector.cast (by omega) (I.extract 0 n'))))
            (hc : s.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = none ) :
    (Invariant op O.bdd.heap U.bdd.heap r.1) ∧
    (r.1.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some r.2) ∧
    s.size ≤ r.1.size ∧
    (∀ (k : Pointer m × Pointer m'),
      (∀ p, s.cache[k]? = some p → r.1.cache[k]? = some p) ∧
      (r.1.cache[k]? = none → s.cache[k]? = none) ∧
      (s.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) →
      Pointer.Reachable O.1.heap O.1.root k.1 ∧ Pointer.Reachable U.1.heap U.1.root k.2)) := by
    subst heq
    split_ands
    · exact heap_push_aux s inv hNl hNh hNv hxl hxh hh
    · simp only [heap_push, Std.HashMap.getElem?_insert_self]
    · simp only [heap_push, Nat.le_add_right]
    · intro k
      constructor
      · intro p hkp
        rw [← hkp]
        simp only [heap_push, Std.HashMap.getElem?_insert, beq_iff_eq, ite_eq_right_iff]
        intro contra
        rw [← contra] at hkp
        rw [hkp] at hc
        contradiction
      · constructor
        · simp only [heap_push, getElem?_eq_none_iff, Std.HashMap.mem_insert, beq_iff_eq, not_or,
            and_imp, imp_self, implies_true]
        · rintro hk ⟨q, hq⟩
          simp only [heap_push, Std.HashMap.getElem?_insert, beq_iff_eq] at hq
          split at hq
          next heqq => subst heqq; constructor <;> exact .refl
          next heqq => rw [hk] at hq; contradiction

lemma insert_terminal_invariant {n n' m m' op} {O : OBdd n m} {U : OBdd n' m'} {b b'}
    (s0 : State n n' m m') (inv : Invariant op O.bdd.heap U.bdd.heap s0)
    (ho : O.1.root = .terminal b) (hu : U.1.root = .terminal b') :
    Invariant op O.bdd.heap U.bdd.heap { size := s0.size, heap := s0.heap, cache := s0.cache.insert (O.1.root, U.1.root) (Sum.inl (op b b')) } := by
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
    use RawPointer.bounded_inl
    simp [RawPointer.cook_inl, ho, hu, Bdd.ordered_of_terminal]
  next =>
    constructor
    · exact (inv.2 _ _ hp).1
    exact (inv.2 _ _ hp).2

lemma op_if1 (op : Bool → Bool → Bool) {c l rt rf : Bool} :
    op l (if c then rt else rf) = if c then (op l rt) else (op l rf) :=
  apply_ite (op l) (c = true) rt rf

lemma op_if2 (op : Bool → Bool → Bool) {c lt lf r : Bool} :
    op  (if c then lt else lf) r = if c then (op lt r) else (op lf r) := by
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only [Bool.not_eq_true]

lemma op_if3 (op : Bool → Bool → Bool) {c lt lf rt rf : Bool} :
    op (if c then lt else lf) (if c then rt else rf) = if c then (op lt rt) else (op lf rf) := by
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only [Bool.not_eq_true]

lemma aux_lt1_low {n m n' m' b j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .terminal b) (U_root_def : U.1.root = .node j') :
    U.1.heap[j'].var.1 <
    min (O.bdd.root.toVarD O.1.heap (max n n'))
        (U.bdd.heap[j'].low.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := U_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt1_high {n m n' m' b j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .terminal b) (U_root_def : U.1.root = .node j') :
    U.1.heap[j'].var.1 <
    min (O.bdd.root.toVarD O.1.heap (max n n'))
        (U.bdd.heap[j'].high.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt2_low {n m n' m' j b'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .terminal b') :
    O.1.heap[j].var.1 <
    min (O.bdd.heap[j].low.toVarD O.1.heap (max n n'))
        (U.bdd.root.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt2_high {n m n' m' j b'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .terminal b') :
    O.1.heap[j].var.1 <
    min (O.bdd.heap[j].high.toVarD O.1.heap (max n n'))
        (U.bdd.root.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt3_low {n m n' m' j j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j')
    (hleq : O.1.heap[j].var.1 < U.1.heap[j'].var.1) :
    O.1.heap[j].var.1 <
    min (O.bdd.heap[j].low.toVarD O.1.heap (max n n'))
        (U.bdd.root.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt3_high {n m n' m' j j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j')
    (hleq : O.1.heap[j].var.1 < U.1.heap[j'].var.1) :
    O.1.heap[j].var.1 <
    min (O.bdd.heap[j].high.toVarD O.1.heap (max n n'))
        (U.bdd.root.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt4_low {n m n' m' j j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j')
    (hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (O.bdd.root.toVarD O.1.heap (max n n'))
        (U.bdd.heap[j'].low.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt4_high {n m n' m' j j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j')
    (hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (O.bdd.root.toVarD O.1.heap (max n n'))
        (U.bdd.heap[j'].high.toVarD U.1.heap (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var_eq, Pointer.toVarD]
  split <;> simp_all

lemma aux_lt5_low {n m n' m' j j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j')
    (heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (O.bdd.heap[j].low.toVarD O.1.heap (max n n'))
        (U.bdd.heap[j'].low.toVarD U.1.heap (max n n')) := by
  have h1 := OBdd.var_lt_low_var (h := O_root_def)
  have h2 := OBdd.var_lt_high_var (h := O_root_def)
  have h3 := OBdd.var_lt_low_var (h := U_root_def)
  have h4 := OBdd.var_lt_high_var (h := U_root_def)
  have h5 : U.1.heap[↑j'].var.1 < n + 1 := by omega
  simp_all [OBdd.var_eq, Pointer.toVarD]
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

lemma aux_lt5_high {n m n' m' j j'} {O : OBdd n m} {U : OBdd n' m'}
    (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j')
    (heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (O.bdd.heap[j].high.toVarD O.1.heap (max n n'))
        (U.bdd.heap[j'].high.toVarD U.1.heap (max n n')) := by
  have h2 := OBdd.var_lt_high_var (h := O_root_def)
  have h3 := OBdd.var_lt_low_var (h := U_root_def)
  have h4 := OBdd.var_lt_high_var (h := U_root_def)
  have h5 : U.1.heap[↑j'].var.1 < n + 1 := by omega
  simp_all [OBdd.var_eq, Pointer.toVarD]
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

def apply_helper {n m n' m'} (op : (Bool → Bool → Bool)) (O : OBdd n m) (U : OBdd n' m')
    (s0 : State n n' m m') :
    State n n' m m' × RawPointer :=
  match hc : cache_get O.1.root U.1.root s0 with
  | some root => ⟨s0, root⟩
  | none =>
    match O_root_def : O.1.root with
    | .terminal b =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        ⟨⟨s0.size, s0.heap, s0.cache.insert ⟨O.1.root, U.1.root⟩ (.inl (op b b'))⟩, .inl (op b b')⟩
      | .node j' =>
        let ⟨sl, rl⟩ := apply_helper op O (U.low U_root_def) s0
        let ⟨sh, rh⟩ := apply_helper op O (U.high U_root_def) sl
        heap_push O U ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh
    | .node j =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        let ⟨sl, rl⟩ := apply_helper op (O.low O_root_def) U s0
        let ⟨sh, rh⟩ := apply_helper op (O.high O_root_def) U sl
        heap_push O U ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh
      | .node j' =>
        if hlt : O.1.heap[j].var.1 < U.1.heap[j'].var.1
        then
          let ⟨sl, rl⟩ := apply_helper op (O.low O_root_def) U s0
          let ⟨sh, rh⟩ := apply_helper op (O.high O_root_def) U sl
          heap_push O U ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh
        else
          if hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1
          then
            let ⟨sl, rl⟩ := apply_helper op O (U.low U_root_def) s0
            let ⟨sh, rh⟩ := apply_helper op O (U.high U_root_def) sl
            heap_push O U ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh
          else
            let ⟨sl, rl⟩ := apply_helper op (O.low O_root_def) (U.low U_root_def) s0
            let ⟨sh, rh⟩ := apply_helper op (O.high O_root_def) (U.high U_root_def) sl
           heap_push O U ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh
termination_by (O, U)

set_option maxHeartbeats 300000 in
lemma apply_helper_correct {n m n' m'} (op : (Bool → Bool → Bool)) (O : OBdd n m) (U : OBdd n' m')
    (s0 : State n n' m m') (inv : Invariant op O.bdd.heap U.bdd.heap s0)
    {r} (heq : r = apply_helper op O U s0) :
    (Invariant op O.bdd.heap U.bdd.heap r.1) ∧
    (r.1.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some r.2) ∧
    (s0.size ≤ r.1.size) ∧
    (∀ (k : Pointer m × Pointer m'),
      (∀ p, s0.cache[k]? = some p → r.1.cache[k]? = some p) ∧
      (r.1.cache[k]? = none → s0.cache[k]? = none) ∧
      (s0.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) →
      Pointer.Reachable O.1.heap O.1.root k.1 ∧ Pointer.Reachable U.1.heap U.1.root k.2)) := by
  rcases heq with ⟨rfl, rfl⟩
  fun_induction apply_helper with
  | case1 O U s0 root hc => exact ⟨inv, hc, .refl, by grind only⟩
  | case2 O U s0 hc b O_root_def b' U_root_def =>
    split_ands
    · exact insert_terminal_invariant s0 inv O_root_def U_root_def
    · simp only [O_root_def, U_root_def, Std.HashMap.getElem?_insert_self]
    · exact .refl
    · intro k
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
            simp only [O_root_def, Pointer.Reachable.refl, U_root_def, and_self]
          next heq => rw [h1] at hp; contradiction
  | case3 O U s0 hc b O_root_def j' U_root_def sl rl heql sh rh heqh ihl ihh =>
    simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, OBdd.high_heap_eq_heap,
      OBdd.high_root_eq_high, heql, heqh] at ihl ihh
    have ⟨invl, hl, hsl, hlp⟩ := ihl inv
    have ⟨invh, hh, hsh, hhp⟩ := ihh invl
    let N : RawNode (max n n') := ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩
    let r := heap_push O U N
    have ⟨invv, hv, hsv, hvp⟩ := heap_push_correct N rfl invh
      (by
        use ⟨O.1.root, U.bdd.heap[j'].low⟩
        simp only [N]
        exact (hhp _).1 _ hl
      )
      ⟨_, hh⟩
      (by
        simp only [N]
        rw [O_root_def, U_root_def]
        simp only [Fin.getElem_fin, Pointer.toVarD, le_sup_iff, Fin.is_le', or_true,
          inf_of_le_right]
      )
      (by
        simp only [N]
        intro j hj1 hj2
        have := (hhp _).1 _ hl
        rw [hj2] at this
        have that := (invh.2 _ (.inr j) this).1 _ hj1 rfl
        simp only at that
        rw [that]
        exact aux_lt1_low O_root_def U_root_def
      )
      (by
        intro j hj1 hj2
        simp only [N]
        have := (invh.2 _ _ hh).1 _ hj1 hj2
        rw [this]
        exact aux_lt1_high O_root_def U_root_def
      )
      (by
        intro h0 h1 I
        simp only [OBdd.evaluate_node U_root_def, OBdd.evaluate_terminal O_root_def]
        rw [op_if1 op]
        simp only [Pointer.node.injEq, OBdd.evaluate_node, Fin.getElem_fin, Vector.getElem_cast]
        congr 1
        · simp only [cook_heap_eq, RawNode.cook_eq, Vector.getElem_ofFn]
          grind only [= Fin.getElem_fin, Vector.getElem_extract, = Vector.getElem_push]
        · have ⟨h1, h2, h3, h4, h5, h6⟩ := invh.2 ⟨O.1.root, U.bdd.heap[j'].high⟩ rh hh
          simp only [OBdd.mk_eq_self, OBdd.mk_eq_high U_root_def] at h6
          rw [O.evaluate_terminal O_root_def] at h6
          rw [push_evaluate (OBdd.high_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · exact h6 I
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.high_root_eq_high,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
        · have : sh.cache[(⟨O.1.root, U.bdd.heap[j'].low⟩ : Pointer m × Pointer m')]? = some rl := by
            apply (hhp _).1
            exact hl
          have ⟨h1, h2, h3, h4, h5, h6⟩ := invh.2 ⟨O.1.root, U.bdd.heap[j'].low⟩ rl this
          simp only [OBdd.mk_eq_self, U.mk_eq_low U_root_def] at h6
          rw [O.evaluate_terminal O_root_def] at h6
          rw [push_evaluate (OBdd.low_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · exact h6 I
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.low_root_eq_low,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
      )
      (by
        simp only [cache_get] at hc
        cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
        | none => rfl
        | some val =>
          cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
          | none =>
            absurd ((hhp _).2.2 heqq ⟨val, heq⟩).2
            exact OBdd.not_reachable_high_root U_root_def
          | some val =>
            absurd ((hlp _).2.2 hc ⟨_, heqq⟩).2
            exact OBdd.not_reachable_low_root U_root_def
      )
    split_ands
    · exact invv
    · exact hv
    · exact .trans hsl (.trans hsh hsv)
    · intro k
      constructor
      · intro p hp
        apply (hvp _).1
        apply (hhp _).1
        apply (hlp _).1
        exact hp
      · constructor
        · intro hk
          apply (hlp _).2.1
          apply (hhp _).2.1
          apply (hvp _).2.1
          exact hk
        · intro hk hkp
          cases heq : sh.cache[k]? with
          | none =>
            apply (hvp _).2.2 heq hkp
          | some w =>
            cases heqq : sl.cache[k]? with
            | none =>
              have := (hhp _).2.2 heqq ⟨_, heq⟩
              constructor
              · exact this.1
              · exact .trans (U.bdd.reachable_high U_root_def) this.2
            | some ww =>
              have := (hlp _).2.2 hk ⟨_, heqq⟩
              constructor
              · exact this.1
              · exact .trans (U.bdd.reachable_low U_root_def) this.2
  | case4 O U s0 hc j O_root_def b' U_root_def sl rl heql sh rh heqh ihl ihh =>
    simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, OBdd.high_heap_eq_heap,
      OBdd.high_root_eq_high, heql, heqh] at ihl ihh
    have ⟨invl, hl, hsl, hlp⟩ := ihl inv
    have ⟨invh, hh, hsh, hhp⟩ := ihh invl
    clear inv ihl ihh
    let N : RawNode (max n n') := ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩
    let r := heap_push O U N
    have ⟨invv, hv, hsv, hvp⟩ := heap_push_correct N rfl invh
      ⟨_, (hhp _).1 _ hl⟩
      ⟨_, hh⟩
      (by
        simp only [N]
        rw [O_root_def, U_root_def]
        simp only [Fin.getElem_fin, Pointer.toVarD, le_sup_iff, Fin.is_le', true_or, inf_of_le_left]
      )
      (by
        simp only [N]
        intro j hj1 hj2
        have := (hhp _).1 _ hl
        rw [hj2] at this
        have that := (invh.2 _ (.inr j) this).1 _ hj1 rfl
        simp only at that
        rw [that]
        exact aux_lt2_low O_root_def U_root_def
      )
      (by
        simp only [N]
        intro j hj1 hj2
        have := (invh.2 _ _ hh).1 _ hj1 hj2
        rw [this]
        exact aux_lt2_high O_root_def U_root_def
      )
      (by
        intro h0 h1 I
        simp only [OBdd.evaluate_node O_root_def, OBdd.evaluate_terminal U_root_def]
        rw [op_if2 op]
        simp only [Pointer.node.injEq, OBdd.evaluate_node, Fin.getElem_fin, Vector.getElem_cast]
        congr 1
        · simp only [cook_heap_eq, RawNode.cook_eq, Vector.getElem_ofFn]
          grind only [= Fin.getElem_fin, Vector.getElem_extract, = Vector.getElem_push]
        · have h := invh.2 ⟨O.bdd.heap[j].high, U.1.root⟩ rh hh
          rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
          simp only [O.mk_eq_high O_root_def, Vector.take_eq_extract, OBdd.mk_eq_self,
            U.evaluate_terminal U_root_def] at h6
          rw [push_evaluate (OBdd.high_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · exact h6 I
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.high_root_eq_high,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
        · have : sh.cache[(⟨O.bdd.heap[j].low, U.1.root⟩ : Pointer m × Pointer m')]? = some rl := by
            apply (hhp _).1
            exact hl
          have ⟨h1, h2, h3, h4, h5, h6⟩ := invh.2 ⟨O.bdd.heap[j].low, U.1.root⟩ rl this
          simp only [OBdd.mk_eq_low O_root_def, Vector.take_eq_extract, OBdd.mk_eq_self,
            U.evaluate_terminal U_root_def] at h6
          rw [push_evaluate (OBdd.low_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · exact h6 I
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.low_root_eq_low,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
      )
      (by
        simp only [cache_get] at hc
        cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
        | none => rfl
        | some val =>
          cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
          | none =>
            absurd ((hhp _).2.2 heqq ⟨val, heq⟩).1
            exact OBdd.not_reachable_high_root O_root_def
          | some val =>
            absurd ((hlp _).2.2 hc ⟨_, heqq⟩).1
            exact OBdd.not_reachable_low_root O_root_def
      )
    split_ands
    · exact invv
    · exact hv
    · exact .trans hsl (.trans hsh hsv)
    · intro k
      constructor
      · intro p hp
        apply (hvp _).1
        apply (hhp _).1
        apply (hlp _).1
        exact hp
      · constructor
        · intro hk
          apply (hlp _).2.1
          apply (hhp _).2.1
          apply (hvp _).2.1
          exact hk
        · intro hk hkp
          cases heq : sh.cache[k]? with
          | none =>
            apply (hvp _).2.2 heq hkp
          | some w =>
            cases heqq : sl.cache[k]? with
            | none =>
              have := (hhp _).2.2 heqq ⟨_, heq⟩
              constructor
              · exact .trans (O.bdd.reachable_high O_root_def) this.1
              · exact this.2
            | some ww =>
              have := (hlp _).2.2 hk ⟨_, heqq⟩
              constructor
              · exact .trans (O.bdd.reachable_low O_root_def) this.1
              · exact this.2
  | case5 O U s0 hc j O_root_def j' U_root_def hlt sl rl heql sh rh heqh ihl ihh =>
    simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, OBdd.high_heap_eq_heap,
      OBdd.high_root_eq_high, heql, heqh] at ihl ihh
    have ⟨invl, hl, hsl, hlp⟩ := ihl inv
    have ⟨invh, hh, hsh, hhp⟩ := ihh invl
    let N : RawNode (max n n') := ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩
    let r := heap_push O U N
    have ⟨invv, hv, hsv, hvp⟩ := heap_push_correct N rfl invh
      ⟨_, (hhp _).1 _ hl⟩
      ⟨_, hh⟩
      (by
        simp only [N]
        rw [O_root_def, U_root_def]
        simp only [Fin.getElem_fin, Pointer.toVarD]
        exact Eq.symm (min_eq_left_of_lt hlt)
      )
      (by
        simp only [N]
        intro j'' hj1 hj2
        have := (hhp _).1 _ hl
        rw [hj2] at this
        have that := (invh.2 _ _ this).1 _ hj1 rfl
        simp only at that
        rw [that]
        exact aux_lt3_low O_root_def U_root_def hlt
      )
      (by
        simp only [N]
        intro j'' hj1 hj2
        have := (invh.2 _ _ hh).1 _ hj1 hj2
        rw [this]
        exact aux_lt3_high O_root_def U_root_def hlt
      )
      (by
        intro h0 h1 I
        simp only [OBdd.evaluate_node O_root_def, OBdd.evaluate_node U_root_def]
        rw [op_if2 op]
        simp only [Pointer.node.injEq, OBdd.evaluate_node, Fin.getElem_fin, Vector.getElem_cast]
        congr 1
        · simp only [cook_heap_eq, RawNode.cook_eq, Vector.getElem_ofFn]
          grind only [= Fin.getElem_fin, Vector.getElem_extract, = Vector.getElem_push]
        · have ⟨h1, h2, h3, h4, h5, h6⟩ := invh.2 ⟨O.bdd.heap[j].high, U.1.root⟩ rh hh
          simp only [OBdd.mk_eq_high O_root_def, Vector.take_eq_extract, OBdd.mk_eq_self] at h6
          rw [push_evaluate (OBdd.high_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · simp_all only [Fin.getElem_fin, Pointer.node.injEq, OBdd.evaluate_node,
              Vector.getElem_cast]
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.high_root_eq_high,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
        · have : sh.cache[(⟨O.bdd.heap[j].low, U.1.root⟩ : Pointer m × Pointer m')]? = some rl := by
            apply (hhp _).1
            exact hl
          have h := invh.2 ⟨O.bdd.heap[j].low, U.1.root⟩ rl this
          rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
          simp only [O.mk_eq_low O_root_def, Vector.take_eq_extract, OBdd.mk_eq_self] at h6
          rw [push_evaluate (OBdd.low_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · simp_all only [Fin.getElem_fin, Pointer.node.injEq, OBdd.evaluate_node,
              Vector.getElem_cast]
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.low_root_eq_low,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
      )
      (by
        simp only [cache_get] at hc
        cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
        | none => rfl
        | some val =>
          cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
          | none =>
            absurd ((hhp _).2.2 heqq ⟨val, heq⟩).1
            exact OBdd.not_reachable_high_root O_root_def
          | some val =>
            absurd ((hlp _).2.2 hc ⟨_, heqq⟩).1
            exact OBdd.not_reachable_low_root O_root_def
      )
    split_ands
    · exact invv
    · exact hv
    · exact .trans hsl (.trans hsh hsv)
    · intro k
      constructor
      · intro p hp
        apply (hvp _).1
        apply (hhp _).1
        apply (hlp _).1
        exact hp
      · constructor
        · intro hk
          apply (hlp _).2.1
          apply (hhp _).2.1
          apply (hvp _).2.1
          exact hk
        · intro hk hkp
          cases heq : sh.cache[k]? with
          | none =>
            apply (hvp _).2.2 heq hkp
          | some w =>
            cases heqq : sl.cache[k]? with
            | none =>
              have := (hhp _).2.2 heqq ⟨_, heq⟩
              constructor
              · exact .trans (O.bdd.reachable_high O_root_def) this.1
              · exact this.2
            | some ww =>
              have := (hlp _).2.2 hk ⟨_, heqq⟩
              constructor
              · exact .trans (O.bdd.reachable_low O_root_def) this.1
              · exact this.2
  | case6 O U s0 hc j O_root_def j' U_root_def _ hgt sl rl heql sh rh heqh ihl ihh =>
    simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, OBdd.high_heap_eq_heap,
      OBdd.high_root_eq_high, heql, heqh] at ihl ihh
    have ⟨invl, hl, hsl, hlp⟩ := ihl inv
    have ⟨invh, hh, hsh, hhp⟩ := ihh invl
    let N : RawNode (max n n') := ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩
    let r := heap_push O U N
    have ⟨invv, hv, hsv, hvp⟩ := heap_push_correct N rfl invh
      ⟨_, (hhp _).1 _ hl⟩
      ⟨_, hh⟩
      (by
        simp only [N]
        rw [O_root_def, U_root_def]
        simp only [Fin.getElem_fin, Pointer.toVarD]
        exact Eq.symm (min_eq_right_of_lt hgt)
      )
      (by
        simp only [N]
        intro j'' hj1 hj2
        have := (hhp _).1 _ hl
        rw [hj2] at this
        have that := (invh.2 _ _ this).1 _ hj1 rfl
        simp only at that
        rw [that]
        exact aux_lt4_low O_root_def U_root_def hgt
      )
      (by
        simp only [N]
        intro j'' hj1 hj2
        have := (invh.2 _ _ hh).1 _ hj1 hj2
        rw [this]
        exact aux_lt4_high O_root_def U_root_def hgt
      )
      (by
        intro h0 h1 I
        simp only [OBdd.evaluate_node O_root_def, OBdd.evaluate_node U_root_def]
        rw [op_if1 op]
        simp only [Pointer.node.injEq, OBdd.evaluate_node, Fin.getElem_fin, Vector.getElem_cast]
        congr 1
        · simp only [cook_heap_eq, RawNode.cook_eq, Vector.getElem_ofFn]
          grind only [= Fin.getElem_fin, Vector.getElem_extract, = Vector.getElem_push]
        · have ⟨h1, h2, h3, h4, h5, h6⟩ := invh.2 ⟨O.1.root, U.bdd.heap[j'].high⟩ rh hh
          simp only [OBdd.mk_eq_self, Vector.take_eq_extract, U.mk_eq_high U_root_def] at h6
          rw [push_evaluate (OBdd.high_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · simp_all only [Fin.getElem_fin, Pointer.node.injEq, OBdd.evaluate_node,
              Vector.getElem_cast]
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.high_root_eq_high,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
        · have : sh.cache[(⟨O.1.root, U.bdd.heap[j'].low⟩ : Pointer m × Pointer m')]? = some rl := by
            apply (hhp _).1
            exact hl
          have h := invh.2 ⟨O.1.root, U.bdd.heap[j'].low⟩ rl this
          rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
          simp only [OBdd.mk_eq_self, Vector.take_eq_extract, U.mk_eq_low U_root_def] at h6
          rw [push_evaluate (OBdd.low_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · simp_all only [Fin.getElem_fin, Pointer.node.injEq, OBdd.evaluate_node,
              Vector.getElem_cast]
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.low_root_eq_low,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
      )
      (by
        simp only [cache_get] at hc
        cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
        | none => rfl
        | some val =>
          cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
          | none =>
            absurd ((hhp _).2.2 heqq ⟨val, heq⟩).2
            exact OBdd.not_reachable_high_root U_root_def
          | some val =>
            absurd ((hlp _).2.2 hc ⟨_, heqq⟩).2
            exact OBdd.not_reachable_low_root U_root_def
      )
    split_ands
    · exact invv
    · exact hv
    · exact .trans hsl (.trans hsh hsv)
    · intro k
      constructor
      · intro p hp
        apply (hvp _).1
        apply (hhp _).1
        apply (hlp _).1
        exact hp
      · constructor
        · intro hk
          apply (hlp _).2.1
          apply (hhp _).2.1
          apply (hvp _).2.1
          exact hk
        · intro hk hkp
          cases heq : sh.cache[k]? with
          | none =>
            apply (hvp _).2.2 heq hkp
          | some w =>
            cases heqq : sl.cache[k]? with
            | none =>
              have := (hhp _).2.2 heqq ⟨_, heq⟩
              constructor
              · exact this.1
              · exact .trans (U.bdd.reachable_high U_root_def) this.2
            | some ww =>
              have := (hlp _).2.2 hk ⟨_, heqq⟩
              constructor
              · exact this.1
              · exact .trans (U.bdd.reachable_low U_root_def) this.2

  | case7 O U s0 hc j O_root_def j' U_root_def _ hgt sl rl heql sh rh heqh ihl ihh =>
    simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, OBdd.high_heap_eq_heap,
      OBdd.high_root_eq_high, heql, heqh] at ihl ihh
    have ⟨invl, hl, hsl, hlp⟩ := ihl inv
    have ⟨invh, hh, hsh, hhp⟩ := ihh invl
    let N : RawNode (max n n') := ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩
    let r := heap_push O U N
    have ⟨invv, hv, hsv, hvp⟩ := heap_push_correct N rfl invh
      ⟨_, (hhp _).1 _ hl⟩
      ⟨_, hh⟩
      (by
        simp only [N]
        rw [O_root_def, U_root_def]
        simp only [Fin.getElem_fin, Pointer.toVarD]
        have heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1 := by omega
        simp only [Fin.getElem_fin] at heeq
        rw [heeq]
        simp only [min_self]
      )
      (by
        simp only [N]
        intro j'' hj1 hj2
        have := (hhp _).1 _ hl
        rw [hj2] at this
        have that := (invh.2 _ _ this).1 _ hj1 rfl
        simp only at that
        rw [that]
        exact aux_lt5_low O_root_def U_root_def (by omega)
      )
      (by
        simp only [N]
        intro j'' hj1 hj2
        have := (invh.2 _ _ hh).1 _ hj1 hj2
        rw [this]
        exact aux_lt5_high O_root_def U_root_def (by omega)
      )
      (by
        intro h0 h1 I
        simp only [OBdd.evaluate_node U_root_def, OBdd.evaluate_node O_root_def]
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
        simp only [Pointer.node.injEq, OBdd.evaluate_node, Fin.getElem_fin, Vector.getElem_cast]
        congr 1
        · simp only [cook_heap_eq, RawNode.cook_eq, Vector.getElem_ofFn]
          grind only [= Fin.getElem_fin, Vector.getElem_extract, = Vector.getElem_push]
        · have h := invh.2 ⟨O.bdd.heap[j].high, U.bdd.heap[j'].high⟩ rh hh
          rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
          simp only [OBdd.mk_eq_high O_root_def, OBdd.mk_eq_high U_root_def] at h6
          rw [push_evaluate (OBdd.high_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · exact h6 I
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.high_root_eq_high,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
        · have : sh.cache[(⟨O.bdd.heap[j].low, U.bdd.heap[j'].low⟩ : Pointer m × Pointer m')]? = some rl := by
            apply (hhp _).1
            exact hl
          have h := invh.2 ⟨O.bdd.heap[j].low, U.bdd.heap[j'].low⟩ rl this
          rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
          simp only [OBdd.mk_eq_low O_root_def, OBdd.mk_eq_low U_root_def] at h6
          rw [push_evaluate (OBdd.low_heap_eq_heap _) (h0 := h0) (ho := h5)]
          · exact h6 I
          · simp only [Fin.getElem_fin, cook_heap_eq, RawNode.cook_eq, OBdd.low_root_eq_low,
              Vector.getElem_ofFn, Vector.getElem_push_eq, N]
          · grind only [RawPointer.bounded_iff]
      )
      (by
        simp only [cache_get] at hc
        cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
        | none => rfl
        | some val =>
          cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
          | none =>
            absurd ((hhp _).2.2 heqq ⟨val, heq⟩).2
            exact OBdd.not_reachable_high_root U_root_def
          | some val =>
            absurd ((hlp _).2.2 hc ⟨_, heqq⟩).2
            exact OBdd.not_reachable_low_root U_root_def
      )
    split_ands
    · exact invv
    · exact hv
    · exact .trans hsl (.trans hsh hsv)
    · intro k
      constructor
      · intro p hp
        apply (hvp _).1
        apply (hhp _).1
        apply (hlp _).1
        exact hp
      · constructor
        · intro hk
          apply (hlp _).2.1
          apply (hhp _).2.1
          apply (hvp _).2.1
          exact hk
        · intro hk hkp
          cases heq : sh.cache[k]? with
          | none =>
            apply (hvp _).2.2 heq hkp
          | some w =>
            cases heqq : sl.cache[k]? with
            | none =>
              have := (hhp _).2.2 heqq ⟨_, heq⟩
              constructor
              · exact .trans (O.bdd.reachable_high O_root_def) this.1
              · exact .trans (U.bdd.reachable_high U_root_def) this.2
            | some ww =>
              have := (hlp _).2.2 hk ⟨_, heqq⟩
              constructor
              · exact .trans (O.bdd.reachable_low O_root_def) this.1
              · exact .trans (U.bdd.reachable_low U_root_def) this.2

public def oapply {n m n' m'} (op : Bool → Bool → Bool) (O : OBdd n m) (U : OBdd n' m') :
    (s : Nat) × OBdd (n ⊔ n') s :=
  let r := apply_helper op O U initial
  have ⟨inv, ps⟩ := apply_helper_correct op O U initial inv_initial rfl
  ⟨ r.1.size,
    ⟨⟨cook_heap r.1.heap inv.1,
    r.2.cook (inv.2 _ r.2 ps.1).2.2.2.1⟩,
    (inv.2 _ r.2 ps.1).2.2.2.2.1⟩,
  ⟩

public lemma oapply_correct {n m n' m'} (op : Bool → Bool → Bool) (O : OBdd n m) (U : OBdd n' m') :
    ∀ I, (oapply op O U).2.evaluate I = op
      (O.evaluate (Vector.cast (by simp) (I.take n)))
      (U.evaluate (Vector.cast (by simp) (I.take n'))) := by
  let r := apply_helper op O U initial
  have ⟨h1, h2, h3⟩ := apply_helper_correct op O U initial inv_initial rfl
  rw [oapply]
  split
  exact (h1.2 _ r.2 h2).2.2.2.2.2

end Apply
