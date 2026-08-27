module

public import Bdd.Basic
import Std.Data.HashMap.Lemmas

namespace Restrict

open RawBdd

structure State (n) (m) where
  size : Nat
  heap : Vector (RawNode n) size
  cache : Std.HashMap (Pointer m) RawPointer

def initial {n m} : State n m := ⟨_, (Vector.emptyWithCapacity 0), Std.HashMap.emptyWithCapacity 0⟩

def Invariant {n m} (b : Bool) (i : Fin n) (heap : Vector (Node n m) m) (s : State n m) :=
  ∃ hh : (∀ i : Fin s.size, RawNode.Bounded i s.heap[i]),
    ∀ (k : (Pointer m)) (p : RawPointer),
      s.cache[k]? = some p →
      (∀ j h, p = .inr j → (if (Pointer.toVar heap k).1 = i.1 then (s.heap[j]'h).va.1 > (Pointer.toVar heap k) else (s.heap[j]'h).va.1 = (Pointer.toVar heap k))) ∧
      ∃ hk1 : Bdd.Ordered ⟨heap, k⟩,
          ∃ hp : p.Bounded s.size,
            ∃ o : Bdd.Ordered ⟨cook_heap s.heap hh, p.cook hp⟩,
                OBdd.evaluate ⟨⟨cook_heap s.heap hh, p.cook hp⟩, o⟩ = Nary.restrict (OBdd.evaluate ⟨⟨heap, k⟩, hk1⟩) b i

lemma inv_initial {n m b i} {O : OBdd n m} : Invariant b i O.bdd.heap initial := by
  constructor
  · intro k p hp
    simp only [initial, Std.HashMap.getElem?_emptyWithCapacity, reduceCtorEq] at hp
  · rintro ⟨_, c⟩
    simp only [initial, Nat.not_lt_zero] at c

lemma getElem_last_cookHeap_push {n m} {heap : Vector (RawNode n) m} {N : RawNode n} {h0 h1} :
    (cook_heap (heap.push N) h0)[m] = N.cook h1 := by
  simp only [cook_heap_eq, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]

lemma heap_push_aux {n m b i} {O : OBdd n m} {N} (s : State n m) (inv : Invariant b i O.bdd.heap s)
    (hNl : ∃ k : Pointer m, s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m, s.cache[k]? = some N.hi)
    (hNv : (if (O.1.root.toVar O.1.heap).1 = i.1 then N.va.1 > (O.1.root.toVar O.1.heap).1 else N.va.1 = (O.1.root.toVar O.1.heap).1))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _),
      OBdd.evaluate ⟨⟨cook_heap (s.heap.push N) h0, .node ⟨s.size, by simp⟩⟩, h1⟩ = Nary.restrict O.evaluate b i) :
    Invariant b i O.bdd.heap
      { size := s.size + 1, heap := s.heap.push N, cache := s.cache.insert (O.1.root) (Sum.inr s.size) } := by
  rcases hNl with ⟨kl, hkl⟩
  rcases hNh with ⟨kh, hkh⟩
  have hN : RawNode.Bounded s.size N := by
    constructor
    · exact (inv.2 kl N.lo hkl).2.2.1
    · exact (inv.2 kh N.hi hkh).2.2.1
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
  intro k p
  simp only
  intro hp
  rw [Std.HashMap.getElem?_insert] at hp
  simp only [beq_iff_eq] at hp
  split at hp
  next heq =>
    subst heq
    constructor
    · intro j hs hj
      rw [Vector.getElem_push]
      split
      next heqq =>
        injection hp with hpp
        rw [hj] at hpp
        injection hpp with hppp
        split
        next contra => rw [hppp] at contra; absurd contra; simp only [lt_self_iff_false,
          not_false_eq_true]
        next =>
          split at hNv
          next contra => simp_all
          next contra => contradiction
      next heqq =>
        split
        next contra => injection hp with hi; subst hi; injection hj with hi; rw [hi] at contra; absurd contra; simp only [lt_self_iff_false,
          not_false_eq_true]
        next =>
          split at hNv
          next => simp_all
          next contra => rw [← hNv]
    use O.2
    injection hp with hpe
    subst hpe
    have hb : RawPointer.Bounded (s.size + 1) (Sum.inr s.size) := by
      simp only [RawPointer.bounded_inr_iff, Nat.lt_add_one]
    use hb
    have hoo : Bdd.Ordered ⟨cook_heap (s.heap.push N) this, RawPointer.cook (Sum.inr s.size) hb⟩ := by
      obtain ⟨_, _, hb_lo, ho_lo, _⟩ := inv.2 kl N.lo hkl
      obtain ⟨_, _, hb_hi, ho_hi, _⟩ := inv.2 kh N.hi hkh
      rw [RawPointer.cook_inr]
      apply Bdd.ordered_of_low_high_ordered rfl
      · simp only [Bdd.low_eq, Fin.getElem_fin]
        rw [getElem_last_cookHeap_push (h1 := RawNode.bounded_of_le hN (by omega))]
        rw [cook_low]
        exact push_ordered ho_lo
      · simp [Bdd.var_eq, cook_heap_eq, Bdd.low_eq]
        cases heq : N.lo with
        | inl val =>
          simp_rw [cook_low, heq]
          simp only [RawPointer.cook_inl, Pointer.toVar_terminal, Nat.succ_eq_add_one]
          simp only [Fin.lt_def, Nat.succ_eq_add_one, Pointer.toVar_node,
            Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq, Fin.is_lt]
        | inr val =>
          rw [heq, RawPointer.bounded_inr_iff] at hb_lo
          simp_rw [cook_low, heq]
          simp only [RawNode.cook_eq, RawPointer.cook_inr]
          simp only [Fin.lt_def, Nat.succ_eq_add_one, Pointer.toVar_node, Fin.getElem_fin,
            Vector.getElem_ofFn, Vector.getElem_push_eq]
          rw [Vector.getElem_push_lt hb_lo]
          exact hxl _ hb_lo heq
      · simp only [Bdd.high_eq, Fin.getElem_fin]
        rw [getElem_last_cookHeap_push (h1 := RawNode.bounded_of_le hN (by omega))]
        rw [cook_high]
        exact push_ordered ho_hi
      · simp [Nat.succ_eq_add_one, Bdd.var_eq, cook_heap_eq, Bdd.high_eq]
        cases heq : N.hi with
        | inl val =>
          rw [cook_high]
          simp_rw [heq]
          simp only [RawPointer.cook_inl, Pointer.toVar_terminal, Nat.succ_eq_add_one]
          simp only [Fin.lt_def, Nat.succ_eq_add_one, Pointer.toVar_node, Fin.getElem_fin,
            Vector.getElem_ofFn, Vector.getElem_push_eq, Fin.is_lt]
        | inr val =>
          rw [heq, RawPointer.bounded_inr_iff] at hb_hi
          simp_rw [cook_high, heq]
          simp only [RawNode.cook_eq, RawPointer.cook_inr]
          simp only [Fin.lt_def, Nat.succ_eq_add_one, Pointer.toVar_node, Fin.getElem_fin,
            Vector.getElem_ofFn, Vector.getElem_push_eq]
          rw [Vector.getElem_push_lt]
          exact hxh _ hb_hi heq
    use hoo
    simp only [RawPointer.cook_inr, OBdd.mk_eq_self]
    simp [RawPointer.cook_inr] at hoo
    have := hh _ (by exact hoo)
    exact hh _ hoo
  next heq =>
    obtain ⟨inv1, hok, hbp, hop, heval⟩ := inv.2 k p hp
    have hbp' : RawPointer.Bounded (s.size + 1) p :=
        RawPointer.bounded_of_le hbp (by omega)
    constructor
    · intro j hs hj
      rw [hj] at hp
      rw [hj, RawPointer.bounded_inr_iff] at hbp
      rw [Vector.getElem_push_lt hbp]
      exact inv1 j hbp hj
    use hok, hbp', push_ordered hop
    ext I
    calc _
      _ = OBdd.evaluate ⟨{ heap := cook_heap (s.heap) inv.1, root := p.cook hbp }, hop⟩ I := by
        rw [OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq]
        · simp only [Fin.getElem_fin]
          intro j hj
          use (by omega)
          simp [cook_heap_eq]
          exact RawNode.cook_equiv
        · simp only [RawPointer.cook_equiv]
    rw [heval]

def heap_push {n m} (O : OBdd n m) (N : RawNode n) (s : (State n m)) : State n m × RawPointer :=
  ⟨⟨s.size + 1, s.heap.push N, s.cache.insert O.1.root (.inr s.size)⟩, .inr s.size⟩

lemma heap_push_correct {n m O b i} {N : RawNode n} {s s' : State n m} {p'}
    (h : heap_push O N s = (s', p'))
    (inv : Invariant b i O.bdd.heap s)
    (hNl : ∃ k : Pointer m, s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m, s.cache[k]? = some N.hi)
    (hNv : (if (O.1.root.toVar O.1.heap).1 = i.1 then N.va.1 > (O.1.root.toVar O.1.heap).1 else N.va.1 = (O.1.root.toVar O.1.heap).1))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _),
      OBdd.evaluate ⟨⟨cook_heap (s.heap.push N) h0, .node ⟨s.size, by simp⟩⟩, h1⟩ = Nary.restrict (O.evaluate) b i)
    (hc : s.cache[O.1.root]? = none) :
      (Invariant b i O.bdd.heap s') ∧
      (s'.cache[O.1.root]? = some p') ∧
      s.size ≤ s'.size ∧
      (∀ (k : Pointer m),
        (∀ p, s.cache[k]? = some p → s'.cache[k]? = some p) ∧
        (s'.cache[k]? = none → s.cache[k]? = none) ∧
        (s.cache[k]? = none → (∃ p, s'.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k)) := by
    rcases h with ⟨rfl, rfl⟩
    split_ands
    · exact heap_push_aux s inv hNl hNh hNv hxl hxh hh
    · simp only [Std.HashMap.getElem?_insert_self]
    · simp only [Nat.le_add_right]
    · intro k
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
          simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hq
          split at hq
          next heqq => subst heqq; exact Pointer.Reachable.refl
          next heqq => rw [hk] at hq; contradiction

lemma insert_terminal_invariant {n m b i} {O : OBdd n m} {b'} (s0 : State n m) (inv : Invariant b i O.bdd.heap s0) (ho : O.1.root = .terminal b') :
    Invariant b i O.bdd.heap { size := s0.size, heap := s0.heap, cache := s0.cache.insert O.1.root (Sum.inl b') } := by
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
    use O.2
    injection hp with hpe
    subst hpe
    use RawPointer.bounded_inl
    simp [RawPointer.cook_inl, ho, Bdd.ordered_of_terminal, OBdd.evaluate_terminal]
  next =>
    constructor
    · exact (inv.2 _ _ hp).1
    exact (inv.2 _ _ hp).2

def restrict_helper {n m} (O : OBdd n m) (b : Bool) (i : Fin n) (s0 : State n m) :
  State n m × RawPointer :=
  match hc : s0.cache[O.1.root]? with
  | some root => ⟨s0, root⟩
  | none =>
    match O_root_def : O.1.root with
    | .terminal b' =>
      ⟨⟨s0.size, s0.heap, s0.cache.insert O.1.root (.inl b')⟩, .inl b'⟩
    | .node j =>
      if hlt : O.1.heap[j].var = i
      then
        if hb : b
        then
          let ⟨sl, rl⟩ := restrict_helper (O.high O_root_def) b i s0
          ⟨⟨sl.size, sl.heap, sl.cache.insert O.1.root rl⟩, rl⟩
        else
          let ⟨sl, rl⟩ := restrict_helper (O.low O_root_def) b i s0
          ⟨⟨sl.size, sl.heap, sl.cache.insert O.1.root rl⟩, rl⟩
      else
        let ⟨sl, rl⟩ := restrict_helper (O.low O_root_def) b i s0
        let ⟨sh, rh⟩ := restrict_helper (O.high O_root_def) b i sl
        heap_push O ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh
termination_by O

lemma restrict_helper_correct {n m} (O : OBdd n m) (b : Bool) (i : Fin n) (s0 : State n m)
    {s' p'} (h : restrict_helper O b i s0 = (s', p')) (inv : Invariant b i O.bdd.heap s0) :
      (Invariant b i O.bdd.heap s') ∧
      (s'.cache[O.1.root]? = some p') ∧
      (s0.size ≤ s'.size) ∧
      (∀ (k : Pointer m),
        (∀ p, s0.cache[k]? = some p → s'.cache[k]? = some p) ∧
        (s'.cache[k]? = none → s0.cache[k]? = none) ∧
        (s0.cache[k]? = none → (∃ p, s'.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k))
    := by
  fun_induction restrict_helper generalizing s' p' with
  | case1 O s0 root hc =>
    rcases h with ⟨rfl, rfl⟩
    exact ⟨inv, hc, .refl, by grind only⟩
  | case2 O s0 hc b' O_root_def =>
    rcases h with ⟨rfl, rfl⟩
    simp only
    split_ands
    · exact insert_terminal_invariant s0 inv O_root_def
    · simp only [O_root_def, Std.HashMap.getElem?_insert_self]
    · exact .refl
    · intro k
      constructor
      · intro p hp
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
            simp only [O_root_def]
            exact Pointer.Reachable.refl
          next heq => grind only
  | case3 O s0 hc j O_root_def hlt hb sl rl heq ih =>
    rcases h with ⟨rfl, rfl⟩
    let ⟨invl, hl, hsl, hlp⟩ := ih rfl (OBdd.high_heap_eq_heap O_root_def ▸ inv)
    simp_all only
    split_ands
    · subst hlt
      constructor
      · intro k p
        simp only
        intro hkp
        simp only [Std.HashMap.getElem?_insert,beq_iff_eq] at hkp
        split at hkp
        next heq =>
          injection hkp with hinj
          subst hinj heq
          constructor
          · intro j' hj1 rfl
            have that : O.1.heap[j].var.1 < (Pointer.toVar O.1.heap O.bdd.heap[j].high).1 := by
              have := OBdd.var_lt_high_var (O := O) (h := O_root_def)
              simp only [OBdd.var_node O_root_def, OBdd.var_eq, OBdd.high_heap_eq_heap,
                OBdd.high_root_eq_high] at this
              exact this
            have := (invl.2 (O.high O_root_def).bdd.root (.inr j') hl).1 j' hj1 rfl
            split at this
            next hsp =>
              rw [← hsp] at that
              absurd that
              simp only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high, lt_self_iff_false,
                not_false_eq_true]
            next hsp =>
              simp_all only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high, Pointer.toVar_node,
                ↓reduceIte]
          · use O_root_def ▸ O.2
            have := (invl.2 _ _ hl).2.2
            use this.1
            use this.2.1
            rw [this.2.2]
            simp only [← O_root_def, OBdd.mk_eq_self]
            rw [OBdd.evaluate_node' O_root_def]
            rw [Nary.restrict_if]
            simp only [Fin.getElem_fin]
            ext I
            conv =>
              rhs
              congr
              simp only [Nary.restrict, Vector.getElem_set_self]
            rfl
        next heq =>
          simp only [OBdd.high_heap_eq_heap] at invl
          exact (invl.2 _ _ hkp)
    · simp only [Std.HashMap.getElem?_insert_self]
    · trivial
    · intro k
      constructor
      · intro p hkp
        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
        split
        next heq =>
          subst heq
          rw [hkp] at hc
          contradiction
        next => exact (hlp k).1 p hkp
      · constructor
        · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
          split
          next heq =>
            subst heq
            simp only [reduceCtorEq, getElem?_eq_none_iff, IsEmpty.forall_iff]
          next => exact (hlp k).2.1
        · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
          split
          next heq =>
            subst heq
            rw [hc]
            simp only [Option.some.injEq, exists_eq', forall_const]
            exact Pointer.Reachable.refl
          next =>
            intro hkn hhh
            rw [← O_root_def]
            trans O.bdd.heap[j].high
            · exact O.bdd.reachable_high O_root_def
            · simp only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high] at hlp
              exact (hlp k).2.2 hkn hhh
  | case4 O s0 hc j O_root_def hlt hb sl rl heq ih =>
    rcases h with ⟨rfl, rfl⟩
    let ⟨invl, hl, hsl, hlp⟩ := ih rfl (OBdd.low_heap_eq_heap O_root_def ▸ inv)
    simp_all only
    split_ands
    · subst hlt
      constructor
      · intro k p
        simp only
        intro hkp
        simp only [Std.HashMap.getElem?_insert,beq_iff_eq] at hkp
        split at hkp
        next heq =>
          subst heq
          injection hkp with hinj
          subst hinj
          constructor
          · intro j' hj1 hrj
            subst hrj
            have that : O.1.heap[j].var.1 < (Pointer.toVar O.1.heap (O.low O_root_def).1.root).1 := by
              have := OBdd.var_lt_low_var (O := O) (h := O_root_def)
              simp only [OBdd.var_eq, OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at this
              rw [O_root_def, Pointer.toVar_node] at this
              simp only [OBdd.low_root_eq_low]
              exact this
            have := (invl.2 _ _ hl).1 _ hj1 rfl
            split at this
            next hsp =>
              rw [← hsp] at that
              absurd that
              simp only [Nat.succ_eq_add_one, OBdd.low_heap_eq_heap, lt_self_iff_false,
                not_false_eq_true]
            next hsp =>
              simp_all only [getElem?_eq_none_iff,
                Fin.getElem_fin, OBdd.low_heap_eq_heap, forall_exists_index,
                Nat.succ_eq_add_one, Pointer.toVar_node, gt_iff_lt, ite_true]
          · use O_root_def ▸ O.2
            have := (invl.2 _ _ hl).2.2
            use this.1
            use this.2.1
            rw [this.2.2]
            simp only [← O_root_def, OBdd.mk_eq_self]
            have that := OBdd.evaluate_node' O_root_def
            rw [that]
            rw [Nary.restrict_if]
            simp only [Fin.getElem_fin]
            ext I
            conv =>
              rhs
              congr
              simp only [Nary.restrict, Vector.getElem_set_self]
            rfl
        next heq =>
          simp only [OBdd.low_heap_eq_heap] at invl
          exact (invl.2 _ _ hkp)
    · simp only [Std.HashMap.getElem?_insert_self]
    · trivial
    · intro k
      constructor
      · intro p hkp
        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
        split
        next heq =>
          subst heq
          rw [hkp] at hc
          contradiction
        next => exact (hlp k).1 p hkp
      · constructor
        · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
          split
          next heq =>
            subst heq
            simp only [reduceCtorEq, getElem?_eq_none_iff, IsEmpty.forall_iff]
          next => exact (hlp k).2.1
        · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
          split
          next heq =>
            subst heq
            rw [hc]
            simp only [Option.some.injEq, exists_eq', forall_const]
            exact Pointer.Reachable.refl
          next =>
            intro hkn hhh
            rw [← O_root_def]
            trans O.bdd.heap[j].low
            · exact O.bdd.reachable_low O_root_def
            · have := (hlp k).2.2 hkn hhh
              simp_all only [OBdd.low_root_eq_low, OBdd.low_heap_eq_heap]
  | case5 O s0 hc j O_root_def hlt sl rl heql sh rh heqh ihl ihh =>
    rcases h with ⟨rfl, rfl⟩
    simp_all only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, forall_const,
      OBdd.high_heap_eq_heap, OBdd.high_root_eq_high]
    let ⟨invl, hl, hsl, hlp⟩ := ihl rfl
    let ⟨invh, hh, hsh, hhp⟩ := ihh rfl invl
    let r := heap_push O ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh
    let N : RawNode n :=  ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩
    obtain ⟨invv, hv, hsv, hvp⟩ := heap_push_correct (O := O) (N := N) rfl invh
        (by
          use O.bdd.heap[j].low
          exact (hhp _).1 _ hl
        )
        ⟨_, hh⟩
        (by
          simp only [N]
          simp only [Nat.succ_eq_add_one, O_root_def, Pointer.toVar_node,
            gt_iff_lt, lt_self_iff_false, if_false_left, and_true, Fin.val_inj]
          exact hlt
        )
        (by
          intro j' hj1 hj2
          have h1 := (hhp _).1 _ hl
          simp only [N] at hj2
          rw [hj2] at h1
          have h2 := (invh.2 _ (.inr j') h1).1 _ hj1 rfl
          have hll : O.1.heap[j.1].var.1 < (Pointer.toVar O.1.heap O.bdd.heap[j].low).1 := by
            have h3 := OBdd.var_lt_low_var (O := O) (h := O_root_def)
            simp only [OBdd.var_eq,Fin.val_fin_lt] at h3
            rw [O_root_def, OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at h3
            simp_rw [Fin.lt_def, Pointer.toVar_node] at h3
            grind only [= Fin.getElem_fin]
          split at h2
          next =>
            trans (Pointer.toVar O.1.heap O.bdd.heap[j].low).1
            · exact hll
            · exact h2
          next =>
            rw [h2]
            exact hll
        )
        (by
          intro j' hj1 hj2
          have that := (invh.2 _ _ hh).1 _ hj1 hj2
          have hll : O.1.heap[j.1].var.1 < (Pointer.toVar O.1.heap O.bdd.heap[j].high).1 := by
            have := OBdd.var_lt_high_var (O := O) (h := O_root_def)
            simp only [OBdd.var_node O_root_def, OBdd.var_eq, OBdd.high_heap_eq_heap] at this
            rw [OBdd.high_root_eq_high] at this
            grind only [= Fin.getElem_fin]
          split at that
          next =>
            trans (Pointer.toVar O.1.heap O.bdd.heap[j].high).1
            · exact hll
            · exact that
          next =>
            rw [that]
            exact hll
        )
        (by
          intro h0 h1
          rw [OBdd.evaluate_node' O_root_def, OBdd.evaluate_node' rfl]
          rw [Nary.restrict_if]
          simp only [Fin.getElem_fin]
          ext I
          congr 1
          · simp only [Nary.restrict, cook_heap_eq, RawNode.cook_eq, Fin.getElem_fin,
              Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff, Bool.coe_iff_coe]
            rw [Vector.getElem_set_ne]
            · rfl
            · grind only [= Fin.getElem_fin]
          · have h := invh.2 O.bdd.heap[j].high rh hh
            rcases h with ⟨h1, h2, h3, h4, h5⟩
            simp only [OBdd.high_eq, Bdd.high_eq]
            rw [push_evaluate rfl (v := sh.heap) (h0 := h0) (ho := h4), h5]
            simp [cook_heap_eq, cook_high]
            rfl
          · have : sh.cache[O.bdd.heap[j].low]? = some rl :=
              (hhp _).1 _ hl
            have ⟨h1, h2, h3, h4, h5⟩ := invh.2 O.bdd.heap[j].low rl this
            rw [push_evaluate (by simp) (h0 := h0) (ho := h4), h5]
            · rw [OBdd.mk_eq_low]
            · simp [cook_heap_eq, cook_low]
              rfl
        )
        (by
          cases heq : sh.cache[O.1.root]? with
          | none => rfl
          | some val =>
            cases heqq : sl.cache[O.1.root]? with
            | none =>
              have := ((hhp _).2.2 heqq ⟨val, heq⟩)
              grind only [ O.not_reachable_high_root]
            | some val =>
              have := ((hlp _).2.2 hc ⟨_, O_root_def ▸ heqq⟩)
              grind only [O.not_reachable_low_root]
        )
    split_ands
    · simp only [Fin.getElem_fin, O_root_def, N] at invv
      exact invv
    · rw [O_root_def] at hv; exact hv
    · exact .trans hsl (.trans hsh hsv)
    · intro k
      simp_all only
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
          rw [← O_root_def]
          cases heq : sh.cache[k]? with
          | none =>
            rw [O_root_def]
            apply (hvp _).2.2 heq hkp
          | some w =>
            cases heqq : sl.cache[k]? with
            | none =>
              have := (hhp _).2.2 heqq ⟨_, heq⟩
              · trans O.bdd.heap[j].high
                · exact O.bdd.reachable_high O_root_def
                · exact this
            | some ww =>
              have := (hlp _).2.2 hk ⟨_, heqq⟩
              · trans O.bdd.heap[j].low
                · exact O.bdd.reachable_low O_root_def
                · exact this

public def orestrict {n m} (b : Bool) (i : Fin n) (O : OBdd n m) : (s : Nat) × OBdd n s :=
  let r := restrict_helper O b i initial
  let ⟨h1, h2, _⟩ := restrict_helper_correct O b i initial rfl inv_initial
  ⟨ r.1.size, ⟨cook_heap r.1.heap h1.1, r.2.cook (h1.2 _ r.2 h2).2.2.1⟩, (h1.2 _ r.2 h2).2.2.2.1⟩

public lemma orestrict_correct {n m b i} {O : OBdd n m} :
    (orestrict b i O).2.evaluate = Nary.restrict O.evaluate b i := by
  let r := restrict_helper O b i initial
  have ⟨h1, h2, h3⟩ := restrict_helper_correct O b i initial rfl inv_initial
  rw [orestrict]
  split
  exact (h1.2 _ r.2 h2).2.2.2.2

end Restrict
