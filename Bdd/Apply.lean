import Bdd.Basic
import Bdd.Reduce
import Std.Data.HashMap.Lemmas

namespace Apply
inductive RawPointer where
  | terminal : Bool → RawPointer
  | node     : Nat  → RawPointer

structure RawNode (n) where
  var  : Fin n
  low  : RawPointer
  high : RawPointer

abbrev p2t : Nat → Nat → Nat := fun l r ↦ (l + 2) * (r + 2)

structure State (n) (m) (m') where
  cache : Std.HashMap (Pointer m × Pointer m') (Pointer (p2t m m'))
  heap : Vector (Node n (p2t m m')) (p2t m m')
  next : Fin (p2t m m')

def GoodState (op : Bool → Bool → Bool) (Ov : Vector (Node n m) m) (Uv : Vector (Node n m') m') : State n m m' → Prop := fun s ↦
  ∀ key (hk : key ∈ s.cache),
  ∃ (o : Bdd.Ordered ⟨s.heap, s.cache[key]'hk⟩) (o1 : Bdd.Ordered ⟨Ov, key.1⟩) (o2 : Bdd.Ordered ⟨Uv, key.2⟩),
  ∀ I,
  (op (OBdd.evaluate ⟨⟨Ov, key.1⟩, o1⟩ I) (OBdd.evaluate ⟨⟨Uv, key.2⟩, o2⟩ I)) = OBdd.evaluate ⟨⟨s.heap, s.cache[key]'hk⟩, o⟩ I

-- def threeval (op : (Bool → Bool → Bool)) : Pointer m → Pointer m' → (Option Bool)
--   | .terminal b => fun
--     | .terminal b' => op b b'
--     | .node _ => if (op b false) = (op b true) then some (op b false) else none
--   | .node _ => fun
--     | .terminal b' => if (op false b') = (op true b') then some (op false b') else none
--     | .node _ => none

-- def apply_helper (nid : Fin (m * m')) (heap : Vector (Node n (m * m')) (m * m')) (cache : Std.HashMap (Pointer m × Pointer m') (Pointer (m * m'))) (op : (Bool → Bool → Bool)) (O : OBdd n m) (U : OBdd n' m') :
--     Bdd n (m * m') :=
--   match cache.get? ⟨O.1.root, U.1.root⟩ with
--   | some root => ⟨heap, root⟩
--   | none =>
--     if (threeval op O.1.root U.1.root) = none
--     then
--       sorry
--     else sorry

-- def apply_helper {n m m' : Nat} (op : (Bool → Bool → Bool)) (O : OBdd n m.succ) (U : OBdd n' m'.succ) :
--     StateM (State n m.succ m'.succ) (Pointer (m.succ * m'.succ)) := do
--   let s ← get
--   match s.cache.get? ⟨O.1.root, U.1.root⟩ with
--   | some root => pure root
--   | none =>
--     match threeval op O.1.root U.1.root with
--     | some b =>
--       set (⟨s.cache.insert ⟨O.1.root, U.1.root⟩ (.terminal b), s.heap, s.next⟩ : State n m.succ m'.succ)
--       pure (.terminal b)
--     | none =>
--       if O.var ≤ U.var
--       then
--         if O.var ≥ U.var
--         then
-- --        set (⟨s.cache.insert ⟨O.1.root, U.1.root⟩ (.node s.next), s.heap.set s.next sorry, s.next + 1⟩ : State n m.succ m'.succ)
--           pure (.node s.next)
--         else sorry
--       else sorry

def cache_get {n m m' : Nat} (O_root : Pointer m) (U_root : Pointer m') :
    StateM (State n m m') (Option (Pointer (p2t m m'))) := fun s ↦
  ⟨(s.cache.get? ⟨O_root, U_root⟩), s⟩

lemma mem_cache_of_cache_get_eq_some : (cache_get l r s).1.isSome → ⟨l, r⟩ ∈ s.cache := by
  simp only [cache_get]
  intro h
  simp_all only [Std.HashMap.get?_eq_getElem?, isSome_getElem?]

lemma cache_get_preserves_state : (cache_get l r s).2 = s := by
  simp only [cache_get]

def cache_put {n m m' : Nat} (O_root : Pointer m) (U_root : Pointer m') (val : Pointer (p2t m m')) :
    StateM (State n m m') Unit := fun s ↦
  ⟨(), ⟨s.cache.insert ⟨O_root, U_root⟩ val, s.heap, s.next⟩⟩

-- TODO: also call cache_put in heap_push
-- def heap_push {n m m' : Nat} (N : Node n (p2t m m')) :
--     StateM (State n m m') Unit := fun s ↦
--   ⟨(), ⟨s.cache, s.heap.set s.next N, s.next + 1⟩⟩

def heap_push {n m m' : Nat} (O_root : Pointer m) (U_root : Pointer m') (N : Node n (p2t m m')) :
    StateM (State n m m') (Pointer (p2t m m')) := fun s ↦
  ⟨.node s.next, ⟨s.cache.insert ⟨O_root, U_root⟩ (.node s.next), s.heap.set s.next N, s.next + 1⟩⟩

def next : StateM (State n m m') (Fin (p2t m m')) := fun s ↦ ⟨s.next, s⟩

def apply_helper {n m m' : Nat} (op : (Bool → Bool → Bool)) (O : OBdd n m) (U : OBdd n m') :
    StateM (State n m m') (Pointer (p2t m m')) := do
  let cache_hit ← cache_get O.1.root U.1.root
  match cache_hit with
  | some root => pure root
  | none =>
    match O_root_def : O.1.root with
    | .terminal b =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        let b'' := op b b'
        cache_put O.1.root U.1.root (.terminal b'')
        pure (.terminal b'')
      | .node j' =>
        let l ← apply_helper op O (U.low  U_root_def)
        let h ← apply_helper op O (U.high U_root_def)
        heap_push O.1.root U.1.root ⟨U.1.heap[j'].var, l, h⟩
    | .node j =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        let l ← apply_helper op (O.low  O_root_def) U
        let h ← apply_helper op (O.high O_root_def) U
        heap_push O.1.root U.1.root ⟨O.1.heap[j].var, l, h⟩
      | .node j' =>
        if O.1.heap[j].var < U.1.heap[j'].var
        then
          let l ← apply_helper op (O.low  O_root_def) U
          let h ← apply_helper op (O.high O_root_def) U
          heap_push O.1.root U.1.root ⟨O.1.heap[j].var, l, h⟩
        else
          if O.1.heap[j].var > U.1.heap[j'].var
          then
            let l ← apply_helper op O (U.low  U_root_def)
            let h ← apply_helper op O (U.high U_root_def)
            heap_push O.1.root U.1.root ⟨U.1.heap[j'].var, l, h⟩
          else
            let l ← apply_helper op (O.low  O_root_def) (U.low  U_root_def)
            let h ← apply_helper op (O.high O_root_def) (U.high U_root_def)
            heap_push O.1.root U.1.root ⟨U.1.heap[j'].var, l, h⟩
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
  · left;  exact oedge_of_low
  · left;  exact oedge_of_high

def apply {n m m' : Nat} : (Bool → Bool → Bool) → OBdd n.succ m → OBdd n.succ m' → Bdd n.succ (p2t m m') := fun op O U ↦
  let ⟨root, state⟩ := apply_helper op O U ⟨Std.HashMap.emptyWithCapacity, Vector.replicate _ ⟨0, .terminal false, .terminal false⟩, 0⟩
  ⟨state.heap, root⟩

def apply' {n n' m m' p : Nat} : max n n' = p.succ → (Bool → Bool → Bool) → OBdd n m → OBdd n' m' → OBdd (max n n') (p2t m m') := fun h op O U ↦
  ⟨h ▸ apply op (h ▸ O.lift (n' := max n n') (Nat.le_max_left ..)) (h ▸ U.lift (n' := max n n') (Nat.le_max_right ..)), sorry⟩


-- theorem apply_helper_spec' {n m m' : Nat} {op : (Bool → Bool → Bool)} {O : OBdd n m} {U : OBdd n m'} {s : State n m m'} :
--     GoodState op O.1.heap U.1.heap s →
--     let ⟨root, s'⟩ := apply_helper op O U s
--     ∃ (o : Bdd.Ordered ⟨s'.heap, root⟩), ∀ I, (op (O.evaluate I) (U.evaluate I)) = OBdd.evaluate ⟨⟨s'.heap, root⟩, o⟩ I := by
--   intro sg
--   split
--   next final_root final_state h =>
--     unfold apply_helper at h
--     simp only [bind, StateT.bind] at h
--     split at h
--     next hit s' heq =>
--       cases hit with
--       | some val =>
--         simp only [pure, StateT.pure] at h
--         rw [Prod.mk.injEq] at h
--         have := sg ⟨O.1.root, U.1.root⟩ (mem_cache_of_cache_get_eq_some (Option.isSome_iff_exists.mpr ⟨val, (by rw [heq])⟩))
--         simp only at this
--         rw [show { heap := O.1.heap, root := O.1.root } = O.1 by rfl] at this
--         sorry
--       | none =>
--         sorry

theorem apply_helper_spec {n m m' : Nat} {op : (Bool → Bool → Bool)} {O : OBdd n m} {U : OBdd n m'} {initial_state : State n m m'} :
    GoodState op O.1.heap U.1.heap initial_state →
    let ⟨root, s'⟩ := apply_helper op O U initial_state
    GoodState op O.1.heap U.1.heap s' ∧
    ∃ (o : Bdd.Ordered ⟨s'.heap, root⟩), ∀ I, (op (O.evaluate I) (U.evaluate I)) = OBdd.evaluate ⟨⟨s'.heap, root⟩, o⟩ I := by
  intro sg
  split
  next final_root final_state h =>
    unfold apply_helper at h
    split at h
    next b heq =>
      split at h
      next b' heqq =>
        simp only [bind, StateT.bind] at h
        split at h
        next a s'' heqqq =>
          split at h
          next root =>
            -- cache hit!
            simp only [pure, StateT.pure] at h
            rw [Prod.mk.injEq] at h
            have := (mem_cache_of_cache_get_eq_some (Option.isSome_iff_exists.mpr ⟨root, (by rw [heqqq])⟩))
            rcases (sg ⟨O.1.root, U.1.root⟩ this) with ⟨h1, h2, h3, h4⟩
            have that : initial_state.cache[(O.1.root, U.1.root)]'this = root := by
              simp [cache_get] at heqqq
              rw [Prod.mk.injEq] at heqqq
              rw [Std.HashMap.getElem?_eq_some_getElem (h' := this)] at heqqq
              rcases heqqq with ⟨hh1, hh2⟩
              injection hh1 with hhh1
            rw [that] at h1
            rw [← h.1, ← h.2]
            have : s'' = (cache_get O.1.root U.1.root initial_state).2 := by rw [heqqq]
            rw [cache_get_preserves_state] at this
            rw [this]
            constructor
            · assumption
            · use h1
              intro I
              have := h4 I
              convert this
              exact symm that
          next =>
            -- cache miss...
            simp only [StateT.bind, cache_put, Bdd.Ordered.eq_1, pure, StateT.pure, Id.bind_eq] at h
            rw [Prod.mk.injEq] at h
            rw [← h.1, ← h.2]
            simp only
            have : s'' = (cache_get O.1.root U.1.root initial_state).2 := by rw [heqqq]
            rw [cache_get_preserves_state] at this
            rw [this]
            rw [this] at h heqqq
            constructor
            · simp only [GoodState]
              intro key hk
              rw [Std.HashMap.getElem_insert]
              split
              next hh =>
                simp at hh
                use Bdd.Ordered_of_terminal
                simp_rw [← hh]
                use O.2
                use U.2
                have : ⟨{ heap := O.1.heap, root := O.1.root }, O.2⟩ = O := rfl
                simp_rw [this]
                have : ⟨{ heap := U.1.heap, root := U.1.root }, U.2⟩ = U := rfl
                simp_rw [this]
                intro I
                rw [OBdd.evaluate_terminal' heq, OBdd.evaluate_terminal' heqq]
                simp
              next hh =>
                have : key ∈ initial_state.cache := by
                  apply Std.HashMap.mem_of_mem_insert hk
                  simp_all only [beq_eq_false_iff_ne]
                exact sg key this
            · use Bdd.Ordered_of_terminal
              intro I
              rw [OBdd.evaluate_terminal' heq, OBdd.evaluate_terminal' heqq]
              simp
      next j' heqq =>
        simp only [bind, StateT.bind] at h
        split at h
        next a s heqqq =>
          split at h
          next root => sorry --cache hit
          next =>
            simp only [StateT.bind, Id.bind_eq, pure, StateT.pure] at h
--            generalize hh : (apply_helper op O (U.low heqq) s) = sss at h
            rcases hh : (apply_helper op O (U.low heqq) s) with ⟨ll, s'⟩
            rcases hhh : (apply_helper op O (U.high heqq) s') with ⟨hl, s''⟩
            rw [hh, hhh] at h
            simp only [next] at h
            have : s = (cache_get O.1.root U.1.root initial_state).2 := by rw [heqqq]
            rw [cache_get_preserves_state] at this
            rw [this] at hh
            have : GoodState op O.1.heap U.1.heap (apply_helper op O (U.low heqq) initial_state).2 := (apply_helper_spec (by rw [OBdd.low_heap_eq_heap]; assumption)).1
            rw [show (apply_helper op O (U.low heqq) initial_state).2 = s' by rw [hh]] at this
            have : GoodState op O.1.heap U.1.heap (apply_helper op O (U.high heqq) s').2 := (apply_helper_spec (by rw [OBdd.high_heap_eq_heap]; assumption)).1
            rw [show (apply_helper op O (U.high heqq) s').2 = s'' by rw [hhh]] at this
            constructor
            · rw [← show (heap_push O.1.root U.1.root { var := U.1.heap[j'].var, low := ll, high := hl } s'').2 = final_state by rw [h]]
              intro key
              simp only [heap_push]
              intro hk

              simp only [GoodState, Bdd.Ordered.eq_1, Bdd.Ordered, Prod.forall]
              sorry
            · sorry
    next j heq =>
      split at h
      next => sorry
      next =>
        split at h
        sorry
        sorry
termination_by (O, U)
decreasing_by
  · right; exact oedge_of_low
  · right; exact oedge_of_high


theorem apply_spec {n m m' : Nat} {op : (Bool → Bool → Bool)} {O : OBdd n.succ m} {U : OBdd n.succ m'} :
    ∃ (o : Bdd.Ordered (apply op O U)), ∀ I, (op (O.evaluate I) (U.evaluate I)) = OBdd.evaluate ⟨apply op O U, o⟩ I :=
  (apply_helper_spec (by sorry)).2

theorem apply'_spec {n n' m m' p : Nat} {h : max n n' = p.succ} {op : Bool → Bool → Bool} {O : OBdd n m} {U : OBdd n' m'} :
    ∀ I : Vector Bool (n ⊔ n'), (op ((O.lift (by simp)).evaluate I) ((U.lift (by simp)).evaluate I)) = OBdd.evaluate (apply' h op O U) I := by
  sorry

end Apply
