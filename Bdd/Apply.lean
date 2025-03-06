import Bdd.Basic
import Bdd.Reduce
-- import Std.HashMap.Basic

open List renaming Vector → Vec

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
  heap : Vec (Node n (p2t m m')) (p2t m m')
  next : Fin (p2t m m')

-- def threeval (op : (Bool → Bool → Bool)): Pointer m → Pointer m' → (Option Bool)
--   | .terminal b => fun
--     | .terminal b' => op b b'
--     | .node _ => if (op b false) = (op b true) then some (op b false) else none
--   | .node _ => fun
--     | .terminal b' => if (op false b') = (op true b') then some (op false b') else none
--     | .node _ => none

-- def apply_helper (nid : Fin (m * m')) (heap : Vec (Node n (m * m')) (m * m')) (cache : Std.HashMap (Pointer m × Pointer m') (Pointer (m * m'))) (op : (Bool → Bool → Bool)) (O : OBdd n m) (U : OBdd n' m') :
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

def cache_put {n m m' : Nat} (O_root : Pointer m) (U_root : Pointer m') (val : Pointer (p2t m m')) :
    StateM (State n m m') Unit := fun s ↦
  ⟨(), ⟨s.cache.insert ⟨O_root, U_root⟩ val, s.heap, s.next⟩⟩

def heap_push {n m m' : Nat} (N : Node n (p2t m m')) :
    StateM (State n m m') Unit := fun s ↦
  ⟨(), ⟨s.cache, s.heap.set s.next N, s.next + 1⟩⟩

def next : StateM (State n m m') (Fin (p2t m m')) := do
  let s ← get
  pure s.next

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
        let nid ← next
        cache_put O.1.root U.1.root (.node nid)
        heap_push ⟨U.1.heap[j'].var, l, h⟩
        pure (.node nid)
    | .node j =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        let l ← apply_helper op (O.low  O_root_def) U
        let h ← apply_helper op (O.high O_root_def) U
        let nid ← next
        cache_put O.1.root U.1.root (.node nid)
        heap_push ⟨O.1.heap[j].var, l, h⟩
        pure (.node nid)
      | .node j' =>
        if O.1.heap[j].var < U.1.heap[j'].var
        then
          let l ← apply_helper op (O.low  O_root_def) U
          let h ← apply_helper op (O.high O_root_def) U
          let nid ← next
          cache_put O.1.root U.1.root (.node nid)
          heap_push ⟨O.1.heap[j].var, l, h⟩
          pure (.node nid)
        else
          if O.1.heap[j].var > U.1.heap[j'].var
          then
            let l ← apply_helper op O (U.low  U_root_def)
            let h ← apply_helper op O (U.high U_root_def)
            let nid ← next
            cache_put O.1.root U.1.root (.node nid)
            heap_push ⟨U.1.heap[j'].var, l, h⟩
            pure (.node nid)
          else
            let l ← apply_helper op (O.low  O_root_def) (U.low  U_root_def)
            let h ← apply_helper op (O.high O_root_def) (U.high U_root_def)
            let nid ← next
            cache_put O.1.root U.1.root (.node nid)
            heap_push ⟨U.1.heap[j'].var, l, h⟩
            pure (.node nid)
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
  let ⟨root, state⟩ := apply_helper op O U ⟨Std.HashMap.empty, Vec.replicate _ ⟨0, .terminal false, .terminal false⟩, 0⟩
  ⟨state.heap, root⟩

theorem apply_spec {n m m' : Nat} {op : (Bool → Bool → Bool)} {O : OBdd n.succ m} {U : OBdd n.succ m'} : ∃ (o : Bdd.Ordered (apply op O U)), ∀ I, (op (O.evaluate I) (U.evaluate I)) = OBdd.evaluate ⟨apply op O U, o⟩ I := by
  sorry

end Apply

def Bdd.fromVar {n} : Fin n → Bdd n 1 := fun i ↦ ⟨⟨[⟨i, .terminal false, .terminal true⟩], rfl⟩, .node 0⟩

lemma Bdd.fromVar_Ordered {n} {i : Fin n} : Bdd.Ordered (fromVar i) := by
  apply Ordered_of_Proper
  simp only [fromVar, Proper]
  simp only [Vec.instMembership, Function.comp_apply, List.Vector.toList_singleton, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  intro j contra
  cases contra <;> contradiction

def foo := Compactify.compactify' ⟨(Reduce.reduce ⟨(Apply.apply Bool.and ⟨(Bdd.fromVar (n := 2) 0), Bdd.fromVar_Ordered⟩ ⟨(Bdd.fromVar (n := 2) 1), Bdd.fromVar_Ordered⟩), Apply.apply_spec.1⟩), Reduce.reduce_spec.1⟩
def bar := Compactify.compactify' ⟨(Reduce.reduce ⟨(Apply.apply Bool.or ⟨(Bdd.fromVar (n := 3) 0), Bdd.fromVar_Ordered⟩ ⟨(Bdd.fromVar (n := 3) 1), Bdd.fromVar_Ordered⟩), Apply.apply_spec.1⟩), Reduce.reduce_spec.1⟩
def baz := Compactify.compactify' ⟨(Reduce.reduce ⟨(Apply.apply Bool.or (⟨(Apply.apply Bool.and example_bdd example_bdd), Apply.apply_spec.1⟩) example_bdd), sorry⟩), sorry⟩

#eval! baz
#eval! foo
#eval! bar

#eval (Bdd.fromVar (n := 2) 0)
#eval Apply.apply Bool.and ⟨(Bdd.fromVar (n := 2) 0), Bdd.fromVar_Ordered⟩ ⟨(Bdd.fromVar (n := 2) 1), Bdd.fromVar_Ordered⟩
#eval! Reduce.reduce ⟨(Apply.apply Bool.and ⟨(Bdd.fromVar (n := 2) 0), Bdd.fromVar_Ordered⟩ ⟨(Bdd.fromVar (n := 2) 1), Bdd.fromVar_Ordered⟩), Apply.apply_spec.1⟩
#eval! Compactify.compactify' ⟨(Reduce.reduce ⟨(Apply.apply Bool.and ⟨(Bdd.fromVar (n := 2) 0), Bdd.fromVar_Ordered⟩ ⟨(Bdd.fromVar (n := 2) 1), Bdd.fromVar_Ordered⟩), Apply.apply_spec.1⟩), Reduce.reduce_spec.1⟩
#eval! Compactify.compactify' ⟨(Reduce.reduce ⟨(Apply.apply Bool.or ⟨(Bdd.fromVar (n := 2) 0), Bdd.fromVar_Ordered⟩ ⟨(Bdd.fromVar (n := 2) 1), Bdd.fromVar_Ordered⟩), Apply.apply_spec.1⟩), Reduce.reduce_spec.1⟩


#eval! Compactify.compactify' ⟨(Apply.apply Bool.and ⟨(Bdd.fromVar (n := 2) 0), Bdd.fromVar_Ordered⟩ ⟨(Bdd.fromVar (n := 2) 1), Bdd.fromVar_Ordered⟩), Apply.apply_spec.1⟩
