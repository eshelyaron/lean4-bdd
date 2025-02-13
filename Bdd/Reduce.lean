import Bdd.Basic
open List renaming Vector → Vec

open Pointer
open Bdd

def OBdd.discover_helper : List (Fin m) → Vec (Node n m ) m → Vec (List (Fin m)) n → Vec (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => discover_helper tail v (I.set v[head].var (head :: I.get v[head].var))

lemma OBdd.discover_helper_retains_found (O : OBdd n m) {I : Vec (List (Fin m)) n} : j ∈ I.get i → j ∈ (discover_helper l v I).get i := by
  intro h
  cases l with
  | nil => assumption
  | cons head tail =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    cases decEq v[head.1].var i with
    | isFalse hf => rw [List.Vector.get_set_of_ne hf]; assumption
    | isTrue  ht => subst ht; rw [List.Vector.get_set_same]; right; assumption

lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vec (List (Fin m)) n} :
    j ∈ l → j ∈ (discover_helper l v I).get v[j].var := by
  intro h
  cases h with
  | head as =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    rw [List.Vector.get_set_same]
    left
  | tail b ih =>
    simp [discover_helper]
    apply discover_helper_spec O ih

/-- Return a vector whose `v`th entry is a list of node indices with variable index `v`.

This is a subroutine of `reduce`.  -/
def OBdd.discover (O : OBdd n m) : Vec (List (Fin m)) n := discover_helper (collect O) O.1.heap (Vec.replicate n [])

/-- `discover` is correct. -/
theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (discover O).get O.1.heap[j].var :=
  (discover_helper_spec O) ∘ collect_spec

structure ReduceState (n) (m) where
  subgraph : Vec (Node n m) m
  ids : Vec (Pointer m) m
  nextid : Fin m

open ReduceState

def ReduceState.initial {n m : Nat} : ReduceState n.succ m.succ := ⟨(Vec.replicate m.succ {var := 0, low := terminal false, high := terminal true}), (Vec.replicate m.succ (terminal false)), Fin.last m⟩

def ReduceState.setId {n m} : Fin m → Pointer m → ReduceState n m → ReduceState n m :=
  fun j id s ↦ ⟨s.subgraph, s.ids.set j id, s.nextid⟩

def ReduceState.setSg {n m : Nat} : Node n.succ m.succ → ReduceState n.succ m.succ → ReduceState n.succ m.succ :=
  fun N s ↦ ⟨s.subgraph.set (s.nextid + 1) N, s.ids, s.nextid + 1⟩

def ReduceState.reduceId : ReduceState n m → Pointer m → Pointer m :=
  fun s p ↦
    match p with
    | terminal b => terminal b
    | node j     => s.ids[j]

def OBdd.populate_queue (v : Vec (Node n m) m) (Q : List ((Pointer m × Pointer m) × Fin m)) (s : ReduceState n m) :
    List (Fin m) → (List ((Pointer m × Pointer m) × Fin m) × ReduceState n m)
  | [] => ⟨Q, s⟩
  | u :: tail =>
    let lid := s.reduceId v[u].low
    let hid := s.reduceId v[u].high
    if decide (lid = hid)
    then populate_queue v Q (s.setId u lid) tail
    else populate_queue v (⟨⟨lid, hid⟩, u⟩ :: Q) s tail

def OBdd.reduce_process_queue {n m : Nat} (Q : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (curkey : Pointer m.succ × Pointer m.succ) (v : Vec (Node n.succ m.succ) m.succ) (s : ReduceState n.succ m.succ) : ReduceState n.succ m.succ :=
  match Q with
  | [] => s
  | head :: tail =>
    if head.1 = curkey
    then
      reduce_process_queue tail curkey v (s.setId head.2 (node s.nextid))
    else
      let s := s.setSg ⟨v[head.2].var, s.reduceId v[head.2].low, s.reduceId v[head.2].high⟩
      let s := s.setId head.2 (node s.nextid)
      reduce_process_queue tail head.1 v s

def OBdd.reduce_step {n m : Nat} (vlist : Vec (List (Fin m.succ)) n.succ) (i : Fin n.succ) (v : Vec (Node n.succ m.succ) m.succ) (s : ReduceState n.succ m.succ) : ReduceState n.succ m.succ :=
  let ⟨Q, s⟩ := populate_queue v [] s vlist[i]
  reduce_process_queue (List.mergeSort Q) ⟨node 0, node 0⟩ v s

def OBdd.reduce_loop {n m : Nat} (vlist : Vec (List (Fin m.succ)) n.succ) (v : Vec (Node n.succ m.succ) m.succ) (r : Fin m.succ) (i : Fin n.succ) (s : ReduceState n.succ m.succ) : Bdd n.succ m.succ :=
  let s := reduce_step vlist i v s
  match h : i.1 - v[r].var.1 with
  | Nat.zero    => {heap := s.subgraph, root := s.reduceId (node r)}
  | Nat.succ j  => reduce_loop vlist v r ⟨(j + v[r].var.1), by omega⟩ s
termination_by i.1 - v[r].var.1
decreasing_by simp_all

def OBdd.reduce {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ :=
  match O.1.root with
  | terminal _ => O.1 -- Terminals are already reduced.
  | node r => reduce_loop (discover O) O.1.heap r n initial

def example_not_reduced_bdd : OBdd 3 5 :=
  ⟨ { heap := ⟨[{var := 0, low := node 1, high := node 2},
                 {var := 1, low := terminal false, high := node 4},
                 {var := 1, low := node 3, high := terminal true},
                 {var := 2, low := terminal false, high := terminal true},
                 {var := 2, low := terminal false, high := terminal true}], rfl⟩
      root := node 0 },
    by apply Ordered_of_Proper; decide⟩

#eval example_not_reduced_bdd.reduce

private lemma ordered_after_reduce : example_not_reduced_bdd.reduce.Ordered := by apply Ordered_of_Proper; decide (config := {kernel := true})

example : OBdd.Reduced ⟨example_not_reduced_bdd.reduce, ordered_after_reduce⟩ := by decide (config := {kernel := true})
