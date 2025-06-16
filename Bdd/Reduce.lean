import Bdd.Collect
import Bdd.Trim

open Pointer
open Bdd

private def OBdd.discover_helper : List (Fin m) → Vector (Node n m ) m → Vector (List (Fin m)) n → Vector (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => discover_helper tail v (I.set v[head].var (head :: I[v[head].var]))

private lemma OBdd.discover_helper_retains_found (O : OBdd n m) {I : Vector (List (Fin m)) n} {i : Fin n}: j ∈ I[i] → j ∈ (discover_helper l v I)[i] := by
  intro h
  cases l with
  | nil => assumption
  | cons head tail =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    cases decEq v[head.1].var i with
    | isFalse hf =>
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hf])]
      assumption
    | isTrue  ht =>
      subst ht
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_self]
      right
      assumption

private lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vector (List (Fin m)) n} :
    j ∈ l → j ∈ (discover_helper l v I).get v[j].var := by
  intro h
  cases h with
  | head as =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_set_self]
    left
  | tail b ih =>
    simp [discover_helper]
    apply discover_helper_spec O ih

/-- Return a vector whose `v`th entry is a list of node indices with variable index `v`.

This is a subroutine of `reduce`.  -/
def OBdd.discover (O : OBdd n m) : Vector (List (Fin m)) n := discover_helper (Collect.collect O) O.1.heap (Vector.replicate n [])

/-- `discover` is correct. -/
theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (discover O).get O.1.heap[j].var :=
  (discover_helper_spec O) ∘ Collect.collect_spec

namespace Reduce
private structure State (n) (m) where
  out : Vector (Node n m) m
  ids : Vector (Pointer m) m
  nid : Fin m

private def initial {n m : Nat} : State n.succ m.succ :=
  ⟨ (Vector.replicate m.succ {var := 0, low := terminal false, high := terminal true}),
    (Vector.replicate m.succ (terminal false)),
    Fin.last m
  ⟩

private def get_out : StateM (State n m) (Vector (Node n m) m) := get >>= fun s ↦ pure s.out

private def get_id : Pointer m → StateM (State n m) (Pointer m)
  | terminal b => pure (terminal b)
  | node j => get >>= fun s ↦ pure (s.ids[j])

private def set_id : Fin m → Pointer m → StateM (State n m) Unit :=
  fun j p ↦ get >>= fun s ↦ set (⟨s.out, s.ids.set j p, s.nid⟩ : State n m)

private def set_id_to_nid : Fin m → StateM (State n m) Unit :=
  fun j ↦ get >>= fun s ↦ set_id j (node s.nid)

private def set_out {n m : Nat} : Node n.succ m.succ → StateM (State n.succ m.succ) Unit :=
  fun N ↦ get >>= fun s ↦
    have : (s.nid.1 + 1) % m.succ < m.succ := by simp [Nat.mod_lt]
    set (⟨s.out.set ((s.nid.1 + 1) % m.succ) N, s.ids, s.nid + 1⟩ : State n.succ m.succ)

private def populate_queue (v : Vector (Node n m) m) (acc : List ((Pointer m × Pointer m) × Fin m)) : List (Fin m) → StateM (State n m) (List ((Pointer m × Pointer m) × Fin m))
  | [] => pure acc
  | j :: tail => do
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    if decide (lid = hid)
    then
      -- `node j` is redundant in the original BDD.
      --  Reduce it by mapping it to its child `lid` in the output BDD.
      set_id j lid
      populate_queue v acc tail
    else populate_queue v (⟨⟨lid, hid⟩, j⟩ :: acc) tail

private def process_record {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) : (Pointer m.succ × Pointer m.succ) × Fin m.succ → StateM (State n.succ m.succ) (Pointer m.succ × Pointer m.succ) := fun ⟨key, j⟩ ↦ do
  if key = curkey
  then
    -- isomorphism in original BDD, reduce.
    set_id_to_nid j
    pure curkey
  else
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    set_out ⟨v[j].var, lid, hid⟩
    set_id_to_nid j
    pure key

private def process_queue {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) :
  List ((Pointer m.succ × Pointer m.succ) × Fin m.succ) → StateM (State n.succ m.succ) Unit
  | [] => pure ()
  | head :: tail => do
    let newkey ← process_record v curkey head
    process_queue v newkey tail

private def step {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) Unit := do
  let Q ← populate_queue v [] vlist[i]
  process_queue v ⟨node 0, node 0⟩ (List.mergeSort Q)

private def loop {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) (Bdd n.succ m.succ) := do
  step v vlist i
  match h : i.1 - v[r].var.1 with
  | Nat.zero =>
    let out ← get_out
    let rid ← get_id (node r)
    pure {heap := out, root := rid}
  | Nat.succ j =>
    loop v r vlist ⟨(j + v[r].var.1), by omega⟩
termination_by i.1 - v[r].var.1
decreasing_by simp_all

private def reduce {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ :=
  match O.1.root with
  | terminal _ => O.1 -- Terminals are already reduced.
  | node r => (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1

private def reduce'' {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ × Fin m.succ :=
  match O.1.root with
  | terminal _ => ⟨O.1, 0⟩ -- Terminals are already reduced.  FIXME: return empty heap instead of original heap.
  | node r =>
    let ⟨B, S⟩ := (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial)
    ⟨B, S.nid⟩

private def zero_vars_to_bool : Bdd 0 m → Bool := fun B ↦
  match B.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ B.heap[j].var.2)

def oreduce (O : OBdd n m) : (s : Nat) × OBdd n s :=
  match n with
  | .zero =>
    ⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal (zero_vars_to_bool O.1)⟩, Bdd.Ordered_of_terminal⟩⟩
  | .succ _ =>
    match m with
    | .zero =>
      ⟨0, O⟩
    | .succ _ =>
      match h : reduce'' O with
      | ⟨B, k⟩ =>
        ⟨k.1 + 1, ⟨Trim.trim B (by omega) sorry, Trim.trim_ordered (by sorry)⟩⟩

lemma oreduce_reduced {O : OBdd n m} : OBdd.Reduced (oreduce O).2 := sorry

@[simp]
lemma oreduce_evaluate {O : OBdd n m} : (oreduce O).2.evaluate = O.evaluate := sorry

end Reduce
