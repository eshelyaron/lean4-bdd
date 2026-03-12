import Bdd.Reduce

open Pointer
open Bdd
open RawBdd

/-!
# Reduce2: incremental BDD reduction via the RawBdd pattern

This file re-implements `Reduce.oreduce` without pre-allocating the full heap.
Nodes are pushed one at a time as they are discovered to be non-redundant and
non-isomorphic.  No `Trim` step is needed at the end.

The high-level structure follows Bryant (1986):
1. `discover` groups input-BDD node indices by variable level.
2. For each level (bottom-up), `step` eliminates redundant nodes (low = high)
   and merges isomorphic nodes (same reduced children).
3. The mapping `ids` records, for each input node `j`, the `RawPointer` in the
   output BDD that `j` has been reduced to.

Key innovation: `ProvedState` bundles `State n m` with a direct proof `hh` that
every heap entry is self-bounded, avoiding the need for `Classical.choose` later.
-/

namespace Reduce2

-- ---------------------------------------------------------------------------
-- Instances for RawPointer (= Bool ⊕ Nat)
-- ---------------------------------------------------------------------------

private instance : DecidableEq RawPointer :=
  inferInstanceAs (DecidableEq (Bool ⊕ Nat))


private instance : LE RawPointer where
  le a b := match a, b with
    | .inl false, _       => True
    | .inl true,  .inl false => False
    | .inl true,  _       => True
    | .inr _,     .inl _  => False
    | .inr i,     .inr j  => i ≤ j

private instance : DecidableLE RawPointer :=
  fun a b => match a, b with
    | .inl false, _       => isTrue  trivial
    | .inl true,  .inl false => isFalse id
    | .inl true,  .inl true  => isTrue  trivial
    | .inl true,  .inr _  => isTrue  trivial
    | .inr _,     .inl _  => isFalse id
    | .inr i,     .inr j  => match Nat.decLe i j with
        | isTrue  h => isTrue  h
        | isFalse h => isFalse h

-- ---------------------------------------------------------------------------
-- State and ProvedState
-- ---------------------------------------------------------------------------

/-- Mutable state for the incremental reduction.

* `size` and `heap` together form the output heap built so far.
* `ids` maps each input-node index `j : Fin m` to its representative
  `RawPointer` in the output BDD.  An entry is `none` until the node has been
  processed; it is filled in bottom-up as each variable level is handled.
-/
private structure State (n) (m) where
  size : Nat
  heap : Vector (RawNode n) size
  ids  : Vector (Option RawPointer) m

/-- A `State` together with a proof that every heap entry is self-bounded. -/
private structure ProvedState (n m : Nat) where
  state : State n m
  hh    : ∀ k : Fin state.size, state.heap[k].Bounded k

private def initial (n m : Nat) : State n m :=
  ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩

private def provedStateInitial (n m : Nat) : ProvedState n m where
  state := ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩
  hh := fun k => k.elim0

-- ---------------------------------------------------------------------------
-- Primitive operations
-- ---------------------------------------------------------------------------

/-- Resolve an input pointer to its output `RawPointer`.
`h` is a proof that every node pointer in `p` has an entry in `ps.state.ids`; this
proof will be discharged from the loop invariant at each call site. -/
private def get_id {n m : Nat} (ps : ProvedState n m) (p : Pointer m)
    (h : ∀ j, p = .node j → (ps.state.ids[j]).isSome) : RawPointer :=
  match p with
  | .terminal b => .inl b
  | .node j     => (ps.state.ids[j]).get (h j rfl)

/-- Record that input node `j` maps to output pointer `p`. -/
private def set_id {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) : ProvedState n m :=
  { state := { size := ps.state.size, heap := ps.state.heap, ids := ps.state.ids.set j (some p) },
    hh    := ps.hh }

/-- Push a new node and extend the heap-boundedness proof. -/
private def push_node {n m : Nat} (ps : ProvedState n m) (N : RawNode n)
    (hN : N.Bounded ps.state.size) : ProvedState n m × RawPointer :=
  let hh' : ∀ k : Fin (ps.state.size + 1), (ps.state.heap.push N)[k].Bounded k := fun k => by
    by_cases hlt : k.1 < ps.state.size
    · simp only [Fin.getElem_fin, Vector.getElem_push_lt hlt]
      exact ps.hh ⟨k.1, hlt⟩
    · have hk : k.1 = ps.state.size := by omega
      simp only [Fin.getElem_fin, show k.1 = ps.state.size from hk,
                 Vector.getElem_push_eq]
      exact hN
  ⟨⟨{ size := ps.state.size + 1, heap := ps.state.heap.push N, ids := ps.state.ids }, hh'⟩,
   .inr ps.state.size⟩

-- ---------------------------------------------------------------------------
-- Invariant
-- ---------------------------------------------------------------------------

/-- The loop invariant. `hh` is now a direct field of `ps`, not wrapped in ∃. -/
private def Invariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat) : Prop :=
  -- Completeness
  (∀ (j : Fin m),
      i < O.1.heap[j].var.1 →
      Reachable O.1.heap O.1.root (.node j) →
      (ps.state.ids[j]).isSome) ∧
  -- Correctness
  ∀ (j : Fin m) (ptr : RawPointer),
      ps.state.ids[j] = some ptr →
      ∃ hj   : Bdd.Ordered ⟨O.1.heap, .node j⟩,
        ∃ hptr : ptr.Bounded ps.state.size,
          ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩,
            OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ ∧
            ∀ I,
              OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ I =
              OBdd.evaluate ⟨⟨O.1.heap, .node j⟩, hj⟩ I

private lemma inv_initial {n m : Nat} {O : OBdd n m} {i : Nat}
    (hi : ∀ j : Fin m, O.1.heap[j].var.1 ≤ i) :
    Invariant O (provedStateInitial n m) i :=
  ⟨fun j h _ => absurd h (Nat.not_lt.mpr (hi j)),
   fun j ptr h => by simp [provedStateInitial] at h⟩

lemma Invariant.ids_isSome {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat} (inv : Invariant O ps i)
    {j : Fin m}
    (hvar  : i < O.1.heap[j].var.1)
    (hreach : Reachable O.1.heap O.1.root (.node j)) :
    (ps.state.ids[j]).isSome :=
  inv.1 j hvar hreach

-- ---------------------------------------------------------------------------
-- Pure proof-carrying algorithm functions
-- ---------------------------------------------------------------------------

/-- For each node j in l: if lid = hid (redundant), set ids[j] := lid;
otherwise add to accumulator. -/
private def populate_queue {n m : Nat} (O : OBdd n m)
    (i : Fin n)
    (acc : List ((RawPointer × RawPointer) × Fin m)) :
    (l : List (Fin m)) →
    (ps : ProvedState n m) →
    Invariant O ps i.1 →
    (∀ j ∈ l, O.1.heap[j].var.1 = i.1) →
    (∀ j ∈ l, Reachable O.1.heap O.1.root (.node j)) →
    { p : ProvedState n m × List ((RawPointer × RawPointer) × Fin m) //
        Invariant O p.1 i.1 ∧
        p.1.state.size = ps.state.size ∧
        ∀ j ∈ l, (∃ key, (key, j) ∈ p.2) ∨ (p.1.state.ids[j]).isSome }
  | [], ps, inv, _, _ =>
      ⟨⟨ps, acc⟩, inv, rfl, fun j hj => by simp at hj⟩
  | j :: tail, ps, inv, hvar, hreach => by
      sorry

/-- Process one entry from the sorted queue. -/
private def process_record {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer)
    (entry  : (RawPointer × RawPointer) × Fin m)
    (ps : ProvedState n m)
    (inv : Invariant O ps i) :
    { p : ProvedState n m × (RawPointer × RawPointer) × RawPointer //
        Invariant O p.1 i ∧
        (p.1.state.ids[entry.2]).isSome } :=
  let ⟨key, j⟩ := entry
  if key = curkey then
    -- Isomorphic: map j to the same output pointer as curptr.
    let ps' := set_id ps j curptr
    ⟨⟨ps', curkey, curptr⟩, by sorry, by sorry⟩
  else
    -- New equivalence class: push a fresh output node.
    have hN : (RawNode.mk O.1.heap[j].var key.1 key.2).Bounded ps.state.size := by sorry
    let ⟨ps', ptr⟩ := push_node ps ⟨O.1.heap[j].var, key.1, key.2⟩ hN
    let ps'' := set_id ps' j ptr
    ⟨⟨ps'', key, ptr⟩, by sorry, by sorry⟩

/-- Thread `process_record` through the entire sorted queue. -/
private def process_queue {n m : Nat} {i : Nat} (O : OBdd n m)
    (curkey : RawPointer × RawPointer) (curptr : RawPointer) :
    (Q : List ((RawPointer × RawPointer) × Fin m)) →
    (ps : ProvedState n m) →
    Invariant O ps i →
    { ps' : ProvedState n m //
        Invariant O ps' i ∧
        ∀ entry ∈ Q, (ps'.state.ids[entry.2]).isSome }
  | [], ps, inv =>
      ⟨ps, inv, fun _ h => by simp at h⟩
  | head :: tail, ps, inv =>
      let ⟨⟨ps', _, curptr'⟩, inv', hhead⟩ :=
        process_record O curkey curptr head ps inv
      let ⟨ps'', inv'', htail⟩ :=
        process_queue O curkey curptr' tail ps' inv'
      ⟨ps'', inv'', fun entry h => by
        cases h with
        | head =>
          simp at *
          exact by sorry
        | tail _ h => exact htail entry h⟩

/-- Process all input nodes at variable level `i`. -/
private def step {n m : Nat} (O : OBdd n m)
    (vlist : Vector (List (Fin m)) n) (i : Fin n)
    (ps : ProvedState n m) (inv : Invariant O ps i.1) :
    { ps' : ProvedState n m //
        Invariant O ps' i.1 ∧
        ∀ j ∈ vlist[i], Reachable O.1.heap O.1.root (.node j) → (ps'.state.ids[j]).isSome } := by
  sorry

-- ---------------------------------------------------------------------------
-- Proof-carrying helpers
-- ---------------------------------------------------------------------------

/-- After processing variable level `i`, the completeness extends to `i - 1`:
every reachable node at any level `≥ i` (not just `> i`) has its id set. -/
private lemma invariant_step_down {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat}
    (inv  : Invariant O ps i)
    (hset : ∀ (j : Fin m), O.1.heap[j].var.1 = i →
              Reachable O.1.heap O.1.root (.node j) → (ps.state.ids[j]).isSome)
    (hi   : 0 < i) :
    Invariant O ps (i - 1) :=
  ⟨fun j hj hreach => by
     have h : i ≤ O.1.heap[j].var.1 := by omega
     rcases h.eq_or_lt with h_eq | h_lt
     · exact hset j h_eq.symm hreach
     · exact inv.1 j h_lt hreach,
   inv.2⟩

/-- Process levels from `i` down to `O.1.heap[r].var`, returning a final state
in which `r`'s id is set and the correctness invariant holds for the root.
`h_le` witnesses that `O.1.heap[r].var.1 ≤ i.1`, maintained by the recursion. -/
private def loop_helper {n m : Nat} (O : OBdd n m) (r : Fin m)
    (hr    : O.1.root = .node r)
    (vlist : Vector (List (Fin m)) n)
    (hdiscover : ∀ (j : Fin m),
        Reachable O.1.heap O.1.root (.node j) →
        j ∈ vlist[O.1.heap[j].var])
    (i    : Fin n)
    (h_le : O.1.heap[r].var.1 ≤ i.1)
    (ps : ProvedState n m) (inv : Invariant O ps i.1) :
    { ps' : ProvedState n m //
        (ps'.state.ids[r]).isSome ∧
        ∀ (ptr : RawPointer), ps'.state.ids[r] = some ptr →
          ∃ hptr : ptr.Bounded ps'.state.size,
            ∃ ho : Bdd.Ordered ⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩,
              OBdd.Reduced ⟨⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩, ho⟩ ∧
              ∀ I, OBdd.evaluate ⟨⟨cook_heap ps'.state.heap ps'.hh, ptr.cook hptr⟩, ho⟩ I =
                   O.evaluate I } :=
  let ⟨ps₁, inv₁, hset₁⟩ := step O vlist i ps inv
  match h : i.1 - O.1.heap[r].var.1 with
  | Nat.zero =>
    have hi_eq  : O.1.heap[r].var = i :=
      Fin.ext (Nat.le_antisymm h_le (Nat.le_of_sub_eq_zero h))
    have hr_in  : r ∈ vlist[i] :=
      hi_eq ▸ hdiscover r (by rw [← hr]; exact .refl)
    have hrisSome : (ps₁.state.ids[r]).isSome :=
      hset₁ r hr_in (by rw [← hr]; exact .refl)
    ⟨ps₁, hrisSome, by sorry⟩
  | Nat.succ j =>
    have hlt    : j + O.1.heap[r].var.1 < n := by
      have := i.isLt; simp only [Nat.succ_eq_add_one] at h; omega
    have hi_pos : 0 < i.1 := by omega
    have inv₁' : Invariant O ps₁ (j + O.1.heap[r].var.1) := by
      have hbase := invariant_step_down inv₁
        (fun k hk hreach => hset₁ k (Fin.ext hk ▸ hdiscover k hreach) hreach)
        hi_pos
      simp only [Nat.succ_eq_add_one] at h
      convert hbase using 1; omega
    loop_helper O r hr vlist hdiscover
      ⟨j + O.1.heap[r].var.1, hlt⟩ (Nat.le_add_left _ _) ps₁ inv₁'
termination_by i.1 - O.1.heap[r].var.1
decreasing_by simp_all

-- ---------------------------------------------------------------------------
-- Top-level
-- ---------------------------------------------------------------------------

private def zero_vars_to_bool : Bdd 0 m → Bool
  | B => match B.root with
    | .terminal b => b
    | .node j     => False.elim (Nat.not_lt_zero _ B.heap[j].var.2)

def oreduce2 (O : OBdd n m) : (s : Nat) × OBdd n s :=
  match n with
  | .zero =>
    ⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal (zero_vars_to_bool O.1)⟩,
         Bdd.Ordered_of_terminal⟩⟩
  | .succ nn =>
    match hroot : O.1.root with
    | .terminal b =>
      ⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩⟩
    | .node r =>
      let ⟨ps, hrisSome, hcorr⟩ :=
        loop_helper O r hroot (OBdd.discover O)
          (fun j hj => OBdd.discover_spec hj)
          ⟨nn, Nat.lt_add_one nn⟩ (Nat.lt_succ_iff.mp O.1.heap[r].var.isLt)
          (provedStateInitial (nn + 1) m)
          (inv_initial (fun j => Nat.lt_succ_iff.mp O.1.heap[j].var.isLt))
      -- hh is now a direct field on ps — no Classical.choose needed for hh!
      let rid  := (ps.state.ids[r]).get hrisSome
      let hrid := hcorr rid (Option.get_mem hrisSome)
      let hptr : rid.Bounded ps.state.size        := hrid.choose
      let ho   : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, rid.cook hptr⟩ :=
        hrid.choose_spec.choose
      ⟨ps.state.size, ⟨⟨cook_heap ps.state.heap ps.hh, rid.cook hptr⟩, ho⟩⟩

lemma oreduce2_reduced {O : OBdd n m} : OBdd.Reduced (oreduce2 O).2 := sorry

@[simp]
lemma oreduce2_evaluate {O : OBdd n m} : (oreduce2 O).2.evaluate = O.evaluate := sorry

end Reduce2
