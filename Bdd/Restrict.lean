import Bdd.Basic
import Bdd.Nary

namespace Restrict

private structure State (n) (m) where
  visited : Vector (Option (Pointer m)) m
  newheap : Vector (Node n m) m

private def lookup (j : Fin m) : StateM (State n m) (Option (Pointer m)) := fun ⟨V, M⟩ ↦ ⟨V[j], V, M⟩
private def store (j : Fin m) (p : Pointer m) : StateM (State n m) (Pointer m) := fun ⟨V, M⟩ ↦ ⟨p, V.set j p, M⟩
private def setj (j : Fin m) : Node n m → StateM (State n m) Unit := fun N ⟨V, M⟩ ↦ ⟨(), V, M.set j N⟩

private def restrict_helper (O : OBdd n m) (b : Bool) (i : Fin n) :
    StateM (State n m) (Pointer m) := do
  let r := O.1.root
  match hr : r with
  | .terminal _ => return r
  | .node j =>
    -- TODO: there must be a nicer way to write this get-match-return-or-else dance.
    let cached ← lookup j
    match cached with
    | some p => return p
    | none =>
      let N := O.1.heap[j]
      if N.var > i
      then -- Orderedness guarantees that we won't encounter i anywhere in this subgraph, so keep it as is.
        store j r
      else
        if N.var < i
        then
          let l ← restrict_helper (O.low  hr) b i
          let h ← restrict_helper (O.high hr) b i
          setj j ⟨N.var, l, h⟩
          store j r
        else -- Found a node with variable i, short-circuit to the appropriate child.
          store j (if b then N.high else N.low)
termination_by O

private def restrict (O : OBdd n m) (b : Bool) (i : Fin n) : Bdd n m :=
  let ⟨r, _, M⟩ := restrict_helper O b i ⟨Vector.replicate m none, O.1.heap⟩
  ⟨M,r⟩

@[simp]
private lemma restrict_toVar : Pointer.toVar (restrict O b i).heap p = Pointer.toVar O.1.heap p := by
  sorry

private lemma restrict_edge_trans : Edge (restrict O b i).heap p q → Relation.TransGen (Edge O.1.heap) p q := by
  sorry

private lemma restrict_reachable : Pointer.Reachable (restrict O b i).heap (restrict O b i).root p → Pointer.Reachable O.1.heap O.1.root p := by
  intro h
  induction h with
  | refl =>
    simp only [restrict]
    split
    next M heq => sorry
  | tail r e ih =>
    exact .trans ih (Relation.TransGen.to_reflTransGen (restrict_edge_trans e))

private lemma restrict_ordered : Bdd.Ordered (restrict O b i) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp_all only [Bdd.RelevantEdge, Bdd.RelevantMayPrecede, Pointer.MayPrecede, Nat.succ_eq_add_one]
  have : Pointer.Reachable O.1.heap O.1.root x := restrict_reachable hx
  rw [restrict_toVar]
  rw [restrict_toVar]
  exact Pointer.toVar_lt_of_trans_edge_of_ordered (Bdd.ordered_of_reachable this) (restrict_edge_trans hxy)

def orestrict (O : OBdd n m) (b : Bool) (i : Fin n) : OBdd n m := ⟨restrict O b i, restrict_ordered⟩

@[simp]
lemma orestrict_evaluate {O : OBdd n m} : (orestrict O b i).evaluate = Nary.restrict (O.evaluate) b i := sorry

end Restrict
