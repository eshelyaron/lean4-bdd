import Bdd.Basic

namespace Evaluate

def evaluate (O : OBdd n m) : Vector Bool n → Bool := fun I ↦
  match h : O.1.root with
  | .terminal b => b
  | .node j => if I[O.1.heap[j].var] then evaluate (O.high h) I else evaluate (O.low h) I
termination_by O

lemma evaluate_evaluate {O : OBdd n m }: evaluate O = O.evaluate := by
  ext I
  unfold evaluate
  split
  next b hb => simp [OBdd.evaluate_terminal' hb]
  next j hj =>
    have := evaluate_evaluate (O := O.low hj)
    have := evaluate_evaluate (O := O.high hj)
    simp [OBdd.evaluate_node'' hj, *]
termination_by O

lemma evaluate_terminal {O : OBdd n m} : O.1.root = .terminal b → evaluate O = Function.const _ b := by
  rw [evaluate_evaluate]
  exact OBdd.evaluate_terminal'

lemma evaluate_node {O : OBdd n m} (h : O.1.root = .node j) :
    evaluate O = fun I ↦ if I[O.1.heap[j].var] then evaluate (O.high h) I else evaluate (O.low h) I := by
  rw [evaluate_evaluate]
  rw [OBdd.evaluate_node'' h]
  simp [evaluate_evaluate]

end Evaluate
