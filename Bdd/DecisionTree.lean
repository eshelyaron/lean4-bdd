import Mathlib.Data.Vector.Basic

inductive DecisionTree n where
  | leaf   : Bool  → DecisionTree _
  | branch : Fin n → DecisionTree n → DecisionTree n → DecisionTree n
deriving DecidableEq

namespace DecisionTree

def evaluate : DecisionTree n → Vector Bool n → Bool
  | leaf b, _ => b
  | branch j l h, v => if v[j] then h.evaluate v else l.evaluate v

def size {n} : DecisionTree n → Nat
  | leaf _ => 0
  | branch _ l h => 1 + l.size + h.size

inductive usesVar (i : Fin n) : DecisionTree n → Prop where
  | here : usesVar i (.branch i _ _)
  | low : usesVar i l → usesVar i (.branch _ l _)
  | high : usesVar i h → usesVar i (.branch _ _ h)

lemma usesVar_iff (i : Fin n) (T : DecisionTree n) :
    T.usesVar i ↔ (∃ i' l h, T = .branch i' l h ∧ (i = i' ∨ l.usesVar i ∨ h.usesVar i)) := by
  constructor
  · intro h
    cases h with
    | here => simp
    | low hl => simp [hl]
    | high hh => simp [hh]
  · rintro ⟨i', l, h, h1, h2⟩
    cases h2 with
    | inl => simp_all [usesVar.here]
    | inr h2 =>
      cases h2 with
      | inl => simp_all [usesVar.low]
      | inr => simp_all [usesVar.high]

end DecisionTree
