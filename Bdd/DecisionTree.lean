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

def lift : n ≤ n' → DecisionTree n → DecisionTree n'
  | _, .leaf b => .leaf b
  | e, .branch j l h => .branch ⟨j.1, by omega⟩ (lift e l) (lift e h)

lemma lift_injective {n n' : Nat} {h : n ≤ n'} : Function.Injective (lift h) := by
  intro x y hxy
  cases x with
  | leaf _ =>
    cases y with
    | leaf _ => simp only [lift] at hxy; simp_all
    | branch _ _ _ => contradiction
  | branch _ _ _ =>
    cases y with
    | leaf _ => contradiction
    | branch _ _ _ =>
      simp only [lift] at hxy
      injection hxy with a b c
      rw [lift_injective b, lift_injective c]
      simp_all only [Fin.mk.injEq, DecisionTree.branch.injEq, and_self, and_true]
      ext
      simp_all only

lemma lift_evaluate {h : n ≤ n'} {T : DecisionTree n} {I : Vector Bool n'} :
    (lift h T).evaluate I = T.evaluate (Vector.cast (show (min n n') = n by simpa) (I.take n)) := by
  cases T with
  | leaf => simp [lift, DecisionTree.evaluate]
  | branch _ _ _ =>
    simp only [lift, DecisionTree.evaluate]
    rw [lift_evaluate]
    rw [lift_evaluate]
    refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
    simp only [eq_iff_iff, Bool.coe_iff_coe, Fin.getElem_fin]
    rename_i a _ _
    have : (I.take n)[a.1] = I[a.1] := by
      apply Vector.getElem_take
    rw [← this]
    rfl

def relabel {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : DecisionTree n → DecisionTree (f n)
  | .leaf b => .leaf b
  | .branch i l h => .branch ⟨f i, hf i⟩ (relabel hf l) (relabel hf h)

lemma relabel_injective {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} {h : ∀ i i' : Fin n, T1.usesVar i → T2.usesVar i' → f i = f i' → i = i'} :
    relabel hf T1 = relabel hf T2 → T1 = T2 := by
  intro h
  cases T1 with
  | leaf _ =>
    cases T2 with
    | leaf _ => simp only [relabel] at h; simp_all
    | branch _ _ _ => contradiction
  | branch i tl th =>
    cases T2 with
    | leaf _ => contradiction
    | branch i' tl' th' =>
      simp only [relabel] at h
      injection h with a b c
      rw [relabel_injective b (hf := hf) (f := f)]
      rw [relabel_injective c (hf := hf) (f := f)]
      simp_all only [Fin.mk.injEq, branch.injEq, and_self, and_true]
      apply h
      · exact .here
      · exact .here
      · exact a
      · intro ii ii' hii hii' hfi
        apply h _ _ (usesVar.high hii) (usesVar.high hii') hfi
      · intro ii ii' hii hii' hfi
        apply h _ _ (usesVar.low hii) (usesVar.low hii') hfi

end DecisionTree
