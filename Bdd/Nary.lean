import Mathlib.Data.Vector.Basic

namespace Nary

abbrev Func n α β := Vector α n → β

/-- `IndependentOf f i` if the output of `f` does not depend on the value of the `i`th input. -/
@[simp]
def IndependentOf (f : Func n α β) (i : Fin n) := ∀ a v, f v = f (Vector.set v i a)

/-- `DependsOn f i` if the output of `f` depends on the value of the `i`th input. -/
@[simp]
def DependsOn (f : Func n α β) (i : Fin n) := ¬ IndependentOf f i

/-- The type of indices that a given function depends on. -/
def Dependency (f : Func n α β) := { i // DependsOn f i }

lemma eq_of_forall_dependency_getElem_eq {f : Func n α β} {I J : Vector α n} :
    (∀ (x : Dependency f), I[x.1] = J[x.1]) → f I = f J := by
  induction n with
  | zero =>
    intro h
    congr
    ext i hi
    contradiction
  | succ n ih =>
    intro h
    let g : Vector α n → β := fun v ↦ f (Vector.push v I[n])
    have h2 : ∀ V : Vector α (n + 1), I[n] = V[n] → f V = g V.pop := by
      intro V hV
      simp only [g]
      congr
      ext i hi
      rw [Vector.getElem_push]
      split
      next hh => simp only [Vector.getElem_pop', g]
      next hh =>
        have : i = n := by omega
        simp_all only [DependsOn, IndependentOf, not_forall, Fin.getElem_fin, forall_exists_index, lt_self_iff_false, not_false_eq_true]
    by_cases hf : DependsOn f n
    · have h1 := h ⟨n, hf⟩
      rw [h2 I rfl]
      rw [h2 J (by convert h1 <;> simp only [Fin.natCast_eq_last, Fin.getElem_fin, Fin.val_last])]
      apply ih
      rintro ⟨x, hx⟩
      simp only [g] at hx
      have : DependsOn f x.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall, g] at hx
        rcases hx with ⟨a, V, hav⟩
        rw [show (V.set x a).push I[n] = (V.push I[n]).set x a by simp only [Vector.set_push, Fin.is_lt, ↓reduceDIte, g]] at hav
        simp only [DependsOn, IndependentOf, not_forall, g]
        use a, V.push I[n]
        exact hav
      have := h ⟨x.castSucc, this⟩
      simp_all only [DependsOn, IndependentOf, not_forall, Fin.getElem_fin, forall_exists_index,
        Fin.natCast_eq_last, Fin.val_last, Vector.getElem_push_eq, Vector.pop_push,
        Fin.coe_castSucc, Vector.getElem_pop', g]
    · simp only [DependsOn, not_not, IndependentOf] at hf
      rw [hf I[n] J]
      rw [h2 I rfl]
      rw [h2 (J.set (n : Fin (n + 1)) I[n]) (by simp only [Fin.natCast_eq_last, Fin.val_last, Vector.getElem_set_self, g])]
      apply ih
      rintro ⟨x, hx⟩
      simp only [g] at hx
      have : DependsOn f x.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall, g] at hx
        rcases hx with ⟨a, V, hav⟩
        rw [show (V.set x a).push I[n] = (V.push I[n]).set x a by simp only [Vector.set_push, Fin.is_lt, ↓reduceDIte, g]] at hav
        simp only [DependsOn, IndependentOf, not_forall, g]
        use a, V.push I[n]
        exact hav
      have := h ⟨x.castSucc, this⟩
      simp only [Fin.getElem_fin, Vector.getElem_pop', Fin.natCast_eq_last, Fin.val_last, g]
      rw [Vector.getElem_set_ne _ _ (by omega)]
      simp_all only [DependsOn, IndependentOf, not_forall, Fin.getElem_fin, forall_exists_index,
        Fin.natCast_eq_last, Fin.val_last, Vector.getElem_push_eq, Vector.pop_push,
        Fin.coe_castSucc]

@[simp]
def restrict (f : Func n α β) : α → Fin n → Func n α β := fun a i I ↦ f (I.set i a)

@[simp]
lemma restrict_const : restrict (Function.const _ b) c i = (Function.const _ b) := by ext; simp

lemma restrict_independentOf : IndependentOf (restrict f c i) i := by simp

lemma restrict_eq_self_of_independentOf : IndependentOf f i → (restrict f c i) = f := by
  intro h
  ext I
  symm
  simp_all only [IndependentOf, restrict]
  apply h

lemma restrict_if {c : Func n α Bool} :
    restrict (fun I ↦ if c I then f I else g I) b i =
    fun I ↦ if (restrict c b i I) then (restrict f b i I) else (restrict g b i I) :=
  funext (fun _ ↦ rfl)

end Nary
