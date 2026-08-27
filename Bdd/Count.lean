module

public import Mathlib.Data.Fintype.Vector
public import Bdd.Basic

import Std.Data.HashMap.Lemmas
import Mathlib.Data.Fintype.BigOperators

namespace Count

@[expose]
public def Solution {n m} (O : OBdd n m) := { I : Vector Bool n // O.evaluate I = true}

lemma solution_iff_exists {n m} (O : OBdd n m) {I} (i : Fin n) :
    O.evaluate I = true ↔ ∃ b, I[i] = b ∧ O.evaluate I = true := by simp

lemma solution_iff_or {n m} (O : OBdd n m) (i : Fin n) :
    (fun I ↦ O.evaluate I = true) = (fun I ↦ (I[i] = false ∧ O.evaluate I = true) ∨ (I[i] = true ∧ O.evaluate I = true)) := by
  ext I
  nth_rw 1 [solution_iff_exists O i]
  simp only [Bool.exists_bool]

def my_vector_equiv_vector : List.Vector α n ≃ Vector α n where
  toFun     := fun l ↦ ⟨l.toList.toArray, .trans List.size_toArray   (List.Vector.toList_length _)⟩
  invFun    := fun v ↦ ⟨v.toList,         .trans Array.length_toList (Vector.size_toArray       _)⟩
  left_inv _  := rfl
  right_inv _ := rfl

@[no_expose]
public instance instVectorFintype {α} [Fintype α] {n : ℕ} : Fintype (Vector α n) :=
  Fintype.ofEquiv (List.Vector α n) my_vector_equiv_vector

@[simp]
lemma my_card_vector {α} [Fintype α] (n : Nat) : Fintype.card (Vector α n) = Fintype.card α ^ n :=
  .trans (Fintype.ofEquiv_card my_vector_equiv_vector) (card_vector n)

public instance instFintypeSolution {n m} {O : OBdd n m} : Fintype (Solution O) := Subtype.fintype _

public abbrev numSolutions {n m} (O : OBdd n m) : Nat := Fintype.card (Solution O)

lemma numSolutions_eq_card_or {n m} (O : OBdd n m) (i : Fin n) :
    numSolutions O = Fintype.card {I : Vector Bool n // (I[i] = false ∧ O.evaluate I = true) ∨ (I[i] = true ∧ O.evaluate I = true)} :=
  Fintype.card_congr (Equiv.subtypeEquivProp (solution_iff_or ..))

lemma card_solution_low {n m} (O : OBdd n m) {j} (h : O.1.root = .node j):
    Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = false ∧ O.evaluate I = true} =
    Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = false ∧ (O.low h).evaluate I = true} :=
  Fintype.card_congr (Equiv.subtypeEquivProp (by
    ext I
    simp only [Fin.getElem_fin, and_congr_right_iff, Bool.coe_iff_coe]
    intro hf
    rw [OBdd.evaluate_low_eq_evaluate_set_false]
    simp only [Fin.getElem_fin, Function.comp_apply]
    congr
    rw [← hf]
    simp only [Vector.set_getElem_self]
  ))

lemma card_solution_high {n m} (O : OBdd n m) {j} (h : O.1.root = .node j):
    Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = true ∧ O.evaluate I = true} =
    Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = true ∧ (O.high h).evaluate I = true} :=
  Fintype.card_congr (Equiv.subtypeEquivProp (by
    ext I
    simp only [Fin.getElem_fin, and_congr_right_iff, Bool.coe_iff_coe]
    intro hf
    rw [OBdd.evaluate_high_eq_evaluate_set_true]
    simp only [Fin.getElem_fin, Function.comp_apply]
    congr
    rw [← hf]
    simp only [Vector.set_getElem_self]
  ))

lemma aux {n} {i : Fin n} {P Q : Vector Bool n → Prop}:
    Disjoint (fun I ↦ I[i] = false ∧ P I)  (fun I ↦ I[i] = true ∧ Q I) := by
  intro p hp1 hp2
  simp only [le_bot_iff]
  ext I
  simp only [Pi.bot_apply, «Prop».bot_eq_false, iff_false]
  intro contra
  have hI1 := hp1 I contra
  have hI2 := hp2 I contra
  simp_all

lemma aux_low {n m j I b} {O : OBdd n m} {h : O.1.root = .node j}:
    (O.low h).evaluate (I.set (O.1.heap[j.1].var : Fin n) b) = (O.low h).evaluate I := by
  have : Nary.IndependentOf (O.low h).evaluate O.1.heap[j.1].var := by
    apply OBdd.independentOf_lt_root (O := (O.low h)) (i := ⟨O.1.heap[j.1].var.1, ?_⟩)
    have := OBdd.var_lt_low_var (O := O) (h := h)
    simp [O.var_node, h] at this
    exact this
  simp_all

lemma aux_high {n m j I b} {O : OBdd n m} {h : O.1.root = .node j}:
    (O.high h).evaluate (I.set (O.1.heap[j.1].var) b) = (O.high h).evaluate I := by
  have : Nary.IndependentOf (O.high h).evaluate O.1.heap[j.1].var := by
    apply OBdd.independentOf_lt_root (O := (O.high h)) (i := ⟨O.1.heap[j.1].var.1, ?_⟩)
    have := OBdd.var_lt_high_var (O := O) (h := h)
    simp [O.var_node, h] at this
    exact this
  simp_all

lemma numSolutions_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = .node j) :
    numSolutions O + numSolutions O = numSolutions (O.low h) + numSolutions (O.high h) := by
  nth_rw 1 [numSolutions_eq_card_or O O.1.heap[j].var]
  rw [Fintype.card_subtype_or_disjoint _ _ aux]
  · rw [card_solution_low O h]
    rw [card_solution_high O h]
    nth_rw 1 [numSolutions_eq_card_or O O.1.heap[j].var]
    rw [Fintype.card_subtype_or_disjoint _ _ aux]
    · rw [card_solution_low O h]
      rw [card_solution_high O h]
      have h1 : Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.low h).evaluate I = true } = Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.low h).evaluate I = true } :=
        Fintype.card_congr
          { toFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var true, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_low]⟩
            invFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var false, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_low]⟩,
            left_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
            right_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
          }
      have h2 : Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.high h).evaluate I = true } = Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.high h).evaluate I = true } :=
        Fintype.card_congr
          { toFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var false, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_high]⟩
            invFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var true, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_high]⟩,
            left_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
            right_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
          }
      nth_rw 1 [h1]
      nth_rw 1 [h2]
      calc _
        _ = Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.low h).evaluate I = true } + Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.low h).evaluate I = true } +
            (Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.high h).evaluate I = true } + Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.high h).evaluate I = true }) := by omega
      rw [← Fintype.card_subtype_or_disjoint _ _ aux]
      rw [← Fintype.card_subtype_or_disjoint _ _ aux]
      rw [← numSolutions_eq_card_or _ O.1.heap[j].var]
      rw [← numSolutions_eq_card_or _ O.1.heap[j].var]

def Invariant {n m} (heap : Vector (Node n m) m) (s : Std.HashMap (Pointer m) Nat) :=
  ∀ p (hp : p ∈ s), ∃ ho : Bdd.Ordered ⟨heap, p⟩, s[p]'hp = numSolutions ⟨⟨heap, p⟩, ho⟩

def PostCond {n m} (O : OBdd n m) (s r : Std.HashMap (Pointer m) Nat) :=
  ∀ p,
    (∀ i, s[p]? = some i → r[p]? = some i) ∧
    (r[p]? = none → s[p]? = none) ∧
    (s[p]? = none → (∃ i, r[p]? = some i) → Pointer.Reachable O.1.heap O.1.root p)

instance postCond_refl {n m} {O : OBdd n m} : Std.Refl (PostCond O) where
  refl := by
    intro _ _
    grind only

lemma postCond_terminal {n m} {O : OBdd n m} {s b i}
    (hr : s[O.1.root]? = none) (h : O.1.root = Pointer.terminal b) :
    PostCond O s (s.insert (Pointer.terminal b) i) := by
  intro p
  constructor
  · intro i hi
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
    split
    next heq =>
      subst heq
      simp_all
    next => exact hi
  · constructor
    · simp_all
    · intro hp1 ⟨_, hp2⟩
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hp2
      split at hp2
      next heq =>
        injection hp2 with hpi
        subst hpi
        subst heq
        rw [h]
        exact Pointer.Reachable.refl
      next => simp_all

lemma invariant_false {n m} (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat )
    (inv : Invariant O.bdd.heap s) :
    Invariant O.bdd.heap (s.insert (Pointer.terminal false) 0) := by
  intro p hp
  simp only [Std.HashMap.mem_insert, beq_iff_eq] at hp
  cases hp with
  | inl hp =>
    subst hp
    simp [Bdd.ordered_of_terminal, numSolutions, Solution]
  | inr hp =>
    obtain ⟨ha, hb⟩ := inv p hp
    use ha
    rw [Std.HashMap.getElem_insert]
    simp only [beq_iff_eq]
    split
    next heq => subst heq; simp [numSolutions, Solution]
    next => exact hb

lemma invariant_true {n m} (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat )
    (inv : Invariant O.bdd.heap s) :
    Invariant O.bdd.heap (s.insert (Pointer.terminal true) (2 ^ n)) := by
  intro p hp
  simp only [Std.HashMap.mem_insert, beq_iff_eq] at hp
  cases hp with
  | inl hp =>
    subst hp
    simp [Bdd.ordered_of_terminal, numSolutions, Solution]
  | inr hp =>
    obtain ⟨ha, hb⟩ := inv p hp
    use ha
    rw [Std.HashMap.getElem_insert]
    simp only [beq_iff_eq]
    split
    next heq => subst heq; simp [numSolutions, Solution]
    next => exact hb

lemma invariant_node {n m j} (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat )
    (inv : Invariant O.bdd.heap s) (h : O.1.root = Pointer.node j) :
    Invariant O.bdd.heap (s.insert (Pointer.node j) (((numSolutions (O.low h)) + (numSolutions (O.high h))) / 2)) := by
  intro p hp
  simp only [Std.HashMap.mem_insert, beq_iff_eq] at hp
  cases hp with
  | inl hp =>
    subst hp
    simp_rw [← h]
    use O.2
    simp only [Std.HashMap.getElem_insert_self]
    symm
    apply Nat.eq_div_of_mul_eq_left
    · omega
    · rw [Nat.mul_two]
      exact numSolutions_node h
  | inr hp =>
    obtain ⟨ha, hb⟩ := inv p hp
    use ha
    rw [Std.HashMap.getElem_insert]
    simp only [beq_iff_eq]
    split
    next heq =>
      subst heq
      simp_rw [← h]
      symm
      apply Nat.eq_div_of_mul_eq_left
      · omega
      · rw [Nat.mul_two]
        exact numSolutions_node h
    next => exact hb

def count_helper {n m} (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat) :
    Std.HashMap (Pointer m) Nat :=
  match s[O.1.root]? with
  | some _ => s
  | none =>
    match h : O.1.root with
    | .terminal false => s.insert (.terminal false) 0
    | .terminal true => s.insert (.terminal true) (2 ^ n)
    | .node j =>
      let sl := count_helper (O.low h) s
      let sh := count_helper (O.high h) sl
      sh.insert (.node j) ((sh[(O.low h).1.root]! + sh[(O.high h).1.root]!) / 2)
termination_by O

lemma count_helper_correct {n m} (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat)
    {r} (heq : r = count_helper O s) (inv : Invariant O.bdd.heap s) :
    Invariant O.bdd.heap r ∧ O.bdd.root ∈ r ∧ PostCond O s r := by
  subst heq
  fun_induction count_helper with
  | case1 O s r heq =>
    split_ands
    · exact inv
    · grind only [= getElem?_neg]
    · exact refl s
  | case2 O s heq O_root_def =>
    split_ands
    · exact invariant_false O s inv
    · grind only [Std.HashMap.mem_insert]
    · exact postCond_terminal heq O_root_def
  | case3 O s heq O_root_def =>
    split_ands
    · exact invariant_true O s inv
    · grind only [Std.HashMap.mem_insert]
    · exact postCond_terminal heq O_root_def
  | case4 O s heq j O_root_def sl sh ihl ihh =>
    simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low, OBdd.high_heap_eq_heap,
      OBdd.high_root_eq_high] at ihl ihh ⊢
    have ⟨invl, hl1, hl2⟩ := ihl inv
    have ⟨invh, hh1, hh2⟩ := ihh invl
    have hlh : O.bdd.heap[j].low ∈ sh := by
        apply Std.HashMap.mem_iff_isSome_getElem?.mp at hl1
        apply Option.eq_some_of_isSome at hl1
        have := (hh2 _).1 _ hl1
        apply Std.HashMap.mem_iff_isSome_getElem?.mpr
        apply Option.isSome_of_eq_some
        exact this
    rw [getElem!_pos _ _ hlh, getElem!_pos _ _ hh1]
    split_ands
    · rw [(invh _ hh1).2]; rw [(invh _ hlh).2]
      simp only [OBdd.mk_eq_low O_root_def, OBdd.mk_eq_high O_root_def]
      exact invariant_node O sh invh O_root_def
    · simp only [O_root_def, Std.HashMap.mem_insert, BEq.rfl, true_or]
    · intro p
      constructor
      · intro i hpi
        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
        split
        next heq =>
          subst heq
          simp_all
        next =>
          exact (hh2 _).1 _ ((hl2 _).1 _ hpi)
      · constructor
        · intro hn
          simp only [getElem?_eq_none_iff, Std.HashMap.mem_insert, beq_iff_eq, not_or] at hn
          rcases hn with ⟨hn1, hn2⟩
          rw [← getElem?_eq_none_iff] at hn2
          exact (hl2 _).2.1 ((hh2 _).2.1 hn2)
        · intro hp1 ⟨_, hp2⟩
          simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hp2
          split at hp2
          next heq =>
            injection hp2 with hpi
            subst hpi
            subst heq
            rw [O_root_def]
            exact Pointer.Reachable.refl
          next i _ =>
            cases hm : sl[p]? with
            | none =>
              trans O.bdd.heap[j].high
              · exact O.bdd.reachable_high O_root_def
              · have := (hh2 p).2.2 hm ⟨i, hp2⟩
                simp_all only [OBdd.high_root_eq_high, OBdd.high_heap_eq_heap]
            | some val =>
              trans O.bdd.heap[j].low
              · exact O.bdd.reachable_low O_root_def
              · have := (hl2 p).2.2 hp1 ⟨_, hm⟩
                simp_all only [OBdd.low_root_eq_low, OBdd.low_heap_eq_heap]

public def count {n m} (O : OBdd n m) : Nat :=
  (count_helper O ∅)[O.1.root]!

public lemma count_correct {n m} {O : OBdd n m} : count O = numSolutions O := by
  have ⟨h1, h2, h3⟩ := count_helper_correct O ∅ rfl (by simp [Invariant])
  simp only [count, getElem!_pos _ _ h2]
  exact (h1 _ h2).2

end Count
