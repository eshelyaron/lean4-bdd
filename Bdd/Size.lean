import Bdd.Basic
import Bdd.Collect

namespace Size

def size : OBdd n m → Nat := List.length ∘ Collect.collect

lemma isTerminal_iff_size_eq_zero {n m} {O : OBdd n m} : size O = 0 ↔ O.isTerminal := by
  constructor
  · intro h
    simp only [size, Function.comp_apply, List.length_eq_zero_iff] at h
    cases O_root_def : O.1.root with
    | terminal b => use b
    | node j =>
      have := Collect.collect_spec (j := j) (by rw [O_root_def]; exact Relation.ReflTransGen.refl)
      rw [h] at this
      contradiction
  · rintro ⟨b, hb⟩
    simp [size, Collect.collect_terminal hb]

def bool_of_size_eq_zero {n m} (O : OBdd n m) (h : size O = 0) : Bool :=
  match O_root_def : O.1.root with
  | .terminal b => b
  | .node _ => False.elim (not_isTerminal_of_root_eq_node O_root_def (isTerminal_iff_size_eq_zero.mp h))

lemma size_gt_zero_of_Sub_root_eq_node {n m} {j} {O : OBdd n m} (S : O.SubBdd) : S.1.1.root = .node j → size O > 0 := by
  contrapose
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
  intro h
  have := OBdd.sub_eq_of_isTerminal S (isTerminal_iff_size_eq_zero.mp h)
  rw [this]
  rcases isTerminal_iff_size_eq_zero.mp h with ⟨b, hb⟩
  rw [hb]
  simp

instance instNeZeroSize {j} {O : OBdd n m} (S : O.SubBdd) : S.1.1.root = .node j → NeZero (size O) := by
  intro h
  have := size_gt_zero_of_Sub_root_eq_node S h
  constructor
  linarith

lemma size_spec {O : OBdd n m} : size O = Fintype.card { j // Pointer.Reachable O.1.heap O.1.root (.node j) } := by
  simp only [size, Function.comp_apply]
  simp_rw [Fintype.card, Finset.univ]
  have : (Collect.collect O).length = (Multiset.ofList (Collect.collect O)).card := by rfl
  rw [this]
  refine Eq.symm (Finset.card_eq_of_bijective (fun i hi ↦ ⟨(Collect.collect O).get ⟨i, hi⟩, by simp; exact Collect.collect_spec_reverse (List.getElem_mem hi)⟩) ?_ ?_ ?_)
  · rintro ⟨j, hj⟩ h
    simp only [Subtype.mk.injEq, Multiset.coe_card]
    exact List.mem_iff_getElem.mp (Collect.collect_spec hj)
  · rintro i hi
    simp only [List.get_eq_getElem]
    apply Fintype.complete
  · intro i j hi hj heq
    simp only [List.get_eq_getElem, Subtype.mk.injEq] at heq
    exact (List.Nodup.getElem_inj_iff Collect.collect_nodup).mp heq

lemma size_node_le {O : OBdd n m} {h : O.1.root = .node j} :
    size O ≤ 1 + (size (O.low h)) + (size (O.high h)) := by
  rw [size_spec]
  rw [size_spec]
  rw [size_spec]
  rw [show 1 = Fintype.card {j' // j' = j} by simp]
  rw [add_assoc]
  rw [← Fintype.card_sum]
  rw [← Fintype.card_sum]
  refine Fintype.card_le_of_embedding ⟨?_, ?_⟩
  · exact
    fun ⟨j', hj'⟩ ↦ match decEq j' j with
      | isTrue ht => .inl ⟨j', ht⟩
      | isFalse hf => .inr (
        match Pointer.instDecidableReachable (O.low h) (.node j') with
        | isTrue htt => .inl ⟨j', htt⟩
        | isFalse hff => .inr ⟨j', by
          apply OBdd.reachable_or_eq_low_high at hj'
          cases hj' with
          | inl hh => simp_all
          | inr hh =>
            rcases hh with ⟨jj, hjj1, hjj2⟩
            have : Pointer.node j = .node jj := by rw [← h, hjj1]
            injection this with that
            subst that
            cases hjj2 with
            | inl hhh => simp_all
            | inr hhh => exact hhh
          ⟩
        )
  · intro x y hxy
    simp only [OBdd.low_heap_eq_heap, OBdd.high_heap_eq_heap] at hxy
    split at hxy
    next =>
      split at hxy <;> (refine Subtype.eq ?_; simp_all)
    next =>
      split at hxy <;>
      (next =>
        split at hxy
        next => simp_all
        next => split at hxy <;> (refine Subtype.eq ?_; simp_all))

lemma size_le' {O : OBdd n m} : size O ≤ 2 ^ (n - O.1.var.1) - 1 := by
  cases O_root_def : O.1.root with
  | terminal b => simp [isTerminal_iff_size_eq_zero.mpr ⟨b, O_root_def⟩]
  | node j =>
    calc _
      _ ≤ 1 + (size (O.low O_root_def)) + (size (O.high O_root_def)) := size_node_le
      _ ≤ 1 + (2 ^ (n - (O.low O_root_def).1.var.1) - 1) + (2 ^ (n - (O.high O_root_def).1.var.1) - 1) := by
        have := size_le' (O := O.low O_root_def)
        have := size_le' (O := O.high O_root_def)
        omega
      _ ≤ 1 + (2 ^ (n - (O.1.var.1 + 1)) - 1) + (2 ^ (n - (O.high O_root_def).1.var.1) - 1) := by
        simp only [Nat.succ_eq_add_one, OBdd.low_heap_eq_heap, add_le_add_iff_right, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        have := OBdd.var_lt_low_var (h := O_root_def)
        simp only [OBdd.var] at this
        omega
      _ ≤ 1 + (2 ^ (n - (O.1.var.1 + 1)) - 1) + (2 ^ (n - (O.1.var.1 + 1)) - 1) := by
        simp only [Nat.succ_eq_add_one, OBdd.low_heap_eq_heap, add_le_add_iff_right, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        have := OBdd.var_lt_high_var (h := O_root_def)
        simp only [OBdd.var] at this
        omega
      _ ≤ 1 + (2 ^ ((n - O.1.var.1) - 1) - 1) + (2 ^ (n - (O.1.var.1 + 1)) - 1) := by
        simp only [Nat.succ_eq_add_one, add_le_add_iff_right, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        omega
      _ ≤ 1 + (2 ^ ((n - O.1.var.1) - 1) - 1) + (2 ^ ((n - O.1.var.1) - 1) - 1) := by
        simp only [Nat.succ_eq_add_one, add_le_add_iff_right, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        omega
      _ ≤ 2 ^ ((n - O.1.var.1) - 1) + 2 ^ ((n - O.1.var.1) - 1) - 1 := by
        simp only [Nat.succ_eq_add_one]
        have := Nat.one_le_two_pow (n := ((n - O.1.var.1) - 1))
        omega
      _ ≤ 2*2 ^ ((n - O.1.var.1) - 1) - 1 := by omega
      _ ≤ 2 ^ (n - O.1.var.1) - 1 := by
        refine Nat.sub_le_sub_right ?_ 1
        apply le_of_eq
        refine mul_pow_sub_one ?_ 2
        simp [O_root_def]
        omega
termination_by O

lemma size_le {O : OBdd n m} : size O ≤ 2 ^ n - 1 := by
  trans 2 ^ (n - O.1.var.1) - 1
  · exact size_le'
  · rw [tsub_le_iff_right, Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
    apply Nat.pow_le_pow_right <;> omega

end Size
