module

public import Bdd.Basic
import Bdd.Collect

open Pointer
open Bdd

def OBdd.discover_helper : List (Fin m) → Vector (Node n m) m → Vector (List (Fin m)) n → Vector (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => OBdd.discover_helper tail v (I.set v[head].var (head :: I[v[head].var]))

lemma OBdd.discover_helper_retains_found {I : Vector (List (Fin m)) n} {i : Fin n} : j ∈ I[i] → j ∈ (OBdd.discover_helper l v I)[i] := by
  induction l generalizing I with
  | nil => exact id
  | cons head tail ih =>
    intro h
    unfold OBdd.discover_helper
    apply ih
    rcases eq_or_ne (v[head].var) i with heq | hne
    · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = head :: I[i] := by
        subst heq; simp [Vector.getElem_set_self]
      simp only [hkey]; exact List.mem_cons_of_mem _ h
    · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = I[i] :=
        Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hne)
      simp only [hkey]; exact h

lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vector (List (Fin m)) n} :
    j ∈ l → j ∈ (OBdd.discover_helper l v I)[v[j].var] := by
  intro h
  cases h with
  | head as =>
    unfold OBdd.discover_helper
    apply OBdd.discover_helper_retains_found
    simp [Vector.getElem_set_self]
  | tail b ih =>
    unfold OBdd.discover_helper
    exact OBdd.discover_helper_spec O ih

/-- Return a vector whose `v`th entry is a list of node indices with variable index `v`. -/
public def OBdd.discover (O : OBdd n m) : Vector (List (Fin m)) n :=
  OBdd.discover_helper (Collect.collect O) O.1.heap (Vector.replicate n [])

/-- `discover` is correct (forward direction). -/
public theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (OBdd.discover O)[O.1.heap[j].var] :=
  (OBdd.discover_helper_spec O) ∘ Collect.collect_spec

lemma OBdd.discover_helper_mem_var {l : List (Fin m)} {v : Vector (Node n m) m}
    {I : Vector (List (Fin m)) n} {i : Fin n} {j : Fin m} :
    j ∈ (OBdd.discover_helper l v I)[i] → j ∈ I[i] ∨ (j ∈ l ∧ v[j].var = i) := by
  induction l generalizing I with
  | nil => exact .inl
  | cons head tail ih =>
    simp only [OBdd.discover_helper]
    intro h
    rcases ih h with h | ⟨hmem, hvar⟩
    · rcases eq_or_ne (v[head].var) i with heq | hne
      · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = head :: I[i] := by
          subst heq; simp [Vector.getElem_set_self]
        rw [hkey] at h
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact .inr ⟨.head _, heq⟩
        · exact .inl h
      · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = I[i] :=
          Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hne)
        rw [hkey] at h
        exact .inl h
    · exact .inr ⟨.tail _ hmem, hvar⟩

/-- `discover` is correct (backward direction): membership implies var = i and reachability. -/
public theorem OBdd.discover_spec_inv {O : OBdd n m} {j : Fin m} {i : Fin n} :
    j ∈ (OBdd.discover O)[i] →
    O.1.heap[j].var.1 = i.1 ∧ Reachable O.1.heap O.1.root (.node j) := by
  simp only [OBdd.discover, Fin.getElem_fin]
  intro h
  rcases OBdd.discover_helper_mem_var h with h | ⟨hmem, hvar⟩
  · simp [Vector.getElem_replicate] at h
  · exact ⟨congrArg Fin.val hvar, Collect.collect_spec_reverse hmem⟩
