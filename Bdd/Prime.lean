import Bdd.Basic
import Bdd.Relabel

open Relabel

namespace Prime

@[simp]
def oprime p (O : OBdd n m) : OBdd (n + p) m := orelabel O (f := (· + p)) (by simp) (fun _ _ _ _ _ ↦ by simpa)

theorem oprime_evaluate (O : OBdd n m) :
    OBdd.evaluate (oprime p O) I = O.evaluate (Vector.cast (Eq.symm (Nat.eq_sub_of_add_eq rfl)) (I.drop p)) := by
  simp only [oprime, orelabel_evaluate, Vector.drop_eq_cast_extract, Vector.cast_cast]
  congr
  ext i hi
  simp only [Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_extract]
  simp_rw [add_comm]

lemma oprime_reduced {O : OBdd n m} : O.Reduced → (oprime p O).Reduced := orelabel_reduced

@[simp]
def ounprime (p : Fin n) (O : OBdd n m) (hp : p ≤ O.1.var) : OBdd (n - p) m := orelabel O (f := (· - p)) (fun _ ↦ by simp_all; omega) (by
  intro x y hxy hx hy
  simp only
  rcases p with ⟨pp, hp⟩
  have : O.1.var.1 ≤ x.1 := by
    rcases hx with ⟨jj, h1, h2⟩
    rw [← h2]
    rw [show O.1.heap[jj].var.1 = Pointer.toVar O.1.heap (Pointer.node jj) by simp]
    apply Pointer.mayPrecede_of_reachable O.2 h1
  simp_all only [Nat.succ_eq_add_one, gt_iff_lt]
  refine Nat.sub_lt_sub_right ?_ hxy
  trans O.1.var.1
  rw [Fin.le_iff_val_le_val] at hp
  simp_all only [Fin.val_natCast, Nat.succ_eq_add_one]
  rw [show pp % (n + 1) = pp from (Nat.mod_eq_of_lt (by omega))] at hp
  repeat assumption)

theorem ounprime_evaluate (O : OBdd n m) {p : Fin n} (hp : p ≤ O.1.var) {I : Vector Bool (n - p)} {J : Vector Bool p} :
    OBdd.evaluate (ounprime p O hp) I = O.evaluate (Vector.cast (by omega) (J ++ I)) := by
  simp only [ounprime, orelabel_evaluate]
  apply OBdd.evaluate_eq_of_forall_usesVar
  intro i hi
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_cast]
  have : O.1.var.1 ≤ i.1 := by
    rcases hi with ⟨jj, h1, h2⟩
    rw [← h2]
    rw [show O.1.heap[jj].var.1 = Pointer.toVar O.1.heap (Pointer.node jj) by simp]
    apply Pointer.mayPrecede_of_reachable O.2 h1
  have : p.1 ≤ i.1 := by
    rw [Fin.le_iff_val_le_val] at hp
    simp_all only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.val_fin_le]
    omega
  rw [Vector.getElem_append_right]
  exact this

lemma ounprime_reduced {O : OBdd n m} {p : Fin n} {hp : p ≤ O.1.var} : O.Reduced → (ounprime p O hp).Reduced := orelabel_reduced

end Prime
