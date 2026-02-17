import Bdd.Lift
import Std.Data.HashMap.Lemmas

namespace Sim

private structure State (O : OBdd n m) (U : OBdd n m') where
  lr : Std.HashMap (Fin m) (Fin m')
  rl : Std.HashMap (Fin m') (Fin m)
  hl : ∀ j j',
    lr[j]? = some j' → rl[j']? = some j           ∧
    Pointer.Reachable O.1.heap O.1.root (.node j) ∧
    ∃ hj : Bdd.Ordered ⟨O.1.heap, .node j⟩,
      ∃ hj' : Bdd.Ordered ⟨U.1.heap, .node j'⟩,
        OBdd.HSimilar ⟨⟨O.1.heap, .node j⟩, hj⟩ ⟨⟨U.1.heap, .node j'⟩, hj'⟩
  hr : ∀ j j',
    rl[j']? = some j → lr[j]? = some j'            ∧
    Pointer.Reachable U.1.heap U.1.root (.node j') ∧
    ∃ hj : Bdd.Ordered ⟨O.1.heap, .node j⟩,
      ∃ hj' : Bdd.Ordered ⟨U.1.heap, .node j'⟩,
        OBdd.HSimilar ⟨⟨O.1.heap, .node j⟩, hj⟩ ⟨⟨U.1.heap, .node j'⟩, hj'⟩

private def sim_helper
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) :
  StateM
    (State O U)
    (Decidable
      (OBdd.HSimilar
        ⟨⟨O.1.heap, p⟩, Bdd.ordered_of_reachable hpr⟩
        ⟨⟨U.1.heap, q⟩, Bdd.ordered_of_reachable hqr⟩)) := do
  match hp : p with
  | .terminal b =>
    match hq : q with
    | .terminal b' =>
      if hb : b = b'
      then return isTrue (by simpa [OBdd.HSimilar, OBdd.toTree_terminal, OBdd.toTree_terminal'])
      else return isFalse (by simpa [OBdd.HSimilar, OBdd.toTree_terminal', OBdd.toTree_terminal'])
    | .node j' => return isFalse (by simp [OBdd.HSimilar, OBdd.toTree_terminal', OBdd.toTree_node])
  | .node j =>
    match hq : q with
    | .terminal b' => return isFalse (by simp [OBdd.HSimilar, OBdd.toTree_terminal', OBdd.toTree_node])
    | .node j' =>
      if hv : O.1.heap[j].var = U.1.heap[j'].var
      then
        let s ← get
        match hl : s.lr[j]? with
        | none =>
          match hr : s.rl[j']? with
          | none =>
            let hll ← sim_helper O hO U hU
              O.1.heap[j].low (.tail hpr (.low rfl))
              U.1.heap[j'].low (.tail hqr (.low rfl))
            match hll with
            | isTrue ht =>
              -- TODO : why is type declaration needed? Note that only `←` does not work, for some reason `:= ←` is needed
              let hhh : Decidable (OBdd.HSimilar ⟨Bdd.mk O.val.heap O.val.heap[j].high, _⟩ ⟨Bdd.mk U.val.heap U.val.heap[j'].high, _⟩) :=
                ← sim_helper O hO U hU
                O.1.heap[j].high (.tail hpr (.high rfl))
                U.1.heap[j'].high (.tail hqr (.high rfl))
              match hhh with
              | isTrue ht' =>
                set
                  (⟨s.lr.insert j j', s.rl.insert j' j,
                    fun jj jj' hjj ↦ by
                      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hjj
                      split at hjj
                      next heq =>
                        subst heq
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          simp only [true_and]
                          constructor
                          · exact hpr
                          · use Bdd.ordered_of_reachable hpr
                            use Bdd.ordered_of_reachable hqr
                            simp only [OBdd.HSimilar]
                            conv =>
                              lhs
                              rw [OBdd.toTree_node]
                            conv =>
                              rhs
                              rw [OBdd.toTree_node]
                            congr 1
                        next heqq => injection hjj; contradiction
                      next heq =>
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          rw [(s.hl jj j' hjj).1] at hr
                          contradiction
                        next heqq =>
                          exact s.hl jj jj' hjj,
                    fun jj jj' hjj ↦ by
                      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hjj
                      split at hjj
                      next heq =>
                        subst heq
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          simp only [true_and]
                          constructor
                          · exact hqr
                          · use Bdd.ordered_of_reachable hpr
                            use Bdd.ordered_of_reachable hqr
                            simp only [OBdd.HSimilar]
                            conv =>
                              lhs
                              rw [OBdd.toTree_node]
                            conv =>
                              rhs
                              rw [OBdd.toTree_node]
                            congr 1
                        next heqq => injection hjj; contradiction
                      next heq =>
                        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                        split
                        next heqq =>
                          subst heqq
                          rw [(s.hr j jj' hjj).1] at hl
                          contradiction
                        next heqq =>
                          exact s.hr jj jj' hjj
                   ⟩ : State O U)
                return isTrue (by
                  simp only [OBdd.HSimilar]
                  conv =>
                    lhs
                    rw [OBdd.toTree_node]
                  conv =>
                    rhs
                    rw [OBdd.toTree_node]
                  congr 1
                )
              | isFalse hf' => return isFalse (fun c ↦ by simp [OBdd.HSimilar, OBdd.toTree_node, OBdd.high, Bdd.high] at c; exact hf' c.2.2)
            | isFalse hf => return isFalse (fun c ↦ by simp [OBdd.HSimilar, OBdd.toTree_node, OBdd.low, Bdd.low] at c; exact hf c.2.1)
          | some i =>
            return isFalse (by
              rcases s.hr i j' hr with ⟨h1, h2, h3, h4, h5⟩
              intro contra
              simp only [OBdd.HSimilar] at contra h5
              rw [← contra] at h5
              rcases s.hl i j' h1 with ⟨h1', h2', h3', h4', h5'⟩
              have := @hO.2 ⟨(Pointer.node i), h2'⟩ ⟨(Pointer.node j), hpr⟩ h5
              simp [InvImage] at this
              subst this
              rw [h1] at hl
              contradiction
            )
        | some i' =>
          if heq : j' = i'
          then
            return isTrue (s.hl j j' (by simp_all)).2.2.2.2
          else
            return isFalse (fun c ↦ heq (by
              rcases s.hl j i' hl with ⟨h1, h2, h3, h4, h5⟩
              simp only [OBdd.HSimilar] at c h5
              rw [c] at h5
              rcases s.hr j i' h1 with ⟨h1', h2', h3', h4', h5'⟩
              have := @hU.2 ⟨.node j', hqr⟩ ⟨.node i', h2'⟩ h5
              simp [InvImage] at this
              exact this
            ))
      else return isFalse (by simp_all [OBdd.HSimilar, OBdd.toTree_node])
termination_by OBdd.size' (⟨⟨O.1.heap, p⟩, Bdd.ordered_of_reachable hpr⟩ : OBdd n m)
decreasing_by
  · simp [OBdd.size_node, OBdd.low, Bdd.low]; omega
  · simp [OBdd.size_node, OBdd.high, Bdd.high]

instance instDecidableRobddHSimilar
    (O : OBdd n m) (hO : O.Reduced)
    (U : OBdd n m') (hU : U.Reduced) :
    Decidable (O.HSimilar U) :=
  ((sim_helper O hO U hU O.1.root .refl U.1.root .refl)
    ⟨ Std.HashMap.emptyWithCapacity 0,
      Std.HashMap.emptyWithCapacity 0,
      by simp,
      by simp
    ⟩
  ).1

end Sim
