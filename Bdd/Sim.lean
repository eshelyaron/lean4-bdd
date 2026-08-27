module

public import Bdd.Basic
import Std.Data.HashMap.Lemmas

namespace Sim

structure State {n m m'} (O : OBdd n m) (U : OBdd n m') where
  lr : Std.HashMap (Fin m) (Fin m')
  rl : Std.HashMap (Fin m') (Fin m)
  hl : ∀ j j',
    lr[j]? = some j' → rl[j']? = some j           ∧
    ∃ hj hj', OBdd.Similar (O.subBdd ⟨.node j, hj⟩) (U.subBdd ⟨.node j', hj'⟩)
  hr : ∀ j j',
    rl[j']? = some j → lr[j]? = some j'            ∧
    ∃ hj hj', OBdd.Similar (O.subBdd ⟨.node j, hj⟩) (U.subBdd ⟨.node j', hj'⟩)

def State.insert {n m m'} {O : OBdd n m} {U : OBdd n m'} (s : State O U) (j : Fin m) (j' : Fin m')
    (hrj : Pointer.Reachable O.bdd.heap O.bdd.root (Pointer.node j))
    (hrj' : Pointer.Reachable U.bdd.heap U.bdd.root (Pointer.node j'))
    (hv : O.bdd.heap[j].var = U.bdd.heap[j'].var)
    (hl : s.lr[j]? = none)
    (hr : s.rl[j']? = none)
    (h : (O.subBdd ⟨O.bdd.heap[j].low, .snoc hrj Edge.low⟩).Similar
      (U.subBdd ⟨U.bdd.heap[j'].low, .snoc hrj' Edge.low⟩))
    (h' : (O.subBdd ⟨O.bdd.heap[j].high, .snoc hrj Edge.high⟩).Similar
      (U.subBdd ⟨U.bdd.heap[j'].high, .snoc hrj' Edge.high⟩))
    : State O U where
  lr := s.lr.insert j j'
  rl := s.rl.insert j' j
  hl jj jj' hjj := by
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hjj
    split at hjj
    next heq =>
      subst heq
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
      split
      next heqq =>
        subst heqq
        simp only [true_and]
        use hrj, hrj'
        simp only [OBdd.similar_iff] at ⊢ h h'
        rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j, _⟩)]
        rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j', _⟩)]
        simp only [OBdd.heap_subBdd, OBdd.low_subBdd, OBdd.high_subBdd,
          DecisionTree.branch.injEq]
        exact ⟨hv, h, h'⟩
      next heqq => injection hjj; contradiction
    next heq =>
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
      split
      next heqq =>
        subst heqq
        rw [(s.hl jj j' hjj).1] at hr
        contradiction
      next heqq =>
        exact s.hl jj jj' hjj
  hr jj jj' hjj := by
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hjj
    split at hjj
    next heq =>
      subst heq
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
      split
      next heqq =>
        subst heqq
        simp only [true_and]
        use hrj, hrj'
        simp only [OBdd.similar_iff] at ⊢ h h'
        rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j, _⟩)]
        rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j', _⟩)]
        simp only [OBdd.heap_subBdd, OBdd.low_subBdd, OBdd.high_subBdd,
          DecisionTree.branch.injEq]
        exact ⟨hv, h, h'⟩
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

def sim_helper {n m m'}
    (O : OBdd n m) (hO : OBdd.Reduced O)
    (U : OBdd n m') (hU : OBdd.Reduced U)
    (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p)
    (q : Pointer m') (hqr : Pointer.Reachable U.1.heap U.1.root q) :
  StateM
    (State O U)
    (Decidable (OBdd.Similar (O.subBdd ⟨p, hpr⟩) (U.subBdd ⟨q, hqr⟩))) :=
  match hp : p with
  | .terminal b =>
    match hq : q with
    | .terminal b' =>
      if hb : b = b'
      then return isTrue <| by simpa [OBdd.similar_iff, OBdd.toTree_terminal]
      else return isFalse <| by simpa [OBdd.similar_iff, OBdd.toTree_terminal]
    | .node j' =>
      return isFalse <| by simp [OBdd.similar_iff, OBdd.toTree_terminal, OBdd.toTree_node]
  | .node j =>
    match hq : q with
    | .terminal b' =>
      return isFalse <| by simp [OBdd.similar_iff, OBdd.toTree_terminal, OBdd.toTree_node]
    | .node j' =>
      if hv : O.1.heap[j].var = U.1.heap[j'].var
      then do
        let s ← get
        match hl : s.lr[j]? with
        | none =>
          match hr : s.rl[j']? with
          | none =>
            let hll ← sim_helper O hO U hU
              O.1.heap[j].low (.snoc hpr .low) U.1.heap[j'].low (.snoc hqr .low)
            if h : (O.subBdd ⟨O.bdd.heap[j].low, _⟩).Similar (U.subBdd ⟨U.bdd.heap[j'].low, _⟩) then
              let hhh :=
                ← sim_helper O hO U hU
                O.1.heap[j].high (Pointer.Reachable.snoc hpr .high)
                U.1.heap[j'].high (Pointer.Reachable.snoc hqr .high)
              if h' : (O.subBdd ⟨O.bdd.heap[j].high, _⟩).Similar (U.subBdd ⟨U.bdd.heap[j'].high, _⟩) then
                set (s.insert j j' hpr hqr hv hl hr h h')
                return isTrue <| by
                  simp only [OBdd.similar_iff] at ⊢ h h'
                  rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j, _⟩)]
                  rw [OBdd.toTree_node (OBdd.root_subBdd ⟨.node j', _⟩)]
                  simp only [OBdd.heap_subBdd, OBdd.low_subBdd, OBdd.high_subBdd,
                    DecisionTree.branch.injEq]
                  exact ⟨hv, h, h'⟩
              else
                return isFalse <| by
                  intro c
                  have := OBdd.similar_high (OBdd.root_subBdd _) (OBdd.root_subBdd _) c
                  grind only [OBdd.high_subBdd]
            else
              return isFalse <| by
                intro c
                have := OBdd.similar_low (OBdd.root_subBdd _) (OBdd.root_subBdd _) c
                grind only [OBdd.low_subBdd]
          | some i =>
            return isFalse <| by
              rcases s.hr i j' hr with ⟨h1, h2, h3, h4⟩
              rcases s.hl i j' h1 with ⟨h1', h2', h3', h4'⟩
              intro contra
              have hsim : OBdd.SimilarRP ⟨.node i, h2'⟩ ⟨.node j, hpr⟩ := by
                rw [OBdd.similar_iff] at contra h4
                rw [OBdd.similarRP_iff, contra]
                exact h4
              have h := hO.2 hsim
              simp [InvImage] at h
              subst h
              rw [h1] at hl
              contradiction
        | some i' =>
          if heq : j' = i'
          then
            return isTrue (s.hl j j' (by simp_all)).2.2.2
          else
            return isFalse <| by
              intro c
              rcases s.hl j i' hl with ⟨h1, h2, h3, h4⟩
              rcases s.hr j i' h1 with ⟨h1', h2', h3', h4'⟩
              have hsim : OBdd.SimilarRP ⟨.node j', hqr⟩ ⟨.node i', h3'⟩ := by
                rw [OBdd.similarRP_iff]
                rw [OBdd.similar_iff] at c h4
                rw [c] at h4
                exact h4
              have := hU.2 hsim
              simp [InvImage] at this
              exact heq this
      else return isFalse <| by simp_all [OBdd.similar_iff, OBdd.toTree_node]
termination_by OBdd.size' ⟨⟨O.1.heap, p⟩, O.ordered_of_reachable hpr⟩
decreasing_by
  · simp [OBdd.size'_node, OBdd.low_eq, Bdd.low_eq]; omega
  · simp [OBdd.size'_node, OBdd.high_eq, Bdd.high_eq]; omega

public def decidableRobddHSimilar {n m m'}
    (O : OBdd n m) (hO : O.Reduced)
    (U : OBdd n m') (hU : U.Reduced) :
    Decidable (O.Similar U) :=
  O.subBdd_root ▸ U.subBdd_root ▸
    (sim_helper O hO U hU O.1.root .refl U.1.root .refl ⟨∅, ∅, by simp, by simp⟩).1

end Sim
