import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
open List renaming Vector → Vec

/-- Pointer to a BDD node or terminal -/
inductive Pointer m where
  | terminal : Bool  → Pointer _
  | node : Fin m → Pointer m
deriving Fintype, DecidableEq

open Pointer

/-- BDD node -/
structure Node (n) (m) where
  var  : Fin n
  low  : Pointer m
  high : Pointer m
deriving DecidableEq

/-- Raw BDD -/
structure Bdd (n) (m) where
  heap : Vec (Node n m) m
  root : Pointer m
deriving DecidableEq

open Bdd

inductive Edge {n m} (w : Vec (Node n m) m) : Pointer m → Pointer m → Prop where
  | low  : w[j].low  = p → Edge w (node j) p
  | high : w[j].high = p → Edge w (node j) p

/-- Terminals have no outgoing edges. -/
lemma not_terminal_edge {q} : ¬ Edge w (terminal b) q := by
  intro contra
  contradiction

def Pointer.toVar {n m} (w : Vec (Node n m) m) : Pointer m → Fin n.succ
  | terminal _ => n
  | node j => w[j].var

@[simp]
lemma Pointer.toVar_terminal_eq {n m} (w : Vec (Node n m) m) : toVar w (terminal b) = n := rfl

@[simp]
lemma Pointer.toVar_node_eq {n m} (w : Vec (Node n m) m) {j} : toVar w (node j) = w[j].var := rfl

@[simp]
def Pointer.MayPrecede {n m} (w : Vec (Node n m) m) (p q : Pointer m) : Prop := toVar w p < toVar w q

/-- Terminals must not precede other pointers. -/
lemma Pointer.not_terminal_MayPrecede {n m} (w : Vec (Node n m) m) {q} : ¬ MayPrecede w (terminal b) q := by
  intro contra
  simp only [MayPrecede] at contra
  cases q <;> simp_all
  case node j =>
    rcases j with ⟨j, hj⟩
    simp_all
    apply Fin.ne_last_of_lt at contra
    contradiction

/-- Non-terminals may precede terminals. -/
lemma Pointer.MayPrecede_node_terminal {n m} (w : Vec (Node n m) m) {j} : MayPrecede w (node j) (terminal b) := by
  simp [Fin.castSucc_lt_last]

@[simp]
instance Vec.instMembership : Membership α (Vec α m) where mem := Membership.mem ∘ Vec.toList

def Node.RespectsOrder {n m} (v : Vec (Node n m) m) (nod : Node n m) := ∀ (j : Fin m), (nod.low = node j ∨ nod.high = node j → nod.var < v[j].var)
def Proper {n m} (v : Vec (Node n m) m) := (∀ nod ∈ v, nod.RespectsOrder v)

def Pointer.Reachable {n m} (w : Vec (Node n m) m) := Relation.ReflTransGen (Edge w)

/-- `B.RelevantPointer` is the subtype of pointers reachable from `B.point`. -/
def Bdd.RelevantPointer {n m} (B : Bdd n m) := { q // Reachable B.heap B.root q}

instance Bdd.instDecidableEqRelevantPointer : DecidableEq (Bdd.RelevantPointer B) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.eq_iff)

def Bdd.toRelevantPointer {n m} (B : Bdd n m) : B.RelevantPointer :=
  ⟨B.root, Relation.ReflTransGen.refl⟩

/-- The `Edge` relation lifted to `RelevantPointer`s. -/
@[simp]
def Bdd.GraphEdge {n m} (B : Bdd n m) (l r : B.RelevantPointer) := Edge B.heap l.1 r.1

/-- The `MayPrecede` relation lifted to `RelevantPointer`s. -/
@[simp]
def Bdd.GraphMayPrecede {n m} (B : Bdd n m) (l r : B.RelevantPointer) := MayPrecede B.heap l.1 r.1

/-- A BDD is `Ordered` if all edges relevant from the root respect the variable ordering. -/
@[simp]
def Bdd.Ordered {n m} (B : Bdd n m) := Subrelation (GraphEdge B) (GraphMayPrecede B)

/-- Terminals induce `Ordered` BDDs. -/
lemma Bdd.Ordered_of_terminal {n m} {v : Vec (Node n m) m} {b} : Bdd.Ordered {heap := v, root := terminal b} := by
  simp only [Ordered]
  intro p q h
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  cases Relation.reflTransGen_swap.mp hp <;> exfalso <;> apply not_terminal_edge <;> assumption

lemma Ordered_of_Proper (B : Bdd n m) : Proper B.heap → Ordered B := by
  rintro h ⟨p, hp⟩ ⟨q, hq⟩ e
  simp_all only [GraphEdge, GraphMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  cases e
  case low j low_q =>
    cases q
    case terminal => simp [Fin.castSucc_lt_last]
    case node i =>
      simp only [toVar_node_eq, Nat.succ_eq_add_one, Fin.getElem_fin, Fin.coe_eq_castSucc,
                 Fin.castSucc_lt_castSucc_iff, h]
      apply h
      simp only [Vec.instMembership, List.Vector.getElem_def, Function.comp_apply, List.getElem_mem]
      left
      assumption
  case high j high_q =>
    cases q
    case terminal => simp [Fin.castSucc_lt_last]
    case node i =>
      simp only [toVar_node_eq, Nat.succ_eq_add_one, Fin.getElem_fin, Fin.coe_eq_castSucc,
                 Fin.castSucc_lt_castSucc_iff]
      apply h
      simp only [Fin.getElem_fin, List.Vector.getElem_def, Vec.instMembership,
                 Function.comp_apply, List.getElem_mem]
      right
      assumption

instance Vec.decidableBAll (p : α → Prop) [DecidablePred p] :
    ∀ v : Vec α n, Decidable (∀ x, x ∈ v → p x) :=
  fun v ↦ (List.decidableBAll p v.toList)

instance (v : Vec (Node n m) m) (nod : Node n m) (j : Fin m) :
  Decidable (nod.low = node j ∨ nod.high = node j → nod.var < v[j].1) :=
  match nod with
  | ⟨nv, nl, nh⟩ =>
    match nl with
    | terminal _ =>
      match nh with
      | terminal _ => isTrue (fun contra ↦ match contra with
                            | .inl hh => by contradiction
                            | .inr hh => by contradiction)
      | node i => match decEq i j with
        | isFalse h => isTrue (fun contra ↦ match contra with
                                 | .inl hh => by contradiction
                                 | .inr hh => by injection hh; contradiction)
        | isTrue  h =>
          match Nat.decLt nv v[j].1 with
          | isFalse hh => isFalse (fun contra ↦ hh (contra (.inr (by simpa))))
          | isTrue  hh => isTrue (fun hhh ↦ hh)
    | node i => match decEq i j with
      | isFalse h => match nh with
        | terminal _ => isTrue (fun contra ↦ match contra with
                            | .inl hh => (by injection hh; contradiction)
                            | .inr hh => (by simp at hh))
        | node k => match decEq k j with
          | isFalse hhh => isTrue (fun contra ↦ match contra with
                                    | .inl hhhh => (by injection hhhh; contradiction)
                                    | .inr hhhh => (by injection hhhh; contradiction))
          | isTrue hhh => match Nat.decLt nv v[j].1 with
            | isFalse h5 => isFalse (fun contra ↦ h5 (contra (.inr (by simpa))))
            | isTrue h5 => isTrue (fun h6 ↦ (by simpa))
      | isTrue h => match Nat.decLt nv v[j].1 with
        | isFalse hh => isFalse (fun contra ↦ hh (contra (.inl (by simpa))))
        | isTrue hh => isTrue (fun hhh ↦ hh)

instance Node.RespectsOrder.instDecidable : Decidable (Node.RespectsOrder v nod) := by
  apply Nat.decidableForallFin

instance RespectsOrder.instDecidable {v : Vec (Node n m) m} : Decidable (Proper v) := by
  exact (Vec.decidableBAll (Node.RespectsOrder v) v)

def OBdd n m := { B : Bdd n m // Ordered B }

instance OBdd.instDecidableEq {n m} : DecidableEq (OBdd n m) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.eq_iff)

def OEdge {n m} (B C : OBdd n m) := B.1.heap = C.1.heap ∧ Edge B.1.heap B.1.root C.1.root

@[simp]
def OBdd.var {n m} (B : OBdd n m) : Nat := B.1.root.toVar B.1.heap

@[simp]
def OBdd.rav {n m} (B : OBdd n m) : Nat := n - B.var

/-- The `OEdge` relation between Ordered BDDs is well-founded. -/
theorem OEdge.wellFounded {n m} : @WellFounded (OBdd n m) OEdge := by
  have : Subrelation (@OEdge n m) (InvImage Nat.lt OBdd.var) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
    simp_all only [Ordered]
    rw [← h1] at h2
    let xs := x.toRelevantPointer
    let ys : x.RelevantPointer := ⟨y.root, Relation.ReflTransGen.tail Relation.ReflTransGen.refl h2⟩
    have h3 : GraphEdge x xs ys := h2
    apply hx at h3
    simp only [GraphMayPrecede, Bdd.toRelevantPointer, xs, ys] at h3
    simp only [InvImage, OBdd.var, Nat.succ_eq_add_one, Nat.lt_eq, Fin.val_fin_lt, gt_iff_lt, xs, ys]
    rcases hp : x.root
    case terminal => simp_all
    case node j => rcases hq : y.root <;> simp_all
  exact Subrelation.wf this (InvImage.wf _ (Nat.lt_wfRel.wf))

/-- The `OEdge` relation between Ordered BDDs is converse well-founded. -/
theorem OEdge.flip_wellFounded {n m} : @WellFounded (OBdd n m) (flip OEdge) := by
  have : Subrelation (flip (@OEdge n m)) (InvImage Nat.lt OBdd.rav) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
    simp_all only [Ordered]
    rw [← h1] at h2
    let ys := y.toRelevantPointer
    let xs : y.RelevantPointer := ⟨x.root, Relation.ReflTransGen.tail Relation.ReflTransGen.refl h2⟩
    have h3 : GraphEdge y ys xs := h2
    apply hy at h3
    simp only [GraphMayPrecede, Bdd.toRelevantPointer, xs, ys] at h3
    simp only [InvImage, OBdd.rav, OBdd.var, Nat.succ_eq_add_one, Nat.lt_eq, gt_iff_lt, xs, ys]
    rcases hp : y.root
    case terminal =>
      simp_all only [Ordered, MayPrecede, Nat.succ_eq_add_one, toVar_terminal_eq,
                     Fin.natCast_eq_last, Fin.val_last, Nat.sub_self, Nat.not_lt_zero, xs, ys]
      apply Fin.ne_last_of_lt at h3
      contradiction
    case node j => rcases hq : x.root <;> refine Nat.sub_lt_sub_left ?_ ?_ <;> simp_all
  exact Subrelation.wf this (InvImage.wf _ (Nat.lt_wfRel.wf))

instance OEdge.instWellFoundedRelation {n m} : WellFoundedRelation (OBdd n m) where
  rel := flip OEdge
  wf  := flip_wellFounded

inductive DecisionTree n where
  | leaf   : Bool → DecisionTree _
  | branch : Fin n → DecisionTree n → DecisionTree n → DecisionTree n
deriving DecidableEq

/-- All BDDs in the graph of an `Ordered` BDD are `Ordered`. -/
lemma ordered_of_relevant {n m} (O : OBdd n m) (S : O.1.RelevantPointer) :
    Ordered {heap := O.1.heap, root := S.1} := by
  rcases S with ⟨q, h⟩
  simp_all only [Ordered]
  rintro ⟨x, hx⟩ ⟨y, hy⟩ e
  simp_all only [Ordered, GraphEdge, GraphMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  have : GraphEdge O.1 ⟨x, (by exact Relation.ReflTransGen.trans h hx)⟩
                     ⟨y, (by exact Relation.ReflTransGen.trans h hy)⟩ := e
  apply O.2 at this
  exact this

/-- `Ordered` BDDs map into decision trees. -/
def OBdd.toTree {n m} (O : OBdd n m) : DecisionTree n := by
  rcases h : O.1.root
  case terminal b => exact .leaf b
  case node j =>
    let low : Bdd _ _ := {heap := O.1.heap, root := O.1.heap[j].low}
    have hlow : Ordered low :=
      ordered_of_relevant O ⟨O.1.heap[j].low, Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by rw [h]; exact (.low rfl))⟩
    have : flip OEdge ⟨low, hlow⟩ O := by   -- for termination checking
      simp only [flip, Ordered, Fin.getElem_fin, low]
      constructor <;> simp only [Ordered, low]
      rw [h]; exact Edge.low rfl
    let high : Bdd _ _ := {heap := O.1.heap, root := O.1.heap[j].high}
    have hhigh : Ordered high :=
      ordered_of_relevant O ⟨O.1.heap[j].high, Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by rw [h]; exact (.high rfl))⟩
    have : flip OEdge ⟨high, hhigh⟩ O := by -- for termination checking
      simp only [flip, Ordered, Fin.getElem_fin, high, low]
      constructor <;> simp only [Ordered, low, high]
      rw [h]; exact Edge.high rfl
    exact .branch O.1.heap[j].var (toTree ⟨low, hlow⟩ ) (toTree ⟨high, hhigh⟩ )
termination_by O

lemma OBdd.toTree_of_terminal {h : Bdd.Ordered { heap := v, root := terminal b }} :
    OBdd.toTree ⟨{heap := v, root := terminal b}, h⟩ = DecisionTree.leaf b := by simp [toTree]

def DecisionTree.evaluate {n} : DecisionTree n → Vec Bool n → Bool
  | leaf b, _ => b
  | branch j l h, v => if v[j] then h.evaluate v else l.evaluate v

def OBdd.evaluate {n m} : OBdd n m → Vec Bool n → Bool := DecisionTree.evaluate ∘ OBdd.toTree

@[simp]
def OBdd.Isomorphic {n m} : OBdd n m → OBdd n m → Prop := InvImage Eq OBdd.toTree

/-- Isomorphism of `Ordered` BDDs is decidable. -/
instance OBdd.instDecidableIsomorphic {n m} : DecidableRel (β := OBdd n m) OBdd.Isomorphic :=
  fun O U ↦ decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [InvImage])

def OBdd.GraphIsomorphic {n m} (O : OBdd n m) (l r : O.1.RelevantPointer) :=
  Isomorphic ⟨{heap := O.1.heap, root := l.1}, ordered_of_relevant O l⟩
             ⟨{heap := O.1.heap, root := r.1}, ordered_of_relevant O r⟩

instance OBdd.instDecidableGraphIsomorphic : Decidable (OBdd.GraphIsomorphic O l r) := by
  simp only [OBdd.GraphIsomorphic]; infer_instance

/-- Isomorphism of `Ordered` BDDs is an equivalence relation. -/
def OBdd.Isomorphic.instEquivalence {n m} : Equivalence (α := OBdd n m) OBdd.Isomorphic := by
  apply InvImage.equivalence
  constructor <;> simp_all

instance OBdd.Isomorphic.instReflexive : Reflexive (α := OBdd n m) OBdd.Isomorphic := instEquivalence.refl

instance OBdd.Isomorphic.instSymmetric : Symmetric (α := OBdd n m) OBdd.Isomorphic := fun _ _ ↦ instEquivalence.symm

instance OBdd.Isomorphic.instTransitive : Transitive (α := OBdd n m) OBdd.Isomorphic := fun _ _ _ ↦ instEquivalence.trans

/-- A pointer is redundant if it point to node `N` with `N.low = N.high`. -/
inductive Pointer.Redundant {n m} (w : Vec (Node n m) m) : Pointer m → Prop where
  | intro : w[j].low = w[j].high → Redundant w (node j)

instance Pointer.Redundant.instDecidable {n m} (w : Vec (Node n m) m) : DecidablePred (Redundant w) := by
  intro p
  cases p
  case terminal => apply isFalse; intro; contradiction
  case node j =>
    cases decEq w[j].low w[j].high
    case isFalse => apply isFalse; intro contra; cases contra; contradiction
    case isTrue h => exact isTrue (intro h)

def Bdd.NoRedundancy {n m} (B : Bdd n m) : Prop := ∀ (p : B.RelevantPointer), ¬ Redundant B.heap p.1

def RProper {n m} (v : Vec (Node n m) m) := (∀ nod ∈ v, nod.low ≠ nod.high)

instance RProper.instDecidable {v : Vec (Node n m) m} : Decidable (RProper v) := by
  exact (Vec.decidableBAll _ v)

theorem NoRedundancy_of_RProper {n m} (v : Vec (Node n m) m) {p} : RProper v → ({heap := v, root := p} : Bdd n m).NoRedundancy := by
  intro h
  intro q contra
  rcases q with ⟨q, hq⟩
  cases contra
  case intro j c =>
    apply h at c
    · assumption
    · simp_all [Vec.instMembership, List.Vector.getElem_def]

/-- A BDD is `Reduced` if its graph does not contain redundant nodes or distinct isomorphic subgraphs. -/
@[simp]
def OBdd.Reduced {n m} (O : OBdd n m) : Prop
  -- No redundant nodes.
  := NoRedundancy O.1
  -- Isomorphism implies pointer-equality.
   ∧ Subrelation (GraphIsomorphic O) (InvImage Eq Subtype.val)

lemma transGen_iff_single_and_reflTransGen : (Relation.TransGen r a b) ↔ ∃ c, r a c ∧ Relation.ReflTransGen r c b := by
  constructor
  case mp =>
    intro h
    apply Relation.transGen_swap.mp at h
    induction h
    case single c e => use b
    case tail a' b' c e ih =>
      use a'
      constructor
      assumption
      rcases ih with ⟨z, h1, h2⟩
      apply Relation.reflTransGen_swap.mp at h2
      apply Relation.reflTransGen_swap.mp
      apply Relation.ReflTransGen.tail h2 h1
  case mpr =>
    rintro ⟨z, h1, h2⟩
    induction h2
    case refl => exact Relation.TransGen.single h1
    case tail a' b' t e ih => exact Relation.TransGen.tail ih e

@[simp]
def RelevantPointer.var {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := p.1.toVar B.heap

@[simp]
def RelevantPointer.gap {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := n - (RelevantPointer.var p)

theorem GraphEdge.flip_wellFounded (o : Ordered B) : WellFounded (flip (GraphEdge B)) := by
  have : Subrelation (flip (GraphEdge B)) (InvImage Nat.lt RelevantPointer.gap) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ e
    simp_all only [InvImage, flip, RelevantPointer.gap]
    refine Nat.sub_lt_sub_left ?_ ?_
    cases e <;> simp
    exact o e
  exact Subrelation.wf this (InvImage.wf _ (Nat.lt_wfRel.wf))

instance GraphEdge.instWellFoundedRelation {n m} (O : OBdd n m) : WellFoundedRelation O.1.RelevantPointer where
  rel := flip O.1.GraphEdge
  wf  := (GraphEdge.flip_wellFounded O.2)

instance OBdd.instDecidableReflTransGen {n m} (O : OBdd n m) (p : O.1.RelevantPointer) (q) :
    Decidable (Relation.ReflTransGen (Edge O.1.heap) p.1 q) := by
  convert decidable_of_iff _ (symm Relation.reflTransGen_iff_eq_or_transGen)
  convert instDecidableOr
  · exact decEq q p.1
  · convert decidable_of_iff _ (symm transGen_iff_single_and_reflTransGen)
    rcases h : p.1
    case terminal =>
      apply isFalse
      rintro ⟨x, contra1, contra2⟩
      contradiction
    case node j =>
      let low := O.1.heap[j].low
      have hlow : Relation.ReflTransGen (Edge O.1.heap) O.1.root low :=
        Relation.ReflTransGen.tail p.2 (by rw [h]; exact Edge.low rfl)
      cases OBdd.instDecidableReflTransGen O ⟨low, hlow⟩ q
      case isFalse hfl =>
        let high := O.1.heap[j].high
        have hhigh : Relation.ReflTransGen (Edge O.1.heap) O.1.root high :=
          Relation.ReflTransGen.tail p.2 (by rw [h]; exact Edge.high rfl)
        cases OBdd.instDecidableReflTransGen O ⟨high, hhigh⟩ q
        case isFalse hfh =>
          apply isFalse
          rintro ⟨c, contra1, contra2⟩
          simp_all only [Ordered]
          cases contra1
          case low contra =>
            apply hfl
            apply Relation.reflTransGen_swap.mp
            apply Relation.ReflTransGen.tail
            apply Relation.reflTransGen_swap.mpr
            exact contra2
            simp_all only [Ordered, not_true_eq_false, low]
          case high contra =>
            apply hfh
            apply Relation.reflTransGen_swap.mp
            apply Relation.ReflTransGen.tail
            apply Relation.reflTransGen_swap.mpr
            exact contra2
            simp_all only [Ordered, not_true_eq_false, low, high]
        case isTrue hth =>
          apply isTrue
          use high
          constructor
          · simp only [Ordered, low, high, Edge.high rfl]
          · apply hth
      case isTrue hth =>
        apply isTrue
        use low
        constructor
        · simp only [Ordered, low, Edge.low rfl]
        · apply hth
termination_by p
decreasing_by
  all_goals simp_all only [Ordered, flip, GraphEdge, Fin.getElem_fin, Edge.low, Edge.high]

instance Pointer.instDecidableReachable {n m} (O : OBdd n m) :
    DecidablePred (Reachable O.1.heap O.1.root) :=
  OBdd.instDecidableReflTransGen O ⟨O.1.root, Relation.ReflTransGen.refl⟩

instance OBdd.instFintypeRelevantPointer {n m} (O : OBdd n m) : Fintype (O.1.RelevantPointer) := by
  convert Subtype.fintype _ <;> infer_instance

/-- The inverse image of a decidable relation is decidable. -/
instance my_decidableRel_of_invImage2 {r : β → β → Prop} [DecidableRel r] {f : α → β} :
    DecidableRel (InvImage r f) :=
  fun a b ↦ decidable_of_decidable_of_iff (show (r (f a) (f b)) ↔ _ by simp [InvImage])

/-- `Reduced` is decidable. -/
instance OBdd.instReducedDecidable {n m} : DecidablePred (α := OBdd n m) Reduced :=
  fun _ ↦ (instDecidableAnd (dp := Fintype.decidableForallFintype) (dq := Fintype.decidableForallFintype))

def example_bdd : OBdd 3 4 :=
  ⟨ { heap := ⟨[{var := 0, low := node 1, high := node 2},
                 {var := 1, low := terminal false, high := node 3},
                 {var := 1, low := node 3, high := terminal true},
                 {var := 2, low := terminal false, high := terminal true}], rfl⟩
      root := node 0 },
    by apply Ordered_of_Proper; decide⟩

example : example_bdd.Reduced := by decide (config := {kernel := true})

/-- The output of equal constant functions with inhabited domain is equal. -/
lemma eq_of_constant_eq {α β} {c c' : β} [Inhabited α] :
    Function.const α c = Function.const α c' → c = c' :=
  fun h ↦ (show (Function.const α c) default = (Function.const α c') default by rw [h])

instance Vec.instInhabited {n} [Inhabited α] : Inhabited (Vec α n) :=
  match n with
  | Nat.zero => ⟨[], rfl⟩
  | Nat.succ m => ⟨default :: (default : Vec α m).1, (by simp)⟩

lemma Bdd.terminal_or_node {n m} (B : Bdd n m) :
    (∃ b, (B.root = terminal b ∧ B = {heap := B.heap, root := terminal b}))
  ∨ (∃ j, (B.root = node j ∧ B = {heap := B.heap, root := node j})) := by
  cases h : B.root
  case terminal b => left;  use b; simp [← h]
  case node j => right; use j; simp [← h]

theorem OBdd.init_inductionOn t {motive : OBdd n m → Prop}
    (base :  (b : Bool) → motive ⟨{heap := t.1.heap, root := terminal b}, Ordered_of_terminal⟩)
    (step :  (j : Fin m) →
            (hl : ({heap := t.1.heap, root := t.1.heap[j].low} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := t.1.heap[j].low}, hl⟩ →
            (hh : ({heap := t.1.heap, root := t.1.heap[j].high} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := t.1.heap[j].high}, hh⟩ →
            (h : ({heap := t.1.heap, root := node j} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := node j}, h⟩)
    : motive t := by
  rcases (terminal_or_node t.1) with ⟨b, h1, h2⟩ | ⟨j, h1, h2⟩
  case inl => convert base b; apply Subtype.eq_iff.mpr; assumption
  case inr =>
    convert step j _ _ _ _ _
    · apply Subtype.eq_iff.mpr; assumption; exact ordered_of_relevant t ⟨node j, by simp only [Reachable]; rw [← h1]⟩
    · exact ordered_of_relevant t ⟨t.1.heap[j].low, by rw [h1]; exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Edge.low rfl)⟩
    · exact OBdd.init_inductionOn _ base step
    · exact ordered_of_relevant t ⟨t.1.heap[j].high, by rw [h1]; exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Edge.high rfl)⟩
    · exact OBdd.init_inductionOn _ base step
termination_by t
decreasing_by
  · constructor
    · simp
    · convert Edge.low rfl
  · simp only [flip, Ordered, Fin.getElem_fin, OEdge, true_and]; convert Edge.high rfl

def OBdd.isTerminal {n m} (O : OBdd n m) := ∃ b, O.1.root = terminal b

/-- The graph induced by a terminal BDD consists of a sole terminal pointer. -/
lemma Bdd.terminal_relevant_iff {n m} {B : Bdd n m} (h : B.root = terminal b) (S : B.RelevantPointer) {motive : Pointer m → Prop} :
    motive S.1 ↔ motive (terminal b) := by
  rw [← h]
  rcases S with ⟨s, hs⟩
  cases (Relation.reflTransGen_swap.mpr hs)
  case refl        => simp
  case tail contra => rw [h] at contra; contradiction

lemma Bdd.eq_terminal_of_relevant {n m} {v : Vec (Node n m) m} {B : Bdd n m} (h : B = {heap := v, root := terminal b}) (S : B.RelevantPointer) :
    S.1 = terminal b :=
  (terminal_relevant_iff (by simp [h]) S).mp rfl

/-- Terminal BDDs are reduced. -/
lemma OBdd.reduced_of_terminal {n m} (O : OBdd n m) : O.isTerminal → O.Reduced := by
  rintro ⟨b, h⟩
  constructor
  · intro p R
    have contra : Redundant O.1.heap (terminal b) := by apply (terminal_relevant_iff h p).mp R
    contradiction
  · intro p q _
    calc p.1
      _ = terminal b :=         (eq_terminal_of_relevant (by rw [← h]) p)
      _ = q.1    := Eq.symm (eq_terminal_of_relevant (by rw [← h]) q)

/-- Sub-BDDs of a reduced BDD are reduced. -/
lemma OBdd.reduced_of_relevant {n m} (O : OBdd n m) (S : O.1.RelevantPointer) {h} :
    O.Reduced → OBdd.Reduced ⟨{heap := O.1.heap, root := S.1}, h⟩ := by
  intro R
  induction O using OBdd.init_inductionOn
  case base b =>
    apply OBdd.reduced_of_terminal
    simp only [isTerminal, Ordered]
    use b
    apply eq_terminal_of_relevant rfl
  case step j _ _ _ _ o =>
    constructor
    · intro p; apply R.1 ⟨p.1, Relation.transitive_reflTransGen S.2 p.2⟩
    · intro q p _
      have : GraphIsomorphic ⟨{ heap := O.1.heap, root := node j }, o⟩
              ⟨q.1, Relation.transitive_reflTransGen S.2 q.2⟩
              ⟨p.1, Relation.transitive_reflTransGen S.2 p.2⟩ := by
        simp_all only [GraphIsomorphic, Isomorphic, InvImage]
      apply R.2 this


-- Experiments towards canonicity follow.

theorem OBdd.Canonicity1 {O U : OBdd n m} : O.Reduced → U.Reduced → O.evaluate = U.evaluate → O.Isomorphic U := by
  intro OR UR h
  rcases O with ⟨B, OB⟩
  rcases U with ⟨C, OC⟩
  simp_all only [Reduced, Ordered, evaluate, Function.comp_apply, Isomorphic, InvImage]
  cases p : B.root
  case terminal b =>
    have this : ({heap := B.heap, root := terminal b} : Bdd n m).Ordered := by rw [← p]; assumption
    have foo : toTree ⟨B, OB⟩ = DecisionTree.leaf b := by
      calc toTree ⟨B, OB⟩
        _ = toTree ⟨{heap := B.heap, root := terminal b}, this⟩ := by simp_all only [← p]
        _ = DecisionTree.leaf b := OBdd.toTree_of_terminal
    cases q : C.root
    case terminal c =>
      have that : ({heap := C.heap, root := terminal c} : Bdd n m).Ordered := by rw [← q]; assumption
      have bar : toTree ⟨C, OC⟩ = DecisionTree.leaf c := by
        calc toTree ⟨C, OC⟩
          _ = toTree ⟨{heap := C.heap, root := terminal c}, that⟩ := by simp_all only [← q]
          _ = DecisionTree.leaf c := OBdd.toTree_of_terminal
      rw [foo, bar] at h
      simp_all only [Ordered, DecisionTree.evaluate, DecisionTree.leaf.injEq]
      exact eq_of_constant_eq h
    case node j =>
      have that : ({heap := C.heap, root := node j} : Bdd n m).Ordered := by rw [← q]; assumption
      have bar : toTree ⟨C, OC⟩ = toTree ⟨{heap := C.heap, root := node j}, that⟩ := by
        calc toTree ⟨C, OC⟩
          _ = toTree ⟨{heap := C.heap, root := node j}, that⟩ := by simp_all only [← q]
      rw [foo] at h
      simp_all only [DecisionTree.evaluate, Ordered]
      unfold toTree at h
      simp_all only [DecisionTree.evaluate, Fin.getElem_fin, Ordered]
      -- We need a lemma that shows that h is a contradiction since C is reduced.
      -- Idea: show that the two sub-bdds evaluate to the same function, so they
      -- are isomorphic (by recursion), contradicting C.Reduced.
      have contra {h1 : ({ heap := C.heap, root := C.heap[j.1].low } : Bdd n m).Ordered} {h2 : ({ heap := C.heap, root := C.heap[j.1].high } : Bdd n m).Ordered} :
          (toTree ⟨{ heap := C.heap, root := C.heap[j.1].low }, h1⟩).evaluate = (toTree ⟨{ heap := C.heap, root := C.heap[j.1].high }, h2⟩).evaluate := by
        sorry
      -- Now recursively apply Canonicity to contra to obtain a proof of isomorphism between the two sub-bdds...
      sorry
  case node i => sorry

lemma terminal_of_constant {n m} (O : OBdd n m) : O.Reduced → (∃ b, (O.evaluate = fun _ ↦ b)) → O.isTerminal := by
  rintro R ⟨b, hb⟩
  induction O using OBdd.init_inductionOn
  case base b' => use b'
  case step j lo hl ho hh U =>
    exfalso
    sorry

lemma OBdd.toTree_respects_Isomorphism {n m} (O U : OBdd n m) (h : OBdd.Isomorphic O U) : O.toTree = U.toTree := by simpa [OBdd.Isomorphic, InvImage]

instance OBdd.instSetoid : Setoid (OBdd n m) := ⟨OBdd.Isomorphic, OBdd.Isomorphic.instEquivalence⟩

def AbstractBdd {n m} := @Quotient (OBdd n m) (by infer_instance)

theorem OBdd.Canonicity2 {O U : OBdd n m} : O.Reduced → U.Reduced → O.evaluate = U.evaluate → O ≈ U := by
  intro h1 h2 h3
  induction O using init_inductionOn
  case base b =>
    induction U using init_inductionOn
    case base c =>
      simp only [HasEquiv.Equiv, instSetoid, Isomorphic, InvImage, toTree]
      congr
      simp only [evaluate, Function.comp, toTree, DecisionTree.evaluate] at h3
      exact eq_of_constant_eq h3
    case step i => sorry
  case step j =>
    induction U using init_inductionOn with
    | base b => sorry
    | step i hl _ hh _ h => sorry
