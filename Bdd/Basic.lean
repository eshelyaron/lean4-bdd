import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Basic
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Vector
open List renaming Vector → Vec

instance {α : Type u} [ToString α] : ToString (Vec α k) := ⟨fun v ↦ v.1.toString⟩

/-- Pointer to a BDD node or terminal -/
inductive Pointer m where
  | terminal : Bool  → Pointer _
  | node : Fin m → Pointer m
deriving Fintype, DecidableEq, Repr

instance Pointer.instToString : ToString (Pointer m) := ⟨fun p =>
  match p with
  | .terminal true => "⊤"
  | .terminal false => "⊥"
  | .node j => "→" ++ toString j⟩

inductive Pointer.le : Pointer m → Pointer m → Prop where
  | terminal_le_terminal : b ≤ c → le (terminal b) (terminal c)
  | terminal_le_node : le (terminal b) (node j)
  | node_le_node : j ≤ i → le (node j) (node i)

instance Pointer.instLE : LE (Pointer m) := {le := Pointer.le}

instance Pointer.instDecidableLe : DecidableLE (Pointer m) :=
  fun p q ↦ match p with
  | terminal b => match q with
    | terminal c => match Bool.instDecidableLe b c with
      | isTrue ht => isTrue  (.terminal_le_terminal ht)
      | isFalse hf => isFalse (by intro contra; cases contra; contradiction)
    | node i => isTrue (.terminal_le_node)
  | node j => match q with
    | terminal c => isFalse (by intro contra; contradiction)
    | node i => match Fin.decLe j i with
      | isTrue ht => isTrue (.node_le_node ht)
      | isFalse hf => isFalse (by intro contra; cases contra; contradiction)

open Pointer

/-- BDD node -/
structure Node (n) (m) where
  var  : Fin n
  low  : Pointer m
  high : Pointer m
deriving DecidableEq, Repr

instance Node.instToString : ToString (Node n m) := ⟨fun N => "⟨" ++ (toString N.var) ++ ", " ++ (toString N.low) ++ ", " ++ (toString N.high) ++ "⟩"⟩

/-- Raw BDD -/
structure Bdd (n) (m) where
  heap : Vec (Node n m) m
  root : Pointer m
deriving DecidableEq

instance Bdd.instToString : ToString (Bdd n m) := ⟨fun B => "⟨" ++ (toString B.heap) ++ ", " ++ (toString B.root)  ++ "⟩"⟩

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

@[trans]
theorem Pointer.Reachable.trans (hab : Reachable v a b) (hbc : Reachable v b c) : Reachable v a c := Relation.ReflTransGen.trans hab hbc

/-- `B.RelevantPointer` is the subtype of pointers reachable from `B.root`. -/
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

lemma Bdd.Ordered_of_terminal' {n m} {B : Bdd n m} {b} : B.root = terminal b → B.Ordered := by
  intro h
  have : B = {heap := B.heap, root := B.root} := rfl
  have : B = {heap := B.heap, root := terminal b} := by rw [this, h]
  rw [this]
  apply Ordered_of_terminal

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
def Bdd.var {n m} (B : Bdd n m) : Fin n.succ := B.root.toVar B.heap

@[simp]
def OBdd.var {n m} (O : OBdd n m) : Nat := O.1.var

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
    case terminal => simp_all only [Ordered, MayPrecede, Nat.succ_eq_add_one, toVar_terminal_eq, Fin.natCast_eq_last, var, Fin.val_last, ys, xs]
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
    (base : (b : Bool) → motive ⟨{heap := t.1.heap, root := terminal b}, Ordered_of_terminal⟩)
    (step : (j : Fin m) →
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

/-- `f.independentOf i` if the output of `f` does not depend on the value of the `i`th input. -/
def independentOf (f : Vec α n → β) (i : Fin n) := ∀ a, ∀ x, f x = f (Vec.set x i a)

def dependentOn (f : Vec α n → β) (i : Fin n) := ¬ independentOf f i

instance instDecidableIndependentOf' [Fintype α] (f : Vec α n → β) : DecidablePred (fun a ↦ ∀ (x : List.Vector α n), f x = f (x.set i a)) := by
  intro a
  simp
  exact Fintype.decidableForallFintype

instance instDecidableIndependentOf [Fintype α] [DecidableEq β] (f : Vec α n → β) : Decidable (independentOf f i) :=
  Fintype.decidableForallFintype

instance instDecidableDependentOn [Fintype α] [DecidableEq β] (f : Vec α n → β) : Decidable (dependentOn f i) := instDecidableNot

def minDep [Fintype α] [DecidableEq β] (f : Vec α n → β) : Fin n.succ :=
  match Fin.find (dependentOn f) with
  | none => n
  | some i => i

lemma minDep_spec [Fintype α] [DecidableEq β] (f : Vec α n → β) (h : (minDep f) ≠ Fin.last n) : dependentOn f (Fin.castPred (minDep f) h) := by
  cases hh : Fin.find (dependentOn f)
  case none =>
    simp [minDep] at h
    simp_rw [hh] at h
    contradiction
  case some j =>
    simp [minDep]
    simp_rw [hh]
    apply Fin.find_spec
    simp_rw [hh]
    simp

lemma OBdd.reachable_of_edge : Edge w p q → Reachable w p q := Relation.ReflTransGen.tail Relation.ReflTransGen.refl
lemma OBdd.ordered_of_edge {O : OBdd n m} {h : O.1.heap = v} {r : O.1.root = q} (p) : Edge v q p → Bdd.Ordered {heap := v, root := p} := by
  rw [← h]
  rw [← r]
  intro e
  exact ordered_of_relevant O ⟨p, reachable_of_edge e⟩

lemma OBdd.ordered_of_low_edge : Bdd.Ordered {heap := v, root := node j} → Bdd.Ordered {heap := v, root := v[j].low} := by
  intro o x y h
  apply ordered_of_relevant ⟨{ heap := v, root := node j }, o⟩ ⟨v[j].low, (reachable_of_edge (Edge.low rfl))⟩
  simpa

lemma OBdd.ordered_of_high_edge : Bdd.Ordered {heap := v, root := node j} → Bdd.Ordered {heap := v, root := v[j].high} := by
  intro o x y h
  apply ordered_of_relevant ⟨{ heap := v, root := node j }, o⟩ ⟨v[j].high, (reachable_of_edge (Edge.high rfl))⟩
  simpa

/-- Spell out `OBdd.evaluate` for non-terminals. -/
@[simp]
lemma OBdd.evaluate_node {n m} {v : Vec (Node n m) m} {I : Vec Bool n} {j : Fin m} {h} : OBdd.evaluate ⟨{ heap := v, root := node j }, h⟩ I =
    if I[v[j].var]
    then OBdd.evaluate ⟨{ heap := v, root := v[j].high }, ordered_of_high_edge h⟩ I
    else OBdd.evaluate ⟨{ heap := v, root := v[j].low }, ordered_of_low_edge h⟩ I := by
    -- else OBdd.evaluate ⟨{ heap := v, root := v[j].low }, ordered_of_low_edge ordered_of_relevant ⟨{ heap := v, root := node j }, h⟩ ⟨v[j].low, (reachable_of_edge (Edge.low rfl))⟩⟩ I := by
      conv =>
        lhs
        simp only [OBdd.evaluate, Function.comp_apply]
        unfold OBdd.toTree
        simp only [Fin.getElem_fin, Ordered, DecisionTree.evaluate]
      rfl

lemma OBdd.evaluate_node' {n m} {v : Vec (Node n m) m} {j : Fin m} {h} : OBdd.evaluate ⟨{ heap := v, root := node j }, h⟩ = fun I ↦
    if I[v[j].var]
    then OBdd.evaluate ⟨{ heap := v, root := v[j].high }, ordered_of_high_edge h⟩ I
    else OBdd.evaluate ⟨{ heap := v, root := v[j].low }, ordered_of_low_edge h⟩ I := by
      conv =>
        lhs
        simp only [OBdd.evaluate, Function.comp_apply]
        unfold OBdd.toTree
        simp only [Fin.getElem_fin, Ordered, DecisionTree.evaluate]
      rfl

/-- Spell out `OBdd.evaluate` for terminals. -/
@[simp]
lemma OBdd.evaluate_terminal {n m} {v : Vec (Node n m) m} {h} : OBdd.evaluate ⟨{ heap := v, root := terminal b }, h⟩ = Function.const _ b := by
  simp only [evaluate, Function.comp_apply, toTree, DecisionTree.evaluate]
  rfl

lemma OBdd.evaluate_terminal' {n m} {O : OBdd n m} : O.1.root = terminal b → O.evaluate = Function.const _ b := by
  intro h
  rcases O with ⟨⟨heap, root⟩, ho⟩
  simp_all

@[simp]
lemma OBdd.toTree_terminal {n m} {v : Vec (Node n m) m} {h} : OBdd.toTree ⟨{ heap := v, root := terminal b }, h⟩ = .leaf b := by simp [toTree]

lemma OBdd.toTree_terminal' {n m} {O : OBdd n m} : O.1.root = terminal b → O.toTree = .leaf b := by
  intro h
  rcases O with ⟨⟨heap, root⟩, ho⟩
  simp_all [toTree]

lemma OBdd.toTree_node' {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.toTree = .branch O.1.heap[j].var (toTree ⟨{heap := O.1.heap, root := O.1.heap[j].low }, ordered_of_low_edge (by rw [← h]; exact O.2)⟩ ) (toTree ⟨{heap := O.1.heap, root := O.1.heap[j].high }, ordered_of_high_edge (by rw [← h]; exact O.2)⟩) := by
  rcases O with ⟨⟨heap, root⟩, ho⟩
  simp at h
  simp_rw [h]
  conv =>
    lhs
    unfold toTree

private lemma aux {O : OBdd n m} {i : Fin m} :
    O.1.heap[i.1].var = Fin.castPred (toVar O.1.heap (node i)) (Fin.exists_castSucc_eq.mp ⟨O.1.heap[i.1].var, by simp⟩) :=
  by simp

/-- Ordered BDDs denote functions that are independent of any variable below the root variable. -/
lemma OBdd.Independence {O : OBdd n m} (j : Fin (O.1.root.toVar O.1.heap)) :
    independentOf (OBdd.evaluate O) ⟨j.1, (Fin.val_lt_of_le j (Fin.is_le _))⟩ := by
  induction O using OBdd.init_inductionOn with
  | base b =>
    simp only [OBdd.evaluate, Ordered, Function.comp_apply, OBdd.toTree, DecisionTree.evaluate, Nat.succ_eq_add_one, toVar_terminal_eq, Fin.val_natCast]
    intro a v
    rfl
  | step i hl ihl hh ihh h =>
    intro b I
    rw [OBdd.evaluate_node]
    rw [OBdd.evaluate_node]
    have : (I.set ⟨j.1, by rcases j with ⟨jj, jh⟩; simp at jh; apply Nat.lt_trans jh; simp⟩ b)[O.1.heap[i].var] = I[O.1.heap[i].var] := by
      apply List.Vector.get_set_of_ne
      apply ne_of_lt
      rcases j with ⟨jj, jh⟩
      simp only [Ordered, Fin.getElem_fin, Fin.eta]
      simp only [Nat.succ_eq_add_one, Ordered, toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc, Fin.coe_castSucc] at jh
      assumption
    rw [this]
    congr 1
    · apply ihh ⟨j.1, _⟩
      apply Nat.lt_trans (m := O.1.heap[i].var)
      rcases j with ⟨jj, jh⟩
      · simp only [Nat.succ_eq_add_one, Ordered, toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc, Fin.coe_castSucc] at jh; assumption
      · simp only [Ordered, Fin.getElem_fin, Nat.succ_eq_add_one]
        rw [aux]
        have xua : (toVar O.1.heap (node i)) < (toVar O.1.heap O.1.heap[↑i].high) := by
          have hyp := h (show Bdd.GraphEdge { heap := O.1.heap, root := node i } ⟨(node i), Relation.ReflTransGen.refl⟩ ⟨O.1.heap[↑i].high, (Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Edge.high rfl))⟩ by exact (Edge.high rfl))
          assumption
        aesop
    · apply ihl ⟨j.1, _⟩
      apply Nat.lt_trans (m := O.1.heap[i].var)
      rcases j with ⟨jj, jh⟩
      · simp only [Nat.succ_eq_add_one, Ordered, toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc, Fin.coe_castSucc] at jh; assumption
      · simp only [Ordered, Fin.getElem_fin, Nat.succ_eq_add_one]
        rw [aux]
        have xua : (toVar O.1.heap (node i)) < (toVar O.1.heap O.1.heap[↑i].low) := by
          have hyp := h (show Bdd.GraphEdge { heap := O.1.heap, root := node i } ⟨(node i), Relation.ReflTransGen.refl⟩ ⟨O.1.heap[↑i].low, (Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Edge.low rfl))⟩ by exact (Edge.low rfl))
          assumption
        aesop

lemma OBdd.Independence' {O : OBdd n m} (j : Fin O.var) : independentOf (OBdd.evaluate O) ⟨j.1, (Fin.val_lt_of_le j (Fin.is_le _))⟩ := Independence j

lemma OBdd.toTree_respects_Isomorphism {n m} (O U : OBdd n m) (h : OBdd.Isomorphic O U) : O.toTree = U.toTree := by simpa [OBdd.Isomorphic, InvImage]

instance OBdd.instSetoid : Setoid (OBdd n m) := ⟨OBdd.Isomorphic, OBdd.Isomorphic.instEquivalence⟩

def AbstractBdd {n m} := @Quotient (OBdd n m) (by infer_instance)

lemma Vec.get_set_same' (v : Vec α n) (i : Fin n) (a : α) : (v.set i a)[i] = a := by
  cases v; cases i
  simp [Fin.getElem_fin, List.Vector.getElem_def, List.Vector.toList_set, List.getElem_set_self]

def DecisionTree.size {n} : DecisionTree n → Nat
  | leaf _ => 0
  | branch _ l h => 1 + l.size + h.size

def OBdd.size {n m} : OBdd n m → Nat := DecisionTree.size ∘ OBdd.toTree

lemma OBdd.size_zero_of_terminal : OBdd.isTerminal O → O.size = 0 := by
  rintro ⟨b, h⟩
  rcases O with ⟨⟨heap, root⟩, o⟩
  subst h
  simp only [size, Ordered, Function.comp_apply]
  unfold toTree
  rfl

def Bdd.low {n m} (B : Bdd n m) {j : Fin m} : B.root = node j → Bdd n m :=
  fun _ ↦ {heap := B.heap, root := B.heap[j].low}

lemma Bdd.edge_of_low {n m} (B : Bdd n m) {j : Fin m} {h : B.root = node j} : Edge B.heap B.root (B.low h).root := by
  simp [low, h]
  exact Edge.low rfl

def Bdd.high {n m} (B : Bdd n m) {j : Fin m} : B.root = node j → Bdd n m :=
  fun _ ↦ {heap := B.heap, root := B.heap[j].high}

lemma Bdd.edge_of_high {n m} (B : Bdd n m) {j : Fin m} {h : B.root = node j} : Edge B.heap B.root (B.high h).root := by
  simp [high, h]
  exact Edge.high rfl

lemma Bdd.reachable_of_edge : Edge w p q → Reachable w p q := Relation.ReflTransGen.tail Relation.ReflTransGen.refl

lemma Bdd.ordered_of_relevant' {B : Bdd n m} {h : B.heap = v} {r : B.root = q} : B.Ordered → Reachable v q p → Bdd.Ordered {heap := v, root := p} := by
  intro o r_q_p
  simp_all only [Ordered]
  rintro ⟨x, hx⟩ ⟨y, hy⟩ e
  simp_all only [Ordered, GraphEdge, GraphMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  simp at hx
  simp at hy
  have : GraphEdge B ⟨x, (by trans p <;> aesop)⟩
                     ⟨y, (by trans p <;> aesop)⟩ := by
    simp only [GraphEdge]
    rw [h]
    assumption
  apply o at this
  rw [← h]
  exact this

lemma Bdd.ordered_of_edge {B : Bdd n m} {h : B.heap = v} {r : B.root = q} : B.Ordered → Edge v q p → Bdd.Ordered {heap := v, root := p} := by
  rw [← h]
  rw [← r]
  intro o e
  apply ordered_of_relevant' o
  apply reachable_of_edge e
  rfl
  rfl

lemma Bdd.high_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.high h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge
  rfl
  exact h
  exact o
  convert edge_of_high B
  · symm; assumption
  · assumption

def OBdd.high {n m} (O : OBdd n m) {j : Fin m} : O.1.root = node j → OBdd n m :=
  fun h ↦ ⟨O.1.high h, Bdd.high_ordered h O.2⟩

lemma OBdd.high_reduced {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced → (O.high h).Reduced := by
  intro o
  apply reduced_of_relevant O ⟨O.1.heap[j].high, ?_⟩ o
  apply reachable_of_edge
  rw [h]
  exact Edge.high rfl

lemma Bdd.low_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.low h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge
  rfl
  exact h
  exact o
  convert edge_of_low B
  · symm; assumption
  · assumption

def OBdd.low {n m} (O : OBdd n m) {j : Fin m} : O.1.root = node j → OBdd n m :=
  fun h ↦ ⟨O.1.low h, Bdd.low_ordered h O.2⟩

lemma OBdd.low_reduced {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced → (O.low h).Reduced := by
  intro o
  apply reduced_of_relevant O ⟨O.1.heap[j].low, ?_⟩ o
  apply reachable_of_edge
  rw [h]
  exact Edge.low rfl

lemma OBdd.toTree_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.toTree = .branch O.1.heap[j].var (toTree (O.low h)) (toTree (O.high h)) := by
  rcases O with ⟨⟨heap, root⟩, ho⟩
  simp at h
  simp_rw [h]
  conv =>
    lhs
    unfold toTree
  simp [low,high]
  constructor <;> rfl

lemma OBdd.size_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.size = 1 + (O.low h).size + (O.high h).size := by
  simp [size]
  rw [toTree_node h]
  rfl

lemma OBdd.evaluate_node'' {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    O.evaluate = fun I ↦ if I[O.1.heap[j].var] then (O.high h).evaluate I else (O.low h).evaluate I := by
  simp only [evaluate, Function.comp_apply]
  rw [toTree_node h]
  simp [DecisionTree.evaluate]

lemma OBdd.var_lt_high_var {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.var < (O.high h).var := by
  have e := Bdd.edge_of_high (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.high h).1.root, reachable_of_edge e⟩ e

lemma OBdd.var_lt_low_var  {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.var < (O.low  h).var := by
  have e := Bdd.edge_of_low (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.low h).1.root, reachable_of_edge e⟩ e

lemma OBdd.evaluate_high_eq_evaluate_low_of_independentOf_root {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    independentOf O.evaluate O.1.heap[j].var → (O.high h).evaluate = (O.low h).evaluate := by
  intro i
  ext I
  trans O.evaluate I
  · rw [i true I]
    rw [evaluate_node'' h]
    simp only [Vec.get_set_same']
    exact (Independence' (O := O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); simp; rw [h]; simp)⟩) true I
  · rw [i false I]
    rw [evaluate_node'' h]
    simp only [Vec.get_set_same']
    symm
    exact (Independence' (O := O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var  (O := O); simp; rw [h]; simp)⟩) false I

lemma OBdd.evaluate_high_eq_evaluate_set_true {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.high h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var true := by
  ext I
  simp only [Function.comp_apply]
  nth_rw 2 [evaluate_node'' (j := j)]
  beta_reduce
  rw [Vec.get_set_same']
  simp only [↓reduceIte]
  have := var_lt_high_var (h := h)
  simp [var] at this
  rw [h] at this
  simp at this
  apply Independence (O := (O.high h)) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); simp; rw [h]; simp)⟩

lemma OBdd.evaluate_low_eq_evaluate_set_false {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.low h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var false := by
  ext I
  simp only [Function.comp_apply]
  nth_rw 2 [evaluate_node'' (j := j)]
  beta_reduce
  rw [Vec.get_set_same']
  simp only [Bool.false_eq_true, ↓reduceIte]
  have := var_lt_high_var (h := h)
  simp [var] at this
  rw [h] at this
  simp at this
  apply Independence (O := (O.low h)) ⟨O.1.heap[j].var, (by convert var_lt_low_var (O := O); simp; rw [h]; simp)⟩

lemma OBdd.evaluate_high_eq_of_evaluate_eq_and_var_eq {n m} {O U : OBdd n m} {j i : Fin m} {ho : O.1.root = node j} {hu : U.1.root = node i} :
    O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.high ho).evaluate = (U.high hu).evaluate := by
  intro h eq
  rw [evaluate_high_eq_evaluate_set_true, h, eq ,← evaluate_high_eq_evaluate_set_true]


lemma OBdd.evaluate_low_eq_of_evaluate_eq_and_var_eq {n m} {O U : OBdd n m} {j i : Fin m} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := by
  intro h eq
  rw [evaluate_low_eq_evaluate_set_false, h, eq ,← evaluate_low_eq_evaluate_set_false]

lemma OBdd.not_reduced_of_iso_high_low {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    Isomorphic (O.high h) (O.low h) → ¬ O.Reduced := by
  intro iso R
  apply R.1 O.1.toRelevantPointer
  simp [toRelevantPointer]
  rw [h]
  constructor
  have giso : GraphIsomorphic O ⟨(O.high h).1.root, reachable_of_edge (edge_of_high (h := h) O.1)⟩
                                ⟨(O.low  h).1.root, reachable_of_edge (edge_of_low  (h := h) O.1)⟩ := iso
  exact (symm (R.2 giso))

/-- Reduced OBDDs are canonical.  -/
theorem OBdd.Canonicity {O U : OBdd n m} : O.Reduced → U.Reduced → O.evaluate = U.evaluate → O ≈ U := by
  intro O_reduced U_reduced h
  cases O_root_def : O.1.root with
  | terminal b =>
    cases U_root_def : U.1.root with
    | terminal c =>
      simp only [HasEquiv.Equiv, instSetoid, Isomorphic, InvImage]
      rcases O with ⟨⟨heap, root⟩, o⟩
      rcases U with ⟨⟨ueap, uoot⟩, u⟩
      simp_all
    | node i =>
      rw [evaluate_terminal' O_root_def] at h
      have : (U.high U_root_def).evaluate = (U.low U_root_def).evaluate := by
        ext I
        trans b
        · rw [evaluate_high_eq_evaluate_set_true]
          rw [← h]
          simp
        · rw [evaluate_low_eq_evaluate_set_false]
          rw [← h]
          simp
      absurd U_reduced
      apply not_reduced_of_iso_high_low (h := U_root_def)
      apply Canonicity (high_reduced U_reduced) (low_reduced U_reduced) this
  | node j =>
    cases U_root_def : U.1.root with
    | terminal c =>
      rw [evaluate_terminal' U_root_def] at h
      have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
        ext I
        trans c
        · rw [evaluate_high_eq_evaluate_set_true]
          rw [h]
          simp
        · rw [evaluate_low_eq_evaluate_set_false]
          rw [h]
          simp
      absurd O_reduced
      apply not_reduced_of_iso_high_low (h := O_root_def)
      apply Canonicity (high_reduced O_reduced) (low_reduced O_reduced) this
    | node i =>
      simp only [HasEquiv.Equiv, instSetoid, Isomorphic, InvImage]
      rw [toTree_node O_root_def, toTree_node U_root_def]
      simp only [Ordered, DecisionTree.branch.injEq]
      have same_var : O.1.heap[j].var = U.1.heap[i].var := by
        apply eq_iff_le_not_lt.mpr
        · constructor
          · apply le_of_not_lt
            intro contra
            have := Independence (O := O) ⟨U.1.heap[i].var.1, by rw [O_root_def]; simpa⟩
            rw [h] at this
            simp only [Fin.eta] at this
            simp only [independentOf] at this
            have that : OBdd.Isomorphic (U.high U_root_def) (U.low U_root_def) :=
              Canonicity (high_reduced U_reduced) (low_reduced U_reduced) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
            apply U_reduced.1 U.1.toRelevantPointer
            simp [toRelevantPointer]
            rw [U_root_def]
            constructor
            have iso : GraphIsomorphic U  ⟨(U.high U_root_def).1.root, reachable_of_edge (edge_of_high (h := U_root_def) U.1)⟩
                                          ⟨(U.low  U_root_def).1.root, reachable_of_edge (edge_of_low  (h := U_root_def) U.1)⟩ := that
            exact (symm (U_reduced.2 iso))
          · intro contra
            have := Independence (O := U) ⟨O.1.heap[j].var.1, by rw [U_root_def]; simpa⟩
            rw [← h] at this
            simp only [Ordered, Fin.eta] at this
            simp only [independentOf] at this
            have that : OBdd.Isomorphic (O.high O_root_def) (O.low O_root_def) :=
              Canonicity (high_reduced O_reduced) (low_reduced O_reduced) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
            apply O_reduced.1 O.1.toRelevantPointer
            simp [toRelevantPointer]
            rw [O_root_def]
            constructor
            have iso : GraphIsomorphic O  ⟨(O.high O_root_def).1.root, reachable_of_edge (edge_of_high (h := O_root_def) O.1)⟩
                                          ⟨(O.low  O_root_def).1.root, reachable_of_edge (edge_of_low  (h := O_root_def) O.1)⟩ := that
            exact (symm (O_reduced.2 iso))
      constructor
      · assumption
      · constructor
        · apply Canonicity (low_reduced  O_reduced) (low_reduced  U_reduced) (evaluate_low_eq_of_evaluate_eq_and_var_eq  h same_var)
        · apply Canonicity (high_reduced O_reduced) (high_reduced U_reduced) (evaluate_high_eq_of_evaluate_eq_and_var_eq h same_var)
termination_by O.size + U.size
decreasing_by
  simp [size_node U_root_def]; linarith
  simp [size_node O_root_def]; linarith
  all_goals
    simp [size_node O_root_def, size_node U_root_def]; linarith

/-- The only reduced BDD that denotes a constant function is the terminal BDD. -/
theorem OBdd.terminal_of_constant {n m} (O : OBdd n m) :
    O.Reduced → O.evaluate = (fun _ ↦ b) → O.1.root = terminal b := by
  cases O_root_def : O.1.root
  case terminal b' =>
    rcases O with ⟨⟨heap, root⟩, o⟩
    rintro _ h
    subst O_root_def
    simp only [OBdd.evaluate, Ordered, Function.comp_apply, DecisionTree.evaluate] at h
    unfold toTree at h
    simp [DecisionTree.evaluate] at h
    apply eq_of_constant_eq (α := Vec Bool n) at h
    simpa
  case node j =>
    intro R h
    exfalso
    apply not_reduced_of_iso_high_low (h := O_root_def)
    have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
      ext I
      trans b
      · rw [evaluate_high_eq_evaluate_set_true]
        rw [h]
        simp
      · rw [evaluate_low_eq_evaluate_set_false]
        rw [h]
        simp
    apply Canonicity (high_reduced R) (low_reduced R) this
    exact R

@[simp]
lemma low_heap_eq_heap {O : OBdd n m} {h : O.1.root = node j} : (O.low h).1.heap = O.1.heap := rfl

@[simp]
lemma high_heap_eq_heap {O : OBdd n m} {h : O.1.root = node j} : (O.high h).1.heap = O.1.heap := rfl


lemma oedge_of_low {h : O.1.root = node j} : OEdge O (O.low h) := ⟨rfl, edge_of_low (h := h)⟩
lemma oedge_of_high {h : O.1.root = node j} : OEdge O (O.high h) := ⟨rfl, edge_of_high (h := h)⟩

def OBdd.collect_helper (O : OBdd n m) : Vec Bool m × List (Fin m) → Vec Bool m × List (Fin m) := by
  cases h : O.1.root with
  | terminal b => exact id
  | node j =>
    let v := O.1.heap[j].var
    intro I
    exact if I.1.get j then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩)
termination_by O
decreasing_by
  exact oedge_of_high
  exact oedge_of_low

/-- Return a list of all reachable node indices. -/
def OBdd.collect : OBdd n m → List (Fin m) :=
  fun O ↦ (collect_helper O ⟨Vec.replicate m false, []⟩).2

lemma OBdd.collect_helper_terminal {v : Vec (Node n m) m} {h : Bdd.Ordered {heap := v, root := terminal b}} :
    collect_helper ⟨{heap := v, root := terminal b}, h⟩ I = I := by
  conv =>
    lhs
    unfold collect_helper
  congr

lemma OBdd.collect_helper_terminal' (O : OBdd n m) (h : O.1.root = terminal b) :
    collect_helper O I = I := by
  have O_def : O = ⟨{heap := O.1.heap, root := O.1.root}, O.2⟩ := rfl
  have := collect_helper_terminal (h := (show Bdd.Ordered {heap := O.1.heap, root := terminal b} by simp_rw [← h]; exact O.2)) (I := I)
  simp_rw [h] at O_def
  simp_rw [← O_def] at this
  rw [this]

lemma OBdd.collect_helper_node {v : Vec (Node n m) m} {h : Bdd.Ordered {heap := v, root := node j}} :
    collect_helper ⟨{heap := v, root := node j}, h⟩ I =
      if I.1.get j
      then I
      else collect_helper ⟨{heap := v, root := v[j].high}, ordered_of_relevant ⟨{heap := v, root := node j}, h⟩ ⟨v[j].high, reachable_of_edge (Edge.high rfl)⟩⟩
                          (collect_helper ⟨{heap := v, root := v[j].low}, ordered_of_relevant ⟨{heap := v, root := node j}, h⟩ ⟨v[j].low, reachable_of_edge (Edge.low rfl)⟩⟩
                                          ⟨I.1.set j true, j :: I.2⟩) := by
  conv =>
    lhs
    unfold collect_helper
  congr

lemma OBdd.collect_helper_node' (O : OBdd n m) {j : Fin m} (h : O.1.root = node j) :
    collect_helper O I = if I.1.get j then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩) := by
  have O_def : O = ⟨{heap := O.1.heap, root := O.1.root}, O.2⟩ := rfl
  have := collect_helper_node (h := (show Bdd.Ordered {heap := O.1.heap, root := node j} by simp_rw [← h]; exact O.2)) (I := I)
  simp_rw [h] at O_def
  simp_rw [← O_def] at this
  rw [this]
  congr

theorem OBdd.collect_helper_retains_found {O : OBdd n m} {I : Vec Bool m × List (Fin m)} :
    j ∈ I.2 → j ∈ (collect_helper O I).2 := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O O_root_def]
    assumption
  | node i =>
    rw [collect_helper_node' O O_root_def]
    cases I.1.get i
    case true  => simpa
    case false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have : j ∈ ((O.low O_root_def).collect_helper (I.1.set i true, i :: I.2)).2 := by
        apply collect_helper_retains_found
        simp only []
        cases decEq j i with
        | isFalse hf => right; assumption
        | isTrue ht => rw [ht]; left
      exact collect_helper_retains_found this
termination_by O
decreasing_by
  · exact oedge_of_low
  · exact oedge_of_high

theorem OBdd.collect_helper_retains_marked {O : OBdd n m} {I : Vec Bool m × List (Fin m)} :
    I.1.get j = true → (collect_helper O I).1.get j = true := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O O_root_def]
    assumption
  | node i =>
    rw [collect_helper_node' O O_root_def]
    cases I.1.get i
    case true  => simpa
    case false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have : ((O.low O_root_def).collect_helper (I.1.set i true, i :: I.2)).1.get j = true := by
        apply collect_helper_retains_marked
        simp only []
        cases decEq i j with
        | isFalse hf => rw [List.Vector.get_set_of_ne hf]; assumption
        | isTrue ht => rw [ht]; simp
      exact collect_helper_retains_marked this
termination_by O
decreasing_by
  · exact oedge_of_low
  · exact oedge_of_high

theorem OBdd.collect_helper_only_marks_reachable {O : OBdd n m} {I : Vec Bool m × List (Fin m)} :
    I.1.get j = false → (collect_helper O I).1.get j = true → Reachable O.1.heap O.1.root (node j) := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O O_root_def, h1] at h2; contradiction
  | node i =>
    cases decEq i j with
    | isTrue ht  => rw [ht]; exact Relation.ReflTransGen.refl
    | isFalse hf =>
      rw [collect_helper_node' O O_root_def] at h2
      cases hh : I.1.get i with
      | true => rw [hh] at h2; simp at h2; rw [h1] at h2; contradiction
      | false =>
        rw [hh] at h2
        simp at h2
        rw [← O_root_def]
        cases hhh : ((O.low O_root_def).collect_helper (I.1.set i true, i :: I.2)).1.get j with
        | false =>
          have : Reachable (O.high O_root_def).1.heap (O.high O_root_def).1.root (node j) := by
            apply collect_helper_only_marks_reachable (I := ((O.low O_root_def).collect_helper (I.1.set i true, i :: I.2)))
            · assumption
            · assumption
          simp at this
          trans (O.high O_root_def).1.root
          · exact reachable_of_edge (edge_of_high (h := O_root_def) O.1)
          · assumption
        | true =>
          have : Reachable (O.low O_root_def).1.heap (O.low O_root_def).1.root (node j) := by
            apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
            · simp; rw [List.Vector.get_set_of_ne hf]; assumption
            · assumption
          simp at this
          trans (O.low O_root_def).1.root
          · exact reachable_of_edge (edge_of_low (h := O_root_def) O.1)
          · assumption
termination_by O
decreasing_by
  exact oedge_of_high
  exact oedge_of_low

theorem OBdd.collect_helper_spec {O : OBdd n m} :
    (∀ i, (Reachable O.1.heap O.1.root (node i) → I.1.get i → i ∈ I.2)) →
    ∀ i, (Reachable O.1.heap O.1.root (node i) → (collect_helper O I).1.get i → i ∈ (collect_helper O I).2) := by
  intro h j re ma
  cases O_root_def : O.1.root with
  | terminal b =>
    have : (⟨node j, re⟩ : O.1.RelevantPointer).1  = terminal b := by
      apply eq_terminal_of_relevant
      rw [← O_root_def]
    contradiction
  | node k =>
    rw [collect_helper_node' O O_root_def] at ma
    rw [collect_helper_node' O O_root_def]
    cases hh : I.1.get k with
    | true =>
      rw [hh] at ma
      simp at ma
      simp
      exact h j re ma
    | false =>
      rw [hh] at ma
      simp at ma
      simp
      cases decEq k j with
      | isTrue hht =>
        apply collect_helper_retains_found
        apply collect_helper_retains_found
        rw [hht]
        left
      | isFalse hhf =>
        cases hhh : I.1.get j with
        | true =>
          apply collect_helper_retains_found
          apply collect_helper_retains_found
          right
          apply h <;> assumption
        | false=>
          cases hhhh : ((O.low O_root_def).collect_helper (I.1.set k true, k :: I.2)).1.get j with
          | true =>
            have : j ∈ ((O.low O_root_def).collect_helper (I.1.set k true, k :: I.2)).2 := by
              apply collect_helper_spec
              · intro i' re' ma'
                simp at ma'
                simp at re'
                simp only
                cases decEq k i' with
                | isFalse hff =>
                  rw [List.Vector.get_set_of_ne hff] at ma'
                  right
                  apply h
                  exact Reachable.trans (reachable_of_edge (edge_of_low (h := O_root_def) O.1)) re'
                  exact ma'
                | isTrue  htt => rw [htt]; left
              · have : (I.1.set k true, k :: I.2).1.get j = false := by simp only; rw [List.Vector.get_set_of_ne hhf]; exact hhh
                apply collect_helper_only_marks_reachable this hhhh
              · exact hhhh
            apply collect_helper_retains_found this
          | false=>
            apply collect_helper_spec
            · intro i' re' ma'
              simp at ma' re'
              have := h i' (Reachable.trans (reachable_of_edge (edge_of_high (h := O_root_def) O.1)) re')
              cases hhhhh : I.1.get i' with
              | true =>
                apply this at hhhhh
                have : i' ∈ (I.1.set k true, k :: I.2).2 := by simp only; right; exact hhhhh
                apply collect_helper_retains_found this
              | false=>
                cases decEq k i' with
                | isTrue hhtt =>
                  apply collect_helper_retains_found
                  rw [hhtt]
                  left
                | isFalse hhff =>
                  have that : (I.1.set k true, k :: I.2).1.get i' = false := by simp only; rw [List.Vector.get_set_of_ne hhff]; exact hhhhh
                  apply collect_helper_spec
                  · intro i'' re'' ma''
                    simp at ma''
                    simp at re''
                    simp only
                    cases decEq k i'' with
                    | isFalse hfff =>
                      rw [List.Vector.get_set_of_ne hfff] at ma''
                      right
                      apply h
                      exact Reachable.trans (reachable_of_edge (edge_of_low (h := O_root_def) O.1)) re''
                      exact ma''
                    | isTrue  htt => rw [htt]; left

                  · apply collect_helper_only_marks_reachable that ma'
                  · exact ma'
            · apply collect_helper_only_marks_reachable hhhh ma
            · assumption
termination_by O
decreasing_by
  exact oedge_of_low
  exact oedge_of_high
  exact oedge_of_low

/-- An acyclicity lemma: an edge from `O` to `U` implies that `O` is not reachable from `U`.  -/
lemma OBdd.not_oedge_reachable {n m} {O U : OBdd n m}: OEdge O U → ¬ Reachable O.1.heap U.1.root O.1.root := by
  rintro ⟨same_heap, e⟩ contra
  apply Relation.reflTransGen_iff_eq_or_transGen.mp at contra
  cases contra with
  | inl h =>
    rw [← h] at e
    have : GraphEdge O.1 O.1.toRelevantPointer O.1.toRelevantPointer := e
    apply O.2 at this
    simp at this
  | inr h =>
    apply transGen_iff_single_and_reflTransGen.mp at h
    rcases h with ⟨c, h1, h2⟩
    rw [same_heap] at h1
    let V : OBdd n m := ⟨{heap := U.1.heap, root := c}, ordered_of_edge (r := rfl) (h := rfl) c h1⟩
    have : c = V.1.root := rfl
    rw [this] at h1 h2
    apply not_oedge_reachable ⟨by rfl, h1⟩
    trans O.1.root
    rw [same_heap] at h2; exact h2
    rw [← same_heap]; exact reachable_of_edge e
termination_by O

lemma OBdd.reachable_or_eq_low_high {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → (O.1.root = p ∨ (∃ j, ∃ (h : O.1.root = node j), (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p))) := by
  intro r
  cases (Relation.reflTransGen_swap.mp r) with
  | refl => left; rfl
  | tail t e =>
    rcases O_def: O with ⟨⟨heap, root⟩, o⟩
    simp only
    have O_root_def : O.1.root = root := by rw [O_def]
    cases root with
    | terminal b =>
      rw [O_root_def] at e
      contradiction
    | node j =>
      right
      use j
      use rfl
      rw [O_root_def] at e
      cases e with
      | low h =>
        left
        apply (Relation.reflTransGen_swap.mp) at t
        rw [← h] at t
        simp_rw [← O_def]
        have O_heap_def : O.1.heap = heap := by rw [O_def]
        nth_rw 1 [O_heap_def] at t
        exact t
      | high h =>
        right
        apply (Relation.reflTransGen_swap.mp) at t
        rw [← h] at t
        simp_rw [← O_def]
        have O_heap_def : O.1.heap = heap := by rw [O_def]
        nth_rw 1 [O_heap_def] at t
        exact t

lemma OBdd.collect_spec' {O : OBdd n m} {j : Fin m} {I : Vec Bool m × List (Fin m)} :
    Reachable O.1.heap O.1.root (node j) → (∀ i, (Reachable O.1.heap O.1.root (node i) → Reachable O.1.heap (node i) (node j) → I.1.get i = false)) → (O.collect_helper I).1.get j = true := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b =>
    have : (⟨node j, h1⟩ : O.1.RelevantPointer).1  = terminal b := by
      apply eq_terminal_of_relevant
      rw [← O_root_def]
    contradiction
  | node i =>
    rw [collect_helper_node' O O_root_def]
    have : I.1.get i = false := by
      apply h2 i
      · rw [← O_root_def]
        exact Relation.ReflTransGen.refl
      · rw [← O_root_def]
        exact h1
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases decEq i j with
    | isTrue h =>
      apply collect_helper_retains_marked
      apply collect_helper_retains_marked
      rw [h]
      simp
    | isFalse hij =>
      cases Pointer.instDecidableReachable (O.low O_root_def) (node j) with
      | isTrue ht  =>
        apply collect_helper_retains_marked
        apply collect_spec'
        · exact ht
        · intro i' re1 re2
          simp only
          cases decEq i i' with
          | isTrue h =>
            exfalso
            apply not_oedge_reachable (oedge_of_low (h := O_root_def))
            rw [← h] at re1
            rw [O_root_def]
            exact re1
          | isFalse h =>
            rw [List.Vector.get_set_of_ne h]
            apply h2
            exact Reachable.trans (reachable_of_edge (edge_of_low (h := O_root_def) O.1)) re1
            exact re2
      | isFalse hf =>
        apply collect_spec'
        · cases (reachable_or_eq_low_high (p := node j) h1) with
        | inl h => rw [O_root_def] at h; simp at h; contradiction
        | inr h =>
          rcases h with ⟨j', h', d⟩
          have same : i = j' := by rw [O_root_def] at h'; simp at h'; assumption
          subst same
          cases d with
          | inl => contradiction
          | inr => assumption
        · intro i' re ma
          contrapose! hf
          simp only [Bool.not_eq_false] at hf
          apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
          rw [List.Vector.get_set_of_ne hij]
          apply h2
          · exact Reachable.trans (reachable_of_edge (edge_of_high (h := O_root_def) O.1)) (Reachable.trans re ma)
          · exact Relation.ReflTransGen.refl
          · apply collect_spec'
            · have that : Reachable (O.low O_root_def).1.heap (O.low O_root_def).1.root (node i') := by
                apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
                · cases decEq i i' with
                  | isFalse hff =>
                    rw [List.Vector.get_set_of_ne hff]
                    apply h2 i' (Reachable.trans (reachable_of_edge (edge_of_high (h := O_root_def) O.1)) re) ma
                  | isTrue htt =>
                    exfalso
                    apply not_oedge_reachable (oedge_of_high (h := O_root_def))
                    rw [htt] at O_root_def
                    rw [O_root_def]
                    exact re
                · assumption
              exact Reachable.trans that ma
            · intro i'' re1 re2
              simp only
              cases decEq i i'' with
              | isTrue h =>
                rw [← h] at re1
                exfalso
                apply not_oedge_reachable (oedge_of_low (h := O_root_def))
                rw [O_root_def]
                exact re1
              | isFalse h =>
                rw [List.Vector.get_set_of_ne h]
                apply h2
                exact Reachable.trans (reachable_of_edge (edge_of_low (h := O_root_def) O.1)) re1
                exact re2
termination_by O
decreasing_by
  · exact oedge_of_low
  · exact oedge_of_high
  · exact oedge_of_low

/-- `collect` is correct. -/
theorem OBdd.collect_spec {O : OBdd n m} {j : Fin m} : Reachable O.1.heap O.1.root (node j) → j ∈ collect O := by
  intro h
  simp [collect]
  apply collect_helper_spec
  · intro i re ma
    rw [List.Vector.get_replicate false i] at ma
    contradiction
  · assumption
  · apply collect_spec' h
    intro i re1 re2
    exact List.Vector.get_replicate false i

-- def OBdd.collect_helper (O : OBdd n m) : Vec Bool m × List (Fin m) → Vec Bool m × List (Fin m) := by
--   cases h : O.1.root with
--   | terminal b => exact id
--   | node j =>
--     let v := O.1.heap[j].var
--     intro I
--     exact if I.1.get j then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩)
-- termination_by O
-- decreasing_by
--   exact oedge_of_high
--   exact oedge_of_low

-- theorem OBdd.collect_helper_spec_reverse {O : OBdd n m} :
--     (∀ i ∈ I.2, Reachable O.1.heap O.1.root (node i)) →
--     ∀ i ∈ (collect_helper O I).2, Reachable O.1.heap O.1.root (node i) := by
--   intro h1 i h2
--   cases h : O.1.root with
--   | terminal b =>
--     rw [collect_helper_terminal' O h] at h2
--     rw [h] at h1
--     exact h1 i h2
--   | node j =>
--     rw [collect_helper_node' O h] at h2
--     split at h2
--     next ht =>
--       rw [h] at h1
--       exact h1 i h2
--     next hf =>
--       cases List.instDecidableMemOfLawfulBEq i (j :: I.2) with
--       | isTrue htt =>
--         cases htt with
--         | head as => left
--         | tail b hin =>
--           rw [h] at h1
--           exact h1 i hin
--       | isFalse hff =>
--         cases List.instDecidableMemOfLawfulBEq i ((O.low h).collect_helper (I.1.set j true, j :: I.2)).2 with
--         | isFalse hhf => sorry
--         | isTrue hht =>
--           rw [← h]
--           suffices s : (Reachable O.1.heap (O.low h).1.root (node i)) from Relation.ReflTransGen.trans (reachable_of_edge (edge_of_low (h := h) O.1)) s
--           rw [← low_heap_eq_heap (h := h)]
--           apply collect_helper_spec_reverse _ i hht
--           · intro i' hi'
--             simp only at hi'
--             sorry

-- theorem OBdd.collect_spec_reverse {O : OBdd n m} {j : Fin m} : j ∈ collect O → Reachable O.1.heap O.1.root (node j) := by
--   intro h
--   simp only [collect] at h
--   unfold collect_helper at h
--   sorry
