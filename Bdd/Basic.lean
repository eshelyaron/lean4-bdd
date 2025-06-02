import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Basic
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Vector
import Bdd.Nary
import Bdd.DecisionTree

instance {α : Type u} [ToString α] : ToString (Vector α k) := ⟨fun v ↦ v.toList.toString⟩

/-- Pointer to a BDD node or terminal -/
inductive Pointer m where
  | terminal : Bool → Pointer _
  | node : Fin m → Pointer m
deriving Fintype, DecidableEq, Repr, Hashable

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
  heap : Vector (Node n m) m
  root : Pointer m
deriving DecidableEq

-- def Pointer' := Bool ⊕ Nat

-- structure Node' where
--   var  : Nat
--   low  : Pointer'
--   high : Pointer'

-- def Edge' (M : Array Node') (j k : Nat) : Prop := ∃ h : j < M.size, ((M[j]'h).low = .inr k ∨ (M[j]'h).high = .inr k)

-- def Pointer'.Safe (M : Array Node') (p : Pointer') := ∀ j, p = .inr j → ∀ k, Relation.ReflTransGen (Edge' M) j k → k < M.size

-- structure Bdd' where
--   heap : Array Node'
--   root : Pointer'
--   safe : root.Safe heap

instance Bdd.instToString : ToString (Bdd n m) := ⟨fun B => "⟨" ++ (toString B.heap) ++ ", " ++ (toString B.root)  ++ "⟩"⟩

open Bdd
-- example : Bdd n 0 := ⟨Vector.emptyWithCapacity 0, .terminal true⟩

-- example : Bdd 1 1 := ⟨Vector.singleton ⟨0, .node 0, .node 0⟩, .node 0⟩

inductive Edge (M : Vector (Node n m) m) : Pointer m → Pointer m → Prop where
  | low  : M[j].low  = p → Edge M (node j) p
  | high : M[j].high = p → Edge M (node j) p

/-- Terminals have no outgoing edges. -/
lemma not_terminal_edge {q} : ¬ Edge w (terminal b) q := by
  intro contra
  contradiction

--FIXME: Maybe use WithTop (Fin n) instead of Fin n.succ
def Pointer.toVar (M : Vector (Node n m) m) : Pointer m → Fin n.succ
  | terminal _ => Fin.last n
  | node j     => M[j].var

@[simp]
lemma Pointer.toVar_terminal_eq {n m} (w : Vector (Node n m) m) : toVar w (terminal b) = n := Fin.natCast_eq_last n ▸ rfl

@[simp]
lemma Pointer.toVar_node_eq {n m} (w : Vector (Node n m) m) {j} : toVar w (node j) = w[j].var := rfl

lemma Pointer.toVar_heap_set : i ≠ j → toVar (M.set i N) (node j) = toVar M (node j) := by
  intro neq
  simp only [Nat.succ_eq_add_one, toVar_node_eq, Fin.coe_eq_castSucc,Fin.castSucc_inj]
  congr 1
  apply Vector.getElem_set_ne
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  simp_all

@[simp]
def Pointer.MayPrecede (M : Vector (Node n m) m) (p q : Pointer m) := toVar M p < toVar M q

/-- Terminals must not precede other pointers. -/
lemma Pointer.not_terminal_MayPrecede : ¬ MayPrecede M (terminal b) p := by
  cases p with
  | terminal _ => simp [MayPrecede]
  | node     j => exact not_lt.mpr (Fin.le_last _)

/-- Non-terminals may precede terminals. -/
lemma Pointer.MayPrecede_node_terminal {n m} (w : Vector (Node n m) m) {j} : MayPrecede w (node j) (terminal b) := by
  simp [Fin.castSucc_lt_last]

def Pointer.Reachable {n m} (w : Vector (Node n m) m) := Relation.ReflTransGen (Edge w)

@[trans]
theorem Pointer.Reachable.trans (hab : Reachable v a b) (hbc : Reachable v b c) : Reachable v a c := Relation.ReflTransGen.trans hab hbc

/-- `B.RelevantPointer` is the subtype of pointers reachable from `B.root`. -/
abbrev Bdd.RelevantPointer {n m} (B : Bdd n m) := { q // Reachable B.heap B.root q}

instance Bdd.instDecidableEqRelevantPointer : DecidableEq (Bdd.RelevantPointer B) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.eq_iff)

def Bdd.toRelevantPointer {n m} (B : Bdd n m) : B.RelevantPointer :=
  ⟨B.root, Relation.ReflTransGen.refl⟩

/-- The `Edge` relation lifted to `RelevantPointer`s. -/
@[simp]
abbrev Bdd.RelevantEdge (B : Bdd n m) (p q : B.RelevantPointer) := Edge B.heap p.1 q.1

lemma Bdd.relevantEdge_of_edge_of_reachable  {B : Bdd n m}
    (e : Edge B.heap p q) (hp : Reachable B.heap B.root p) :
  RelevantEdge B ⟨p, hp⟩ ⟨q, .tail hp e⟩ := e

/-- The `MayPrecede` relation lifted to `RelevantPointer`s. -/
@[simp]
def Bdd.RelevantMayPrecede (B : Bdd n m) (p q : B.RelevantPointer) := MayPrecede B.heap p.1 q.1

/-- A BDD is `Ordered` if all edges relevant from the root respect the variable ordering. -/
def Bdd.Ordered (B : Bdd n m) := Subrelation (RelevantEdge B) (RelevantMayPrecede B)

/-- Terminals induce `Ordered` BDDs. -/
lemma Bdd.Ordered_of_terminal : Bdd.Ordered ⟨M, terminal b⟩ := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ h
  cases Relation.reflTransGen_swap.mp hp <;> exfalso <;> apply not_terminal_edge <;> assumption

lemma Bdd.Ordered_of_terminal' {B : Bdd n m} : B.root = terminal b → B.Ordered := by
  intro h
  rcases B with ⟨M, r⟩
  simp only at h
  rw [h]
  apply Ordered_of_terminal

def OBdd n m := { B : Bdd n m // B.Ordered }

def OEdge (O U : OBdd n m) := O.1.heap = U.1.heap ∧ Edge O.1.heap O.1.root U.1.root

@[simp]
def Bdd.var {n m} (B : Bdd n m) : Fin n.succ := B.root.toVar B.heap

@[simp]
def OBdd.var {n m} (O : OBdd n m) : Nat := O.1.var

@[simp]
def OBdd.rav {n m} (B : OBdd n m) : Nat := n - B.var

/-- The `OEdge` relation between Ordered BDDs is well-founded. -/
theorem OEdge.wellFounded {n m} : @WellFounded (OBdd n m) OEdge := by
  suffices s : Subrelation (@OEdge n m) (InvImage Nat.lt OBdd.var) from Subrelation.wf s (InvImage.wf _ (Nat.lt_wfRel.wf))
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
  simp_all only []
  rw [← h1] at h2
  let xs := x.toRelevantPointer
  let ys : x.RelevantPointer := ⟨y.root, Relation.ReflTransGen.tail Relation.ReflTransGen.refl h2⟩
  have h3 : RelevantEdge x xs ys := h2
  apply hx at h3
  simp only [RelevantMayPrecede, Bdd.toRelevantPointer, xs, ys] at h3
  simp only [InvImage, OBdd.var, Nat.succ_eq_add_one, Nat.lt_eq, Fin.val_fin_lt, gt_iff_lt, xs, ys]
  rcases hp : x.root
  case terminal => simp_all only [Ordered, MayPrecede, Nat.succ_eq_add_one, toVar_terminal_eq, Fin.natCast_eq_last, var, Fin.val_last, ys, xs]
  case node j => rcases hq : y.root <;> simp_all

/-- The `OEdge` relation between Ordered BDDs is converse well-founded. -/
theorem OEdge.flip_wellFounded {n m} : @WellFounded (OBdd n m) (flip OEdge) := by
  refine Subrelation.wf ?_ (InvImage.wf OBdd.rav (Nat.lt_wfRel.wf))
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
  simp_all only
  rw [← h1] at h2
  let ys := y.toRelevantPointer
  let xs : y.RelevantPointer := ⟨x.root, .tail .refl h2⟩
  have h3 : RelevantEdge y ys xs := h2
  apply hy at h3
  simp only [RelevantMayPrecede, Bdd.toRelevantPointer, xs, ys] at h3
  simp only [InvImage, OBdd.rav, OBdd.var, Nat.succ_eq_add_one, Nat.lt_eq, gt_iff_lt, xs, ys]
  cases hp : y.root with
  | terminal => rw [hp] at h2; contradiction
  | node j => cases _ : x.root <;> refine Nat.sub_lt_sub_left ?_ ?_ <;> simp_all

instance OEdge.instWellFoundedRelation {n m} : WellFoundedRelation (OBdd n m) where
  rel := flip OEdge
  wf  := flip_wellFounded

lemma Bdd.ordered_of_reachable' {B : Bdd n m} :
    B.Ordered → Reachable B.heap B.root p → Ordered ⟨B.heap, p⟩ :=
  fun ho hr x _ _ ↦ ho (Bdd.relevantEdge_of_edge_of_reachable (by simp_all) (.trans hr x.2))

lemma Bdd.ordered_of_reachable {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → Ordered ⟨O.1.heap, p⟩ :=
  fun hp ⟨_, hx⟩ _ _ ↦ O.2 (Bdd.relevantEdge_of_edge_of_reachable (by simp_all) (.trans hp hx))

/-- All BDDs in the graph of an `Ordered` BDD are `Ordered`. -/
lemma Bdd.ordered_of_relevant (O : OBdd n m) (S : O.1.RelevantPointer) :
    Ordered {heap := O.1.heap, root := S.1} := ordered_of_reachable S.2

def Bdd.low (B : Bdd n m) : B.root = node j → Bdd n m
  | _ => {heap := B.heap, root := B.heap[j].low}

lemma Bdd.edge_of_low (B : Bdd n m) {h : B.root = node j} : Edge B.heap B.root (B.low h).root := by
  simp only [low, h]
  exact Edge.low rfl

def Bdd.high (B : Bdd n m) : B.root = node j → Bdd n m
  | _ => {heap := B.heap, root := B.heap[j].high}

lemma Bdd.edge_of_high (B : Bdd n m) {h : B.root = node j} : Edge B.heap B.root (B.high h).root := by
  simp only [high, h]
  exact Edge.high rfl

lemma Bdd.reachable_of_edge : Edge M p q → Reachable M p q := Relation.ReflTransGen.tail Relation.ReflTransGen.refl

lemma Bdd.ordered_of_relevant' {B : Bdd n m} {h : B.heap = v} {r : B.root = q} :
    B.Ordered → Reachable v q p → Bdd.Ordered {heap := v, root := p} := by
  intro o r_q_p
  simp_all only [Ordered]
  rintro ⟨x, hx⟩ ⟨y, hy⟩ e
  simp_all only [Ordered, RelevantEdge, RelevantMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  simp at hx
  simp at hy
  have : RelevantEdge B ⟨x, (by trans p <;> aesop)⟩
                        ⟨y, (by trans p <;> aesop)⟩ := by
    simp only [RelevantEdge]
    rw [h]
    assumption
  apply o at this
  rw [← h]
  exact this

lemma Bdd.ordered_of_edge {B : Bdd n m} : B.Ordered → Edge B.heap B.root p → Bdd.Ordered ⟨B.heap, p⟩ := by
  exact fun o e ↦ ordered_of_reachable' o (reachable_of_edge e)

lemma Bdd.high_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.high h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge o
  rw [h]
  right
  rfl

lemma Bdd.low_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.low h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge o
  rw [h]
  left
  rfl

lemma Bdd.low_heap_eq_heap {B : Bdd n m} {h : B.root = node j} : (B.low h).heap = B.heap := rfl
lemma Bdd.low_root_eq_low {B : Bdd n m} {h : B.root = node j} : (B.low h).root = B.heap[j].low := rfl

lemma Bdd.high_heap_eq_heap {B : Bdd n m} {h : B.root = node j} : (B.high h).heap = B.heap := rfl
lemma Bdd.high_root_eq_high {B : Bdd n m} {h : B.root = node j} : (B.high h).root = B.heap[j].high := rfl

def OBdd.high (O : OBdd n m) : O.1.root = node j → OBdd n m
  | h => ⟨O.1.high h, Bdd.high_ordered h O.2⟩

def OBdd.low (O : OBdd n m) : O.1.root = node j → OBdd n m
  | h => ⟨O.1.low h, Bdd.low_ordered h O.2⟩

@[simp]
lemma OBdd.low_heap_eq_heap {O : OBdd n m} {h : O.1.root = node j} : (O.low h).1.heap = O.1.heap := rfl
lemma OBdd.low_root_eq_low {O : OBdd n m} {h : O.1.root = node j} : (O.low h).1.root = O.1.heap[j].low := rfl

@[simp]
lemma OBdd.high_heap_eq_heap {O : OBdd n m} {h : O.1.root = node j} : (O.high h).1.heap = O.1.heap := rfl
lemma OBdd.high_root_eq_high {O : OBdd n m} {h : O.1.root = node j} : (O.high h).1.root = O.1.heap[j].high := rfl

lemma oedge_of_low  {h : O.1.root = node j} : OEdge O (O.low h)  := ⟨rfl, edge_of_low  (h := h)⟩
lemma oedge_of_high {h : O.1.root = node j} : OEdge O (O.high h) := ⟨rfl, edge_of_high (h := h)⟩

macro_rules | `(tactic| decreasing_trivial) => `(tactic| exact oedge_of_low)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| exact oedge_of_high)

def OBdd.toTree (O : OBdd n m) : DecisionTree n :=
  match h : O.1.root with
  | terminal b => .leaf b
  | node j     => .branch O.1.heap[j].var (toTree (O.low h)) (toTree (O.high h))
termination_by O

def OBdd.evaluate : OBdd n m → Vector Bool n → Bool := DecisionTree.evaluate ∘ OBdd.toTree

lemma OBdd.evaluate_cast {O : OBdd n m} (h : n = n') : (h ▸ O).evaluate I = O.evaluate (h ▸ I) := by
  subst h
  rfl

def OBdd.HSimilar (O : OBdd n m) (U : OBdd n m') := O.toTree = U.toTree

def OBdd.Similar : OBdd n m → OBdd n m → Prop := HSimilar

/-- Similarity of `Ordered` BDDs is decidable. -/
instance OBdd.instDecidableSimilar {n m} : DecidableRel (β := OBdd n m) OBdd.Similar :=
  fun O U ↦ decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar, HSimilar])

-- FIXME: Use the instance from Sim.lean instead.
private instance OBdd.instDecidableHSimilar (O : OBdd n m) (U : OBdd n m') : Decidable (OBdd.HSimilar O U) :=
  decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar, HSimilar])

def OBdd.SimilarRP (O : OBdd n m) (p q : O.1.RelevantPointer) :=
  Similar ⟨{heap := O.1.heap, root := p.1}, ordered_of_reachable p.2⟩
          ⟨{heap := O.1.heap, root := q.1}, ordered_of_reachable q.2⟩

instance OBdd.instDecidableSimilarRP : Decidable (OBdd.SimilarRP O l r) := by
  simp only [OBdd.SimilarRP]; infer_instance

/-- Isomorphism of `Ordered` BDDs is an equivalence relation. -/
def OBdd.Similar.instEquivalence {n m} : Equivalence (α := OBdd n m) OBdd.Similar := by
  apply InvImage.equivalence
  constructor <;> simp_all [Similar, HSimilar]

-- instance OBdd.Similar.instReflexive : Reflexive (α := OBdd n m) OBdd.Similar := instEquivalence.refl

-- instance OBdd.Similar.instSymmetric : Symmetric (α := OBdd n m) OBdd.Similar := fun _ _ ↦ instEquivalence.symm

-- instance OBdd.Similar.instTransitive : Transitive (α := OBdd n m) OBdd.Similar := fun _ _ _ ↦ instEquivalence.trans

/-- A pointer is redundant if it point to node `N` with `N.low = N.high`. -/
inductive Pointer.Redundant (M : Vector (Node n m) m) : Pointer m → Prop where
  | red : M[j].low = M[j].high → Redundant M (node j)

instance Pointer.Redundant.instDecidable {n m} (w : Vector (Node n m) m) : DecidablePred (Redundant w) := by
  intro p
  cases p
  case terminal => apply isFalse; intro; contradiction
  case node j =>
    cases decEq w[j].low w[j].high
    case isFalse => apply isFalse; intro contra; cases contra; contradiction
    case isTrue h => exact isTrue ⟨h⟩

def Bdd.NoRedundancy (B : Bdd n m) := ∀ (p : B.RelevantPointer), ¬ Redundant B.heap p.1

/-- A BDD is `Reduced` if its graph does not contain redundant nodes or distinct similar subgraphs. -/
def OBdd.Reduced {n m} (O : OBdd n m) : Prop
  -- No redundant pointers.
  := NoRedundancy O.1
  -- Similarity implies pointer-equality.
   ∧ Subrelation (SimilarRP O) (InvImage Eq Subtype.val)

--- TODO: Move elsewhere or drop.
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

theorem RelevantEdge.flip_wellFounded (o : Ordered B) : WellFounded (flip (RelevantEdge B)) := by
  have : Subrelation (flip (RelevantEdge B)) (InvImage Nat.lt RelevantPointer.gap) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ e
    simp_all only [InvImage, flip, RelevantPointer.gap]
    refine Nat.sub_lt_sub_left ?_ ?_
    cases e <;> simp
    exact o e
  exact Subrelation.wf this (InvImage.wf _ (Nat.lt_wfRel.wf))

instance RelevantEdge.instWellFoundedRelation {n m} (O : OBdd n m) : WellFoundedRelation O.1.RelevantPointer where
  rel := flip O.1.RelevantEdge
  wf  := (RelevantEdge.flip_wellFounded O.2)

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
  all_goals simp_all only [Ordered, flip, RelevantEdge, Fin.getElem_fin, Edge.low, Edge.high]

instance Pointer.instDecidableReachable {n m} (O : OBdd n m) :
    DecidablePred (Reachable O.1.heap O.1.root) :=
  OBdd.instDecidableReflTransGen O ⟨O.1.root, Relation.ReflTransGen.refl⟩

--set_option trace.Meta.synthInstance true

def OBdd.size {n m} (O : OBdd n m) := Fintype.card { j // Reachable O.1.heap O.1.root (.node j) }

instance OBdd.instFintypeRelevantPointer {n m} (O : OBdd n m) : Fintype (O.1.RelevantPointer) := by
  convert Subtype.fintype _ <;> infer_instance

instance Pointer.instDecidableEitherReachable {n m} (O U : OBdd n m) (h : O.1.heap = U.1.heap) :
    DecidablePred (fun q ↦ (Reachable O.1.heap O.1.root q) ∨ (Reachable O.1.heap U.1.root q)) := by
  intro p
  simp
  cases instDecidableReachable O p with
  | isFalse hf =>
    cases instDecidableReachable U p with
    | isFalse hhf =>
      apply isFalse
      simp_all only [or_self, not_false_eq_true]
    | isTrue  hht =>
      apply isTrue
      simp_all only [or_true]
  | isTrue  ht =>
    apply isTrue
    simp_all only [true_or]

instance OBdd.instFintypeEitherRelevantPointer (O U : OBdd n m) (h : O.1.heap = U.1.heap) : Fintype {q // Reachable O.1.heap O.1.root q ∨ Reachable O.1.heap U.1.root q} := by
  convert Subtype.fintype _
  · exact instDecidableEitherReachable O U h
  · infer_instance

/-- The inverse image of a decidable relation is decidable. -/
private instance my_decidableRel_of_invImage2 {r : β → β → Prop} [DecidableRel r] {f : α → β} :
    DecidableRel (InvImage r f) :=
  fun a b ↦ decidable_of_decidable_of_iff (show (r (f a) (f b)) ↔ _ by simp [InvImage])

/-- `Reduced` is decidable. -/
instance OBdd.instReducedDecidable {n m} : DecidablePred (α := OBdd n m) Reduced :=
  fun _ ↦ (instDecidableAnd (dp := Fintype.decidableForallFintype) (dq := Fintype.decidableForallFintype))

/-- The output of equal constant functions with inhabited domain is equal. -/
lemma eq_of_constant_eq {α β} {c c' : β} [Inhabited α] :
    Function.const α c = Function.const α c' → c = c' :=
  fun h ↦ (show (Function.const α c) default = (Function.const α c') default by rw [h])

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

lemma not_OEdge_of_isTerminal {O : OBdd n m}: O.isTerminal → ¬ OEdge O U := by
  rintro ⟨b, h⟩ ⟨_, contra⟩
  rw [h] at contra
  exact not_terminal_edge contra

/-- The graph induced by a terminal BDD consists of a sole terminal pointer. -/
lemma Bdd.terminal_relevant_iff {n m} {B : Bdd n m} (h : B.root = terminal b) (S : B.RelevantPointer) {motive : Pointer m → Prop} :
    motive S.1 ↔ motive (terminal b) := by
  rw [← h]
  rcases S with ⟨s, hs⟩
  cases (Relation.reflTransGen_swap.mpr hs)
  case refl        => simp
  case tail contra => rw [h] at contra; contradiction

lemma Bdd.eq_terminal_of_relevant {n m} {v : Vector (Node n m) m} {B : Bdd n m} (h : B = {heap := v, root := terminal b}) (S : B.RelevantPointer) :
    S.1 = terminal b :=
  (terminal_relevant_iff (by simp [h]) S).mp rfl

/-- Terminal BDDs are reduced. -/
lemma OBdd.reduced_of_terminal {n m} {O : OBdd n m} : O.isTerminal → O.Reduced := by
  rintro ⟨b, h⟩
  constructor
  · intro p R
    have contra : Redundant O.1.heap (terminal b) := by apply (terminal_relevant_iff h p).mp R
    contradiction
  · intro p q _
    calc p.1
      _ = terminal b :=         (eq_terminal_of_relevant (by rw [← h]) p)
      _ = q.1        := Eq.symm (eq_terminal_of_relevant (by rw [← h]) q)

lemma Bdd.reduced_of_terminal : OBdd.Reduced ⟨⟨M, terminal b⟩, o⟩ := OBdd.reduced_of_terminal ⟨b, rfl⟩

/-- Sub-BDDs of a reduced BDD are reduced. -/
lemma OBdd.reduced_of_relevant {O : OBdd n m} (S : O.1.RelevantPointer):
    O.Reduced → OBdd.Reduced ⟨{heap := O.1.heap, root := S.1}, ordered_of_relevant O S⟩ := by
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
      have : SimilarRP ⟨{ heap := O.1.heap, root := node j }, o⟩
              ⟨q.1, Relation.transitive_reflTransGen S.2 q.2⟩
              ⟨p.1, Relation.transitive_reflTransGen S.2 p.2⟩ := by
        simp_all only [SimilarRP, Similar, InvImage]
      apply R.2 this

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
lemma OBdd.evaluate_node {n m} {v : Vector (Node n m) m} {I : Vector Bool n} {j : Fin m} {h} : OBdd.evaluate ⟨{ heap := v, root := node j }, h⟩ I =
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

lemma OBdd.evaluate_node' {n m} {v : Vector (Node n m) m} {j : Fin m} {h} : OBdd.evaluate ⟨{ heap := v, root := node j }, h⟩ = fun I ↦
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
lemma OBdd.evaluate_terminal {n m} {v : Vector (Node n m) m} {h} : OBdd.evaluate ⟨{ heap := v, root := terminal b }, h⟩ = Function.const _ b := by
  simp only [evaluate, Function.comp_apply, toTree, DecisionTree.evaluate]
  rfl

lemma OBdd.evaluate_terminal' {n m} {O : OBdd n m} : O.1.root = terminal b → O.evaluate = Function.const _ b := by
  intro h
  rcases O with ⟨⟨heap, root⟩, ho⟩
  simp_all

@[simp]
lemma OBdd.toTree_terminal {n m} {v : Vector (Node n m) m} {h} : OBdd.toTree ⟨{ heap := v, root := terminal b }, h⟩ = .leaf b := by simp [toTree]

lemma OBdd.toTree_terminal' {n m} {O : OBdd n m} : O.1.root = terminal b → O.toTree = .leaf b := by
  intro h
  rcases O with ⟨⟨heap, root⟩, ho⟩
  simp_all [toTree]

lemma OBdd.HSimilar_of_terminal {n m m' : Nat} {b : Bool} {O : OBdd n m} {U : OBdd n m'} :
    O.1.root = terminal b → U.1.root = terminal b → O.HSimilar U := by
  intro h1 h2
  simp [HSimilar]
  rw [toTree_terminal' h1, toTree_terminal' h2]

private lemma aux {O : OBdd n m} {i : Fin m} :
    O.1.heap[i.1].var = Fin.castPred (toVar O.1.heap (node i)) (Fin.exists_castSucc_eq.mp ⟨O.1.heap[i.1].var, by simp⟩) :=
  by simp

lemma OBdd.toTree_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.toTree = .branch O.1.heap[j].var (toTree (O.low h)) (toTree (O.high h)) := by
  conv => lhs; unfold toTree
  split
  next _  heq => rw [h] at heq; contradiction
  next j' heq => rw [h] at heq; injection heq with heq; subst heq; rfl

lemma OBdd.evaluate_node'' {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    O.evaluate = fun I ↦ if I[O.1.heap[j].var] then (O.high h).evaluate I else (O.low h).evaluate I := by
  simp only [evaluate, Function.comp_apply]
  rw [toTree_node h]
  simp [DecisionTree.evaluate]

lemma OBdd.var_lt_high_var {O : OBdd n m} {h : O.1.root = node j} :
    O.var < (O.high h).var := by
  have e := Bdd.edge_of_high (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.high h).1.root, reachable_of_edge e⟩ e

lemma OBdd.var_lt_low_var {O : OBdd n m} {h : O.1.root = node j} :
    O.var < (O.low h).var := by
  have e := Bdd.edge_of_low (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.low h).1.root, reachable_of_edge e⟩ e

lemma OBdd.independentOf_lt_root (O : OBdd n m) (i : Fin O.var) :
    Nary.IndependentOf (O.evaluate) ⟨i.1, Fin.val_lt_of_le i (Fin.is_le _)⟩ := by
  cases h : O.1.root with
  | terminal _ => simp [evaluate_terminal' h]
  | node j =>
    intro b I
    rw [evaluate_node'' h]
    simp only
    rcases i with ⟨i, hi⟩
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      symm
      apply Vector.getElem_set_ne _ _ (Nat.ne_of_lt (by simp_all))
    · exact (independentOf_lt_root (O.high h) ⟨i, .trans hi var_lt_high_var⟩) b I
    · exact (independentOf_lt_root (O.low  h) ⟨i, .trans hi var_lt_low_var⟩) b I
termination_by O

def OBdd.size' {n m} : OBdd n m → Nat := DecisionTree.size ∘ OBdd.toTree

lemma OBdd.size_zero_of_terminal : OBdd.isTerminal O → O.size' = 0 := by
  rintro ⟨b, h⟩
  rcases O with ⟨⟨heap, root⟩, o⟩
  subst h
  simp only [size', Ordered, Function.comp_apply]
  unfold toTree
  rfl

lemma OBdd.high_reduced {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced → (O.high h).Reduced := by
  intro o
  apply reduced_of_relevant ⟨O.1.heap[j].high, ?_⟩ o
  apply reachable_of_edge
  rw [h]
  exact Edge.high rfl

lemma OBdd.low_reduced {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced → (O.low h).Reduced := by
  intro o
  apply reduced_of_relevant ⟨O.1.heap[j].low, ?_⟩ o
  apply reachable_of_edge
  rw [h]
  exact Edge.low rfl

lemma OBdd.size_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.size' = 1 + (O.low h).size' + (O.high h).size' := by
  simp only [size', Function.comp_apply, toTree_node h]
  rfl

lemma OBdd.evaluate_high_eq_evaluate_low_of_independentOf_root {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    Nary.IndependentOf O.evaluate O.1.heap[j].var → (O.high h).evaluate = (O.low h).evaluate := by
  intro i
  ext I
  trans O.evaluate I
  · rw [i true I]
    rw [evaluate_node'' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
    exact (independentOf_lt_root (O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); simp; rw [h]; simp)⟩) true I
  · rw [i false I]
    rw [evaluate_node'' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
    symm
    exact (independentOf_lt_root (O := O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var  (O := O); simp; rw [h]; simp)⟩) false I

lemma OBdd.evaluate_high_eq_evaluate_set_true {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.high h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var true := by
  ext I
  simp only [Function.comp_apply]
  nth_rw 2 [evaluate_node'' (j := j)]
  beta_reduce
  simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
  have := var_lt_high_var (h := h)
  simp [var] at this
  rw [h] at this
  simp only [toVar_node_eq, Nat.succ_eq_add_one, Fin.getElem_fin, Fin.coe_eq_castSucc] at this
  apply independentOf_lt_root (O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); simp; rw [h]; simp)⟩

lemma OBdd.evaluate_low_eq_evaluate_set_false {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.low h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var false := by
  ext I
  simp only [Function.comp_apply]
  nth_rw 2 [evaluate_node'' (j := j)]
  beta_reduce
  simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have := var_lt_high_var (h := h)
  simp [var] at this
  rw [h] at this
  simp at this
  apply independentOf_lt_root (O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var (O := O); simp; rw [h]; simp)⟩

lemma OBdd.evaluate_high_eq_of_evaluate_eq_and_var_eq' {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
    O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.high ho).evaluate = (U.high hu).evaluate := by
  intro h eq
  rw [evaluate_high_eq_evaluate_set_true, h, eq ,← evaluate_high_eq_evaluate_set_true]

lemma OBdd.evaluate_high_eq_of_evaluate_eq_and_var_eq {n m} {O U : OBdd n m} {j i : Fin m} {ho : O.1.root = node j} {hu : U.1.root = node i} :
    O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.high ho).evaluate = (U.high hu).evaluate := evaluate_high_eq_of_evaluate_eq_and_var_eq'

lemma OBdd.evaluate_low_eq_of_evaluate_eq_and_var_eq' {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := by
  intro h eq
  rw [evaluate_low_eq_evaluate_set_false, h, eq ,← evaluate_low_eq_evaluate_set_false]

lemma OBdd.evaluate_low_eq_of_evaluate_eq_and_var_eq {n m} {O U : OBdd n m} {j i : Fin m} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := evaluate_low_eq_of_evaluate_eq_and_var_eq'

lemma OBdd.not_reduced_of_sim_high_low {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    Similar (O.high h) (O.low h) → ¬ O.Reduced := by
  intro iso R
  apply R.1 O.1.toRelevantPointer
  simp [toRelevantPointer]
  rw [h]
  constructor
  have giso : SimilarRP O ⟨(O.high h).1.root, reachable_of_edge (edge_of_high (h := h) O.1)⟩
                                ⟨(O.low  h).1.root, reachable_of_edge (edge_of_low  (h := h) O.1)⟩ := iso
  exact (symm (R.2 giso))

def OBdd.HIsomorphism (O : OBdd n m) (U : OBdd n' m') :=
  ∃ (f : O.1.RelevantPointer → U.1.RelevantPointer),
    (Function.Bijective f) ∧
    (∀ (p : O.1.RelevantPointer),
       (∀ j, (h : p.1 = node j) → ∃ i hi, f p = ⟨node i, hi⟩
       ∧ O.1.heap[j].var.1 = U.1.heap[i].var.1
       ∧ f ⟨O.1.heap[j].low , Reachable.trans p.2 (reachable_of_edge (h ▸ Edge.low  rfl))⟩ = ⟨U.1.heap[i].low , Reachable.trans hi (reachable_of_edge (Edge.low  rfl))⟩
       ∧ f ⟨O.1.heap[j].high, Reachable.trans p.2 (reachable_of_edge (h ▸ Edge.high rfl))⟩ = ⟨U.1.heap[i].high, Reachable.trans hi (reachable_of_edge (Edge.high rfl))⟩)
     ∧ (∀ b, p.1 = terminal b → ∃   hb, f p = ⟨terminal b, hb⟩))

def OBdd.Isomorphism : OBdd n m → OBdd n m → Prop := HIsomorphism

def OBdd.RelevantIsomorphism (O : OBdd n m) (p q : O.1.RelevantPointer) :=
  Isomorphism ⟨{heap := O.1.heap, root := p.1}, ordered_of_reachable p.2⟩
              ⟨{heap := O.1.heap, root := q.1}, ordered_of_reachable q.2⟩

def OBdd.Reduced' (O : OBdd n m) : Prop
  -- No redundant pointers.
  := NoRedundancy O.1
  -- Isomorphism implies pointer-equality.
   ∧ Subrelation (RelevantIsomorphism O) (InvImage Eq Subtype.val)

/-- Reduced OBDDs are canonical.  -/
theorem OBdd.Canonicity {O : OBdd n m} {U : OBdd n m'} (ho : O.Reduced) (hu : U.Reduced) :
    O.evaluate = U.evaluate → O.HSimilar U := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    cases U_root_def : U.1.root with
    | terminal c =>
      simp only [Similar, HSimilar, InvImage]
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
      absurd hu
      apply not_reduced_of_sim_high_low U_root_def
      apply OBdd.Canonicity (high_reduced hu) (low_reduced hu) this
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
      absurd ho
      apply not_reduced_of_sim_high_low O_root_def
      apply OBdd.Canonicity (high_reduced ho) (low_reduced ho) this
    | node i =>
      simp only [Similar, HSimilar, InvImage]
      rw [toTree_node O_root_def, toTree_node U_root_def]
      simp only [Ordered, DecisionTree.branch.injEq]
      have same_var : O.1.heap[j].var = U.1.heap[i].var := by
        apply eq_iff_le_not_lt.mpr
        constructor
        · apply le_of_not_lt
          intro contra
          have := independentOf_lt_root O ⟨U.1.heap[i].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [O_root_def]; simpa⟩
          rw [h] at this
          simp only [Fin.eta] at this
          simp only [Nary.IndependentOf] at this
          have that : OBdd.Similar (U.high U_root_def) (U.low U_root_def) :=
            OBdd.Canonicity (high_reduced hu) (low_reduced hu) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
          apply hu.1 U.1.toRelevantPointer
          simp [toRelevantPointer]
          rw [U_root_def]
          constructor
          have iso : SimilarRP U ⟨(U.high U_root_def).1.root, reachable_of_edge (edge_of_high (h := U_root_def) U.1)⟩
                                  ⟨(U.low  U_root_def).1.root, reachable_of_edge (edge_of_low  (h := U_root_def) U.1)⟩ := that
          exact (symm (hu.2 iso))
        · intro contra
          have := independentOf_lt_root U ⟨O.1.heap[j].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [U_root_def]; simpa⟩
          rw [← h] at this
          simp only [Ordered, Fin.eta] at this
          simp only [Nary.IndependentOf] at this
          have that : OBdd.Similar (O.high O_root_def) (O.low O_root_def) :=
            OBdd.Canonicity (high_reduced ho) (low_reduced ho) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
          apply ho.1 O.1.toRelevantPointer
          simp [toRelevantPointer]
          rw [O_root_def]
          constructor
          have iso : SimilarRP O ⟨(O.high O_root_def).1.root, reachable_of_edge (edge_of_high (h := O_root_def) O.1)⟩
                                  ⟨(O.low  O_root_def).1.root, reachable_of_edge (edge_of_low  (h := O_root_def) O.1)⟩ := that
          exact (symm (ho.2 iso))
      constructor
      · exact same_var
      · constructor
        · apply OBdd.Canonicity (low_reduced  ho) (low_reduced  hu) (evaluate_low_eq_of_evaluate_eq_and_var_eq'  h same_var)
        · apply OBdd.Canonicity (high_reduced ho) (high_reduced hu) (evaluate_high_eq_of_evaluate_eq_and_var_eq' h same_var)
termination_by O.size' + U.size'
decreasing_by
  simp [size_node U_root_def]; linarith
  simp [size_node O_root_def]; linarith
  all_goals
    simp [size_node O_root_def, size_node U_root_def]; linarith

/-- The only reduced BDD that denotes a constant function is the terminal BDD. -/
theorem OBdd.terminal_of_constant {n m} (O : OBdd n m) :
    O.Reduced → O.evaluate = (fun _ ↦ b) → O.1.root = terminal b := by
  intro R h
  cases O_root_def : O.1.root
  case terminal b' =>
    rcases O with ⟨⟨heap, root⟩, o⟩
    subst O_root_def
    simp only [OBdd.evaluate, Ordered, Function.comp_apply, DecisionTree.evaluate] at h
    unfold toTree at h
    simp only [DecisionTree.evaluate] at h
    apply eq_of_constant_eq (α := Vector Bool n) at h
    simpa
  case node j =>
    exfalso
    refine not_reduced_of_sim_high_low O_root_def ?_ R
    have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
      ext I
      trans b
      · simp [evaluate_high_eq_evaluate_set_true, h]
      · simp [evaluate_low_eq_evaluate_set_false, h]
    exact OBdd.Canonicity (high_reduced R) (low_reduced R) this

theorem OBdd.Canonicity_reverse {O : OBdd n m} {U : OBdd n m'}:
    O.HSimilar U → O.evaluate = U.evaluate := by
  simp_all [evaluate, Function.comp_apply, Similar, HSimilar]

/-- An acyclicity lemma: an edge from `O` to `U` implies that `O` is not reachable from `U`.  -/
lemma OBdd.not_oedge_reachable {n m} {O U : OBdd n m}: OEdge O U → ¬ Reachable O.1.heap U.1.root O.1.root := by
  rintro ⟨same_heap, e⟩ contra
  apply Relation.reflTransGen_iff_eq_or_transGen.mp at contra
  cases contra with
  | inl h =>
    rw [← h] at e
    have : RelevantEdge O.1 O.1.toRelevantPointer O.1.toRelevantPointer := e
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

lemma Pointer.Reachable_iff {M : Vector (Node n m) m } :
  Pointer.Reachable M r p ↔ (r = p ∨ (∃ j, r = .node j ∧ (Pointer.Reachable M M[j].low p ∨ Pointer.Reachable M M[j].high p))) := by
  constructor
  · intro h
    cases Relation.reflTransGen_swap.mp h with
    | refl =>
      left
      rfl
    | tail r e =>
      rename_i q
      right
      cases e with
      | low  hh => rename_i j; exact ⟨j, rfl, .inl (by trans q; rw [hh]; left; exact (Relation.reflTransGen_swap.mpr r))⟩
      | high hh => rename_i j; exact ⟨j, rfl, .inr (by trans q; rw [hh]; left; exact (Relation.reflTransGen_swap.mpr r))⟩
  · intro h
    cases h with
    | inl h => rw [h]; left
    | inr h =>
      rcases h with ⟨j, hj, h⟩
      rw [hj]
      cases h with
      | inl h =>
        apply Relation.reflTransGen_swap.mp
        right
        · apply Relation.reflTransGen_swap.mpr; exact h
        · left; rfl
      | inr h =>
        apply Relation.reflTransGen_swap.mp
        right
        · apply Relation.reflTransGen_swap.mpr; exact h
        · right; rfl

lemma OBdd.reachable_or_eq_low_high {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → (O.1.root = p ∨ (∃ j, ∃ (h : O.1.root = node j), (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p))) := by
  intro hr
  cases Reachable_iff.mp hr with
  | inl => left; assumption
  | inr h =>
    right
    rcases h with ⟨j, O_root_def, hj⟩
    use j, O_root_def
    cases hj with
    | inl hl => left;  simpa [low, Bdd.low]
    | inr hh => right; simpa [high, Bdd.high]

lemma not_isTerminal_of_root_eq_node {n m} {j} {O : OBdd n m} (h : O.1.root = node j) : ¬ O.isTerminal := by
  rintro ⟨b, hb⟩
  rw [h] at hb
  contradiction

def OBdd.OReachable {n m} := Relation.ReflTransGen (@OEdge n m)

lemma OBdd.low_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j}: O.OReachable U → O.OReachable (U.low U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_low

lemma OBdd.high_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j} : O.OReachable U → O.OReachable (U.high U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_high

lemma OBdd.card_RelevantPointer_le {O : OBdd n m} : Fintype.card O.1.RelevantPointer ≤ m + 2 := by
  conv =>
    rhs
    rw [← Fintype.card_fin m]
    rw [← Fintype.card_bool]
  rw [← Fintype.card_sum]
  let emb : O.1.RelevantPointer → Fin m ⊕ Bool := fun
    | ⟨terminal b, _⟩ => .inr b
    | ⟨node j, _⟩ => .inl j
  refine Fintype.card_le_of_embedding ⟨emb, ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  cases x with
  | terminal b =>
    cases y with
    | node j => simp [emb] at h
    | terminal c => simp [emb] at h; simp_rw [h]
  | node j =>
    cases y with
    | node i => simp [emb] at h; simp_rw [h]
    | terminal b => simp [emb] at h

lemma OBdd.card_relevantPointer_eq_one_of_isTerminal {O : OBdd n m} : O.isTerminal → Fintype.card O.1.RelevantPointer = 1 := by
  intro h
  refine Fintype.card_eq_one_iff.mpr ?_
  rcases h with ⟨b, hb⟩
  use ⟨terminal b, by rw [hb]; left⟩
  intro y
  apply Subtype.eq_iff.mpr
  apply (terminal_relevant_iff hb y).mp
  rfl

lemma OBdd.reachable_node_iff {O : OBdd n m} (h : O.1.root = node j) :
  Reachable O.1.heap O.1.root = fun q ↦
    (Reachable O.1.heap O.1.root q ∧ ¬ Reachable O.1.heap (O.low h).1.root q ∧ ¬ Reachable O.1.heap (O.high h).1.root q) ∨
    (Reachable O.1.heap (O.low  h).1.root q ∧ ¬ Reachable O.1.heap (O.high h).1.root q) ∨
    (Reachable O.1.heap (O.high h).1.root q ∧ ¬ Reachable O.1.heap (O.low  h).1.root q) ∨
    (Reachable O.1.heap (O.low  h).1.root q ∧   Reachable O.1.heap (O.high h).1.root q) := by
  ext p
  constructor
  · intro r
    cases instDecidableReachable (O.low h) p with
    | isFalse hf =>
      cases instDecidableReachable (O.high h) p with
      | isFalse hhf =>
        left
        exact ⟨r, hf, hhf⟩
      | isTrue hht =>
        right
        right
        left
        exact ⟨hht, hf⟩
    | isTrue ht =>
      cases instDecidableReachable (O.high h) p with
      | isFalse hhf =>
        right
        left
        exact ⟨ht, hhf⟩
      | isTrue hht =>
        right
        right
        right
        exact ⟨ht, hht⟩
  · intro r
    cases r with
    | inl r => exact r.1
    | inr r =>
      cases r with
      | inl r =>
        trans (O.low h).1.root
        · exact reachable_of_edge (edge_of_low (h := h) O.1)
        · exact r.1
      | inr r =>
        cases r with
        | inl r =>
          trans (O.high h).1.root
          · exact reachable_of_edge (edge_of_high (h := h) O.1)
          · exact r.1
        | inr r =>
          trans (O.high h).1.root
          · exact reachable_of_edge (edge_of_high (h := h) O.1)
          · exact r.2

instance OBdd.instFintypeReachableFromNode (O : OBdd n m) (h : O.1.root = node j) : Fintype {q // (q = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root q ∨ Reachable O.1.heap (O.high h).1.root q))} := by
  convert Subtype.fintype _
  · intro p
    simp only
    cases decEq p O.1.root with
    | isFalse hf =>
      cases instDecidableReachable (O.low h) p with
      | isFalse hhf =>
        cases instDecidableReachable (O.high h) p with
        | isFalse hhhf =>
          apply isFalse
          simp
          exact ⟨hf, hhf, hhhf⟩
        | isTrue hhht =>
          apply isTrue
          right
          right
          assumption
      | isTrue hht =>
        apply isTrue
        right
        left
        assumption
    | isTrue h =>
      apply isTrue
      left
      assumption
  · infer_instance

lemma OBdd.reachable_from_node_iff' {O : OBdd n m} (h : O.1.root = node j) :
    Reachable O.1.heap O.1.root p ↔ p = O.1.root ∨ (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p) := by
  constructor
  · intro r
    cases (Relation.reflTransGen_swap.mp r) with
    | refl => left; rfl
    | tail t e =>
      rename_i q
      right
      rw [h] at e
      cases e with
      | low  l =>
        left
        trans q
        · simp only [low,Bdd.low, l]
          left
        · exact Relation.reflTransGen_swap.mp t
      | high l =>
        right
        trans q
        · simp only [high, Bdd.high, l]
          left
        · exact Relation.reflTransGen_swap.mp t
  · intro r
    cases r with
    | inl r =>
      rw [r]
      left
    | inr r =>
      cases r with
      | inl r =>
        apply Relation.reflTransGen_swap.mpr
        apply Relation.ReflTransGen.tail (Relation.reflTransGen_swap.mpr r)
        simp [Function.swap]
        exact edge_of_low  (h := h)
      | inr r =>
        apply Relation.reflTransGen_swap.mpr
        apply Relation.ReflTransGen.tail (Relation.reflTransGen_swap.mpr r)
        simp [Function.swap]
        exact edge_of_high (h := h)

lemma OBdd.card_reachable_node' {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card {p // Reachable O.1.heap O.1.root p} =
  Fintype.card {p // p = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)} := by
  refine Fintype.card_congr' ?_
  conv =>
    lhs
    arg 1
    ext
    rw [reachable_from_node_iff' h]

lemma OBdd.eq_root_disjoint_reachable_low_or_high {O : OBdd n m} (h : O.1.root = node j) :
    Disjoint
      (· = O.1.root)
      (fun p ↦ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)) := by
  intro P h1 h2 p hp
  have this := h1 p hp
  have that := h2 p hp
  simp_all only
  cases that with
  | inl l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_low l
  | inr l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_high l

lemma OBdd.card_reachable_node {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card { q // Reachable O.1.heap O.1.root q } =
  1 + Fintype.card { q // Reachable (O.low h).1.heap (O.low h).1.root q ∨ Reachable (O.high h).1.heap (O.high h).1.root q } := by
  rw [card_reachable_node' h]
  rw [@Fintype.card_subtype_or_disjoint _ _ _ (eq_root_disjoint_reachable_low_or_high h) ..]
  · simp only [Fintype.card_unique, low_heap_eq_heap, add_right_inj]
    apply @Fintype.card_congr' ..
    · apply instFintypeEitherRelevantPointer (O.low h) (O.high h); simp
    · simp
  · exact Fintype.subtypeEq O.1.root

lemma Bdd.ordered_of_low_high_ordered {B : Bdd n m} (h : B.root = node j):
    (B.low h).Ordered → B.var < (B.low h).var → (B.high h).Ordered → B.var < (B.high h).var → Ordered B := by
  rintro hl1 hl2 hh1 hh2 ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only [RelevantEdge] at hxy
  simp only [RelevantMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  cases Relation.reflTransGen_swap.mp hx
  case refl        =>
    rw [h] at hxy
    rw [h]
    cases hxy with
    | low heq =>
      simp only [var, low_heap_eq_heap, low_root_eq_low, heq, h] at hl2
      exact hl2
    | high heq =>
      simp only [var, high_heap_eq_heap, high_root_eq_high, heq, h] at hh2
      exact hh2
  case tail p r e =>
    rw [h] at e
    cases e with
    | low heq =>
      rw [← low_heap_eq_heap (h := h)]
      rw [← low_heap_eq_heap (h := h)] at hxy
      rw [← low_heap_eq_heap (h := h)] at r
      rw [← heq] at r
      have := @hl1 ⟨x, Relation.reflTransGen_swap.mpr r⟩ ⟨y, by trans x; exact Relation.reflTransGen_swap.mpr r; right; left; exact hxy⟩ hxy
      exact this
    | high heq =>
      rw [← high_heap_eq_heap (h := h)]
      rw [← high_heap_eq_heap (h := h)] at hxy
      rw [← high_heap_eq_heap (h := h)] at r
      rw [← heq] at r
      have := @hh1 ⟨x, Relation.reflTransGen_swap.mpr r⟩ ⟨y, by trans x; exact Relation.reflTransGen_swap.mpr r; right; left; exact hxy⟩ hxy
      exact this

lemma Bdd.ordered_of_ordered_heap_not_reachable_set (O : OBdd n m) :
    ∀ i N, ¬ Reachable O.1.heap O.1.root (node i) → Ordered ⟨O.1.heap.set i N, O.1.root⟩ := by
  intro i N unr
  cases O_root_def : O.1.root with
  | terminal b => exact Ordered_of_terminal
  | node j =>
    have : i ≠ j := by
      intro contra
      rw [contra] at unr
      rw [O_root_def] at unr
      apply unr
      left
    apply ordered_of_low_high_ordered rfl
    · simp only [low, Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      have that := ordered_of_ordered_heap_not_reachable_set (O.low O_root_def) i N
      simp only [OBdd.low_heap_eq_heap] at that
      simp only [OBdd.low_root_eq_low] at that
      apply that
      intro contra
      apply unr
      trans O.1.heap[j].low
      · right
        left
        rw [O_root_def]
        left
        rfl
      · exact contra
    · simp only [Nat.succ_eq_add_one, var, low]
      simp only [low, Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      rw [toVar_heap_set this]
      have that : toVar O.1.heap (node j) < toVar O.1.heap O.1.heap[j].low := by
        exact @O.2 ⟨node j, (by rw [O_root_def]; left)⟩
                   ⟨O.1.heap[j].low, (by trans (node j); rw [O_root_def]; left; right; left; left; rfl)⟩
                   (by left; rfl)
      convert that using 1
      cases low_def : O.1.heap[j].low with
      | terminal bl => simp
      | node jl =>
        simp only [toVar]
        simp only [Nat.succ_eq_add_one, Ordered, Fin.coe_eq_castSucc, Fin.castSucc_inj]
        simp only [Fin.getElem_fin]
        rw [Vector.getElem_set_ne i.2 jl.2]
        intro contra
        rcases i with ⟨iv, ih⟩
        simp at contra
        simp_rw [contra] at unr
        apply unr
        trans (node j)
        · rw [O_root_def]; left
        · rw [← low_def]; right; left; left; rfl
    · simp only [high, Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      have that := ordered_of_ordered_heap_not_reachable_set (O := (O.high O_root_def)) i N
      simp only [OBdd.high_heap_eq_heap] at that
      simp only [OBdd.high_root_eq_high] at that
      apply that
      intro contra
      apply unr
      trans O.1.heap[j].high
      · right
        left
        rw [O_root_def]
        right
        rfl
      · exact contra
    · simp only [Nat.succ_eq_add_one, var, high]
      simp only [high, Fin.getElem_fin]
      simp only [Vector.getElem_set_ne i.2 j.2 (by simp_all [Fin.val_ne_of_ne this])]
      rw [toVar_heap_set this]
      have that : toVar O.1.heap (node j) < toVar O.1.heap O.1.heap[j].high := by
        exact @O.2 ⟨node j, (by rw [O_root_def]; left)⟩
                   ⟨O.1.heap[j].high, (by trans (node j); rw [O_root_def]; left; right; left; right; rfl)⟩
                   (by right; rfl)
      convert that using 1
      cases high_def : O.1.heap[j].high with
      | terminal bh => simp
      | node bh =>
        simp only [toVar]
        simp only [Nat.succ_eq_add_one, Ordered, Fin.coe_eq_castSucc, Fin.castSucc_inj]
        simp only [Fin.getElem_fin]
        rw [Vector.getElem_set_ne i.2 bh.2]
        intro contra
        rcases i with ⟨iv, ih⟩
        simp at contra
        simp_rw [contra] at unr
        apply unr
        trans (node j)
        · rw [O_root_def]; left
        · rw [← high_def]; right; left; right; rfl
termination_by O

lemma Pointer.mayPrecede_of_reachable {B : Bdd n m} :
    B.Ordered → Reachable B.heap B.root p → Pointer.toVar B.heap B.root ≤ Pointer.toVar B.heap p := by
  intro ho hp
  induction hp with
  | refl => simp
  | tail r e ih =>
    rename_i b c
    trans toVar B.heap b
    exact ih
    suffices s : B.RelevantMayPrecede ⟨b, r⟩ ⟨c, by trans b; exact r; exact reachable_of_edge e⟩ by
      simp only [RelevantMayPrecede, MayPrecede, Nat.succ_eq_add_one] at s
      omega
    apply ho
    exact e

lemma OBdd.reduced_var_dependent {O : OBdd n m} {p : Fin n} :
    O.Reduced → (∀ i : Fin p, Nary.IndependentOf (O.evaluate) ⟨i.1, by omega⟩) → p ≤ O.1.var := by
  intro hr hp
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Bdd.var, Bdd.Ordered.eq_1, O_root_def, Pointer.toVar_terminal_eq, Fin.natCast_eq_last]
    exact Fin.le_last p.castSucc
  | node j =>
    by_contra c
    simp only [not_le] at c
    have := hp ⟨O.1.var, by aesop⟩
    simp only [Nat.succ_eq_add_one] at this
    suffices s : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate by
      absurd hr
      apply not_reduced_of_sim_high_low O_root_def
      apply OBdd.Canonicity (OBdd.high_reduced hr) (OBdd.low_reduced hr) s
    ext I
    trans O.evaluate I
    · simp only [Bdd.Ordered.eq_1, Bdd.var, O_root_def, Pointer.toVar_node_eq, Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.eta] at this
      have := this true I
      rw [this]
      rw [OBdd.evaluate_node'' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [↓reduceIte]
      suffices s : Nary.IndependentOf (O.high O_root_def).evaluate O.1.heap[j.1].var by rw [← s true I]
      refine independentOf_lt_root (O.high O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_high_var
      simp [O_root_def]
    · symm
      simp only [Bdd.Ordered.eq_1, Bdd.var, O_root_def, Pointer.toVar_node_eq, Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.eta] at this
      have := this false I
      rw [this]
      rw [OBdd.evaluate_node'' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [Bool.false_eq_true, ↓reduceIte]
      suffices s : Nary.IndependentOf (O.low O_root_def).evaluate O.1.heap[j.1].var by rw [s false I]
      refine independentOf_lt_root (O.low O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_low_var
      simp [O_root_def]

def Bdd.usesVar (B : Bdd n m) (i : Fin n) := ∃ j, Reachable B.heap B.root (node j) ∧ B.heap[j].var = i

lemma Bdd.usesVar_of_high_usesVar {B : Bdd n m} {h : B.root = node j} :
    (B.high h).usesVar i → B.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (B.high h).root
    · apply reachable_of_edge
      have := edge_of_high (h := h)
      simp_all
    · exact h1
  · simp_all [high_heap_eq_heap]

lemma Bdd.usesVar_of_low_usesVar {B : Bdd n m} {h : B.root = node j} :
    (B.low h).usesVar i → B.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (B.low h).root
    · apply reachable_of_edge
      have := edge_of_low (h := h)
      simp_all
    · exact h1
  · simp_all [low_heap_eq_heap]

lemma OBdd.usesVar_of_high_usesVar {O : OBdd n m} {h : O.1.root = node j} :
    (O.high h).1.usesVar i → O.1.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (O.high h).1.root
    · apply reachable_of_edge
      have := oedge_of_high (h := h)
      simp [OEdge] at this
      assumption
    · exact h1
  · simp_all

lemma OBdd.usesVar_of_low_usesVar {O : OBdd n m} {h : O.1.root = node j} :
    (O.low h).1.usesVar i → O.1.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (O.low h).1.root
    · apply reachable_of_edge
      have := oedge_of_low (h := h)
      simp [OEdge] at this
      assumption
    · exact h1
  · simp_all

lemma OBdd.dependsOn_of_usesVar_of_reduced {O : OBdd n m} :
    O.Reduced → Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var = i → ∃ v : Vector Bool n, O.evaluate v ≠ O.evaluate (v.set i true) := by
  intro hr hj hi
  rcases O_def : O with ⟨⟨heap, root⟩, o⟩
  simp_all only
  have hr' : O.Reduced := by
    rw [← O_def] at hr
    exact hr
  cases Relation.reflTransGen_swap.mp hj with
  | refl =>
    rw [← O_def]
    rw [evaluate_node'' (by rw [O_def])]
    rw [show O.1.heap = heap by rw [O_def], hi]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, Bool.false_eq_true, ↓reduceIte, ne_eq]
    rw [← not_forall]
    intro contra
    apply not_reduced_of_sim_high_low (show O.1.root = node j by rw [O_def])
    · apply OBdd.Canonicity
      · exact high_reduced hr'
      · exact low_reduced hr'
      · ext x
        have that := contra (x.set i false)
        simp only [Vector.getElem_set_self, Bool.false_eq_true, ↓reduceIte, Vector.set_set] at that
        calc _
          _ = (O.high (by rw [O_def])).evaluate (x.set i true) := by
            have hhi : i.1 < (O.high (by rw [O_def])).var := by
              rw [← hi]
              simp_rw [show heap = O.1.heap by rw [O_def]]
              rw [show O.1.heap[j].var = O.var by simp [O_def]]
              apply var_lt_high_var
            apply independentOf_lt_root (O.high (by rw [O_def])) ⟨i.1, hhi⟩
          _ = (O.low (by rw [O_def])).evaluate (x.set i false) := by symm; assumption
          _ = _ := by
            symm
            have hhi : i.1 < (O.low (by rw [O_def])).var := by
              rw [← hi]
              simp_rw [show heap = O.1.heap by rw [O_def]]
              rw [show O.1.heap[j].var = O.var by simp [O_def]]
              apply var_lt_low_var
            apply independentOf_lt_root (O.low (by rw [O_def])) ⟨i.1, hhi⟩
    · exact hr'
  | tail r e =>
    rename_i p
    apply Relation.reflTransGen_swap.mpr at r
    cases root with
    | terminal _ => contradiction
    | node jr =>
      cases e with
      | low  he =>
        rw [show heap = O.1.heap by rw [O_def]] at hj
        have := OBdd.dependsOn_of_usesVar_of_reduced (low_reduced (h := by rw [O_def]) hr') (by simp_all [low_heap_eq_heap, low, Bdd.low]; exact r) (i := i) (by rw [low_heap_eq_heap, O_def]; exact hi)
        rcases this with ⟨v, hv⟩
        rw [← O_def]
        use v.set heap[jr].var false
        contrapose hv
        simp only [Fin.getElem_fin, ne_eq, Decidable.not_not] at hv
        simp only [Fin.getElem_fin, ne_eq, Decidable.not_not]
        calc _
          _ = O.evaluate (v.set (heap[jr.1].var.1) false) := by
            rw [evaluate_low_eq_evaluate_set_false]
            simp [O_def]
          _ = O.evaluate ((v.set (heap[jr.1].var.1) false).set i true) := hv
          _ = O.evaluate ((v.set i true).set (heap[jr.1].var.1) false) := by
            rw [Vector.set_comm]
            apply ne_of_lt
            have := var_lt_low_var (O := O) (h := (by rw [O_def]))
            simp only [var, Nat.succ_eq_add_one, Bdd.var, Ordered, O_def, toVar_node_eq,
              Fin.coe_eq_castSucc, Fin.coe_castSucc, low, Bdd.low] at this
            rw [he] at this
            simp only [Fin.getElem_fin] at this
            apply lt_of_lt_of_le this
            rw [← hi]
            rw [show heap[j].var = (toVar heap (node j)).1 by simp [toVar]]
            let B : Bdd n m := ⟨heap, p⟩
            rw [show heap = B.heap by rfl]
            rw [show p = B.root by rfl]
            apply mayPrecede_of_reachable
            · simp only [B]
              rw [← he]
              apply ordered_of_low_edge
              exact o
            · exact r
          _ = (O.low (by rw [O_def])).evaluate (v.set i true) := by
            symm
            rw [evaluate_low_eq_evaluate_set_false]
            simp [O_def]
      | high he =>
        rw [show heap = O.1.heap by rw [O_def]] at hj
        have := OBdd.dependsOn_of_usesVar_of_reduced (high_reduced (h := by rw [O_def]) hr') (by simp_all [high_heap_eq_heap, high, Bdd.high]; exact r) (i := i) (by rw [high_heap_eq_heap, O_def]; exact hi)
        rcases this with ⟨v, hv⟩
        rw [← O_def]
        use v.set heap[jr].var true
        contrapose hv
        simp only [Fin.getElem_fin, ne_eq, Decidable.not_not] at hv
        simp only [Fin.getElem_fin, ne_eq, Decidable.not_not]
        calc _
          _ = O.evaluate (v.set (heap[jr.1].var.1) true) := by
            rw [evaluate_high_eq_evaluate_set_true]
            simp [O_def]
          _ = O.evaluate ((v.set (heap[jr.1].var.1) true).set i true) := hv
          _ = O.evaluate ((v.set i true).set (heap[jr.1].var.1) true) := by
            rw [Vector.set_comm]
            apply ne_of_lt
            have := var_lt_high_var (O := O) (h := (by rw [O_def]))
            simp only [var, Nat.succ_eq_add_one, Bdd.var, Ordered, O_def, toVar_node_eq,
              Fin.coe_eq_castSucc, Fin.coe_castSucc, high, Bdd.high] at this
            rw [he] at this
            simp only [Fin.getElem_fin] at this
            apply lt_of_lt_of_le this
            rw [← hi]
            rw [show heap[j].var = (toVar heap (node j)).1 by simp [toVar]]
            let B : Bdd n m := ⟨heap, p⟩
            rw [show heap = B.heap by rfl]
            rw [show p = B.root by rfl]
            apply mayPrecede_of_reachable
            · simp only [B]
              rw [← he]
              apply ordered_of_high_edge
              exact o
            · exact r
          _ = (O.high (by rw [O_def])).evaluate (v.set i true) := by
            symm
            rw [evaluate_high_eq_evaluate_set_true]
            simp [O_def]
termination_by O

lemma OBdd.usesVar_of_dependsOn {O : OBdd n m} {i : Fin n} :
    O.evaluate v ≠ O.evaluate (v.set i b) → O.1.usesVar i := by
  intro h
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp [evaluate_terminal' O_root_def] at h
  | node j =>
    cases decEq O.1.heap[j].var i with
    | isFalse hf =>
      cases lt_or_gt_of_ne hf with
      | inl hl =>
        rw [evaluate_node'' O_root_def] at h
        simp only at h
        split at h
        next hh =>
          simp only [Fin.getElem_fin] at h
          simp only [Fin.getElem_fin] at hh
          simp only [Fin.getElem_fin] at hf
          simp_rw [Vector.getElem_set_ne (xs := v) (i := i.1) (j := O.1.heap[j.1].var) (by omega) (by omega) (by omega)] at h
          rw [hh] at h
          simp only [↓reduceIte] at h
          exact usesVar_of_high_usesVar (usesVar_of_dependsOn h)
        next hh =>
          simp only [Bool.not_eq_true] at hh
          simp only [Fin.getElem_fin] at h
          simp only [Fin.getElem_fin] at hh
          simp only [Fin.getElem_fin] at hf
          simp_rw [Vector.getElem_set_ne (xs := v) (i := i.1) (j := O.1.heap[j.1].var) (by omega) (by omega) (by omega)] at h
          rw [hh] at h
          simp only [Bool.false_eq_true, ↓reduceIte, ne_eq] at h
          exact usesVar_of_low_usesVar (usesVar_of_dependsOn h)
      | inr hr =>
        have := (independentOf_lt_root O ⟨i.1, by simp [var, Bdd.var, O_root_def]; omega⟩) b v
        contradiction
    | isTrue ht =>
      use j
      constructor
      · rw [O_root_def]; left
      · exact ht
termination_by O

lemma OBdd.usesVar_iff_dependsOn_of_reduced {O : OBdd n m} :
    O.Reduced → (O.1.usesVar i ↔ Nary.DependsOn O.evaluate i) := by
  intro hr
  constructor
  · rintro ⟨j, hj, hi⟩
    simp only [Nary.DependsOn, Nary.IndependentOf, not_forall]
    use true
    apply OBdd.dependsOn_of_usesVar_of_reduced hr hj hi
  · intro nind
    simp only [Nary.DependsOn, Nary.IndependentOf, not_forall] at nind
    rcases nind with ⟨b, v, hbv⟩
    exact usesVar_of_dependsOn hbv

lemma OBdd.usesVar_iff (i : Fin n) (O : OBdd n m) : O.1.usesVar i ↔ (∃ j, ∃ (hj : O.1.root = node j), (O.1.heap[j].var = i ∨ ((O.low hj).1.usesVar i ∨ (O.high hj).1.usesVar i))) := by
  constructor
  · rintro ⟨j, hj, hi⟩
    rcases O_def : O with ⟨⟨heap, root⟩, o⟩
    simp_all
    cases root with
    | terminal _ =>
      cases Relation.ReflTransGen.swap hj with
      | tail _ e => exact False.elim (not_terminal_edge e)
    | node j' =>
      use j', rfl
      cases Relation.ReflTransGen.swap hj with
      | refl => left; assumption
      | tail r e =>
        cases e with
        | low hl =>
          right
          left
          use j
          simp only [Fin.getElem_fin] at hl
          simp only [low_heap_eq_heap, Fin.getElem_fin, low, Bdd.low, hl]
          constructor
          · exact Relation.ReflTransGen.swap r
          · exact hi
        | high hh =>
          right
          right
          use j
          simp only [Fin.getElem_fin] at hh
          simp only [high_heap_eq_heap, Fin.getElem_fin, high, Bdd.high, hh]
          constructor
          · exact Relation.ReflTransGen.swap r
          · exact hi
  · rintro ⟨j, hj, h⟩
    cases h with
    | inl h =>
      use j
      rw [hj]
      constructor
      · left
      · exact h
    | inr h =>
      cases h with
      | inl h => exact usesVar_of_low_usesVar h
      | inr h => exact usesVar_of_high_usesVar h

lemma OBdd.toTree_usesVar {O : OBdd n m} : O.1.usesVar i ↔ O.toTree.usesVar i := by
  constructor
  · rw [OBdd.usesVar_iff]
    rw [DecisionTree.usesVar_iff]
    rintro ⟨j, hj, h⟩
    rw [toTree_node hj]
    use O.1.heap[j].var, (O.low hj).toTree, (O.high hj).toTree
    cases h with
    | inl h => simp_all
    | inr h =>
      simp only [Fin.getElem_fin, true_and]
      right
      cases h with
      | inl h =>
        left
        rw [toTree_usesVar (O := (O.low hj))] at h
        assumption
      | inr h =>
        right
        rw [toTree_usesVar (O := (O.high hj))] at h
        assumption
  · intro h
    cases O_root_def : O.1.root with
    | terminal _ =>
      rw [toTree_terminal' O_root_def] at h
      contradiction
    | node j =>
      rw [DecisionTree.usesVar_iff] at h
      rcases h with ⟨i', l, h, h1, h2⟩
      rw [toTree_node O_root_def] at h1
      injection h1 with ha hl hh
      cases h2 with
      | inl h2 =>
        use j
        constructor
        · rw [O_root_def]; left
        · simp_all
      | inr h2 =>
        cases h2 with
        | inl h2 =>
          rw [← hl, ← toTree_usesVar] at h2
          exact usesVar_of_low_usesVar h2
        | inr h2 =>
          rw [← hh, ← toTree_usesVar] at h2
          exact usesVar_of_high_usesVar h2
termination_by O

lemma OBdd.evaluate_eq_of_forall_usesVar {O : OBdd n m} {I J : Vector Bool n} :
    (∀ i, O.1.usesVar i → I[i] = J[i]) → O.evaluate I = O.evaluate J := by
  intro h
  apply Nary.eq_of_forall_dependency_getElem_eq
  rintro ⟨i, hi⟩
  apply h
  simp only [Nary.DependsOn, Nary.IndependentOf, not_forall] at hi
  rcases hi with ⟨b, v, hbv⟩
  apply usesVar_of_dependsOn hbv

-- FIXME: Optimize.
instance OBdd.instDecidableUsesVar {O : OBdd n m} : DecidablePred O.1.usesVar := by
  intro i
  simp [usesVar]
  infer_instance

lemma Pointer.eq_terminal_of_reachable : Pointer.Reachable w (.terminal b) p → p = (.terminal b) := by
  intro h
  cases Relation.reflTransGen_swap.mp h with
  | refl => rfl
  | tail => contradiction

lemma Bdd.terminal_of_zero_vars {B : Bdd n m} : n = 0 → ∃ b, B.root = .terminal b := by
  intro h
  subst h
  cases hr : B.root with
  | terminal b => exact ⟨b, rfl⟩
  | node j => exact False.elim (Nat.not_lt_zero _ B.heap[j].var.2)

lemma Bdd.terminal_of_zero_heap {B : Bdd n m} : m = 0 → ∃ b, B.root = .terminal b := by
  intro h
  subst h
  cases hr : B.root with
  | terminal b => exact ⟨b, rfl⟩
  | node j => exact False.elim (Nat.not_lt_zero _ j.2)

lemma Pointer.toVar_lt_of_trans_edge_of_ordered :
    Bdd.Ordered ⟨M, x⟩ → Relation.TransGen (Edge M) x y → x.toVar M < y.toVar M := by
  intro h1 h2
  induction h2 with
  | single e =>
    have := h1 (relevantEdge_of_edge_of_reachable e .refl)
    simp_all
  | tail r e t =>
    have := h1 (relevantEdge_of_edge_of_reachable e (Relation.TransGen.to_reflTransGen r))
    simp_all only [Nat.succ_eq_add_one, RelevantMayPrecede, MayPrecede, gt_iff_lt]
    omega

lemma baz (op : Bool → Bool → Bool) (c bt bt' bf bf' : Bool) :
    op (if c then bt else bf) (if c then bt' else bf') = (if c then (op bt bt') else (op bf bf')) := by
  cases c <;> simp

def Pointer.equiv (p : Pointer m) (p' : Pointer m') :=
  (∀ b, p = .terminal b → p' = .terminal b) ∧ (∀ j, p = .node j → ∃ (j' : Fin m'), p' = .node j' ∧ j.1 = j'.1)

lemma Pointer.equiv_refl (p : Pointer m) : p.equiv p := by
  simp only [Pointer.equiv]
  constructor
  · intro b hb
    exact hb
  · intro j hj
    use j

lemma Pointer.equiv_symm {p : Pointer m} : p.equiv q → q.equiv p := by
  simp only [Pointer.equiv]
  simp_all only [Bool.forall_bool, and_imp]
  intro h1 h2 h3
  constructor
  · constructor
    · intro hq
      cases p with
      | terminal b =>
        cases b with
        | false => rfl
        | true => rw [h2 rfl] at hq; simp_all only [terminal.injEq, Bool.true_eq_false]
      | node _ =>
        rcases (h3 _ rfl) with ⟨_, hc⟩
        rw [hc.1] at hq; contradiction
    · intro hq
      cases p with
      | terminal b =>
        cases b with
        | true => rfl
        | false => rw [h1 rfl] at hq; simp_all only [terminal.injEq, Bool.true_eq_false]
      | node _ =>
        rcases (h3 _ rfl) with ⟨_, hc⟩
        rw [hc.1] at hq; contradiction
  · intro j hj
    cases p with
    | terminal b =>
      cases b with
      | false => rw [h1 rfl] at hj; contradiction
      | true => rw [h2 rfl] at hj; contradiction
    | node j' =>
      rcases h3 j' rfl with ⟨j'', hj1, hj2⟩
      rw [hj1] at hj
      injection hj with heq
      subst heq
      use j'
      simp [hj2]

def Node.equiv (N : Node n m) (N' : Node n' m') :=
  N.var.1 = N'.var.1 ∧ Pointer.equiv N.low N'.low ∧ Pointer.equiv N.high N'.high

lemma Node.equiv_refl (N : Node n m) : N.equiv N := by
  simp only [Node.equiv]
  simp
  constructor
  · exact Pointer.equiv_refl N.low
  · exact Pointer.equiv_refl N.high

lemma Node.equiv_symm : Node.equiv N M → Node.equiv M N := by
  simp only [Node.equiv]
  simp_all
  intro h1 h2 h3
  constructor
  · exact Pointer.equiv_symm h2
  · exact Pointer.equiv_symm h3

lemma Bdd.ordered_of_ordered_heap_all_reachable_eq (O : OBdd n m) (B : Bdd n m') :
    (∀ j : Fin m', Reachable B.heap B.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] B.heap[j]) →
    (∀ j, B.root = .node j → ∃ hj, O.1.root = .node ⟨j.1, hj⟩) →
    Ordered B := by
  intro h1 h2
  cases B_root_def : B.root with
  | terminal b => exact Ordered_of_terminal' B_root_def
  | node j =>
    rcases h2 _ B_root_def with ⟨hj1', hj2'⟩
    apply ordered_of_low_high_ordered B_root_def
    · apply ordered_of_ordered_heap_all_reachable_eq (O.low hj2')
      · intro jj hrjj
        simp only [low_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact edge_of_low B
      · intro jl B_low_def
        simp only [OBdd.low, Bdd.low, Fin.getElem_fin]
        rcases h1 jl (.tail .refl (by rw [← B_low_def]; exact edge_of_low _)) with ⟨hjl1, _⟩
        rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
        rcases Pointer.equiv_symm hj3 with ⟨hj31, hj32⟩
        use hjl1
        simp only [Bdd.low] at B_low_def
        rcases hj32 _ B_low_def with ⟨j', hj1', hj2'⟩
        rw [hj1']
        simp only [node.injEq]
        exact Fin.eq_mk_iff_val_eq.mpr (id (Eq.symm hj2'))
    · rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
      have := OBdd.var_lt_low_var (O := O) (h := hj2')
      simp_all [OBdd.var, Bdd.var, OBdd.low, Bdd.low]
      apply Fin.lt_iff_val_lt_val.mpr
      simp only [Fin.coe_castSucc]
      have that : (toVar B.heap B.heap[j.1].low).1 = (toVar O.1.heap O.1.heap[j.1].low).1 := by
        rcases Pointer.equiv_symm hj3 with ⟨hj31, hj32⟩
        cases hl : B.heap[↑j].low with
        | terminal b =>
          simp [hj31 b hl]
        | node jl =>
          rcases hj32 jl hl with ⟨jl', hjl1', hjl2'⟩
          rw [hjl1']
          simp only [Nat.succ_eq_add_one, toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc,
            Fin.coe_castSucc]
          simp_rw [← hjl2']
          rcases h1 jl (by rw [← hl]; exact reachable_of_edge (.low rfl)) with ⟨hs1, hs2, _, _⟩
          exact symm hs2
      rw [that]
      exact this
    · apply ordered_of_ordered_heap_all_reachable_eq (O.high hj2')
      · intro jj hrjj
        simp only [high_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact edge_of_high B
      · intro jl B_high_def
        simp only [OBdd.high, Bdd.high, Fin.getElem_fin]
        rcases h1 jl (.tail .refl (by rw [← B_high_def]; exact edge_of_high _)) with ⟨hjl1, _⟩
        rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
        rcases Pointer.equiv_symm hj4 with ⟨hj41, hj42⟩
        use hjl1
        simp only [Bdd.high] at B_high_def
        rcases hj42 _ B_high_def with ⟨j', hj1', hj2'⟩
        rw [hj1']
        simp only [node.injEq]
        exact Fin.eq_mk_iff_val_eq.mpr (id (Eq.symm hj2'))
    · rcases h1 j (by rw [← B_root_def]; left) with ⟨hj1, hj2, hj3, hj4⟩
      have := OBdd.var_lt_high_var (O := O) (h := hj2')
      simp_all [OBdd.var, Bdd.var, OBdd.high, Bdd.high]
      apply Fin.lt_iff_val_lt_val.mpr
      simp only [Fin.coe_castSucc]
      have that : (toVar B.heap B.heap[j.1].high).1 = (toVar O.1.heap O.1.heap[j.1].high).1 := by
        rcases Pointer.equiv_symm hj4 with ⟨hj41, hj42⟩
        cases hl : B.heap[↑j].high with
        | terminal b =>
          simp [hj41 b hl]
        | node jl =>
          rcases hj42 jl hl with ⟨jl', hjl1', hjl2'⟩
          rw [hjl1']
          simp only [Nat.succ_eq_add_one, toVar_node_eq, Fin.getElem_fin, Fin.coe_eq_castSucc,
            Fin.coe_castSucc]
          simp_rw [← hjl2']
          rcases h1 jl (by rw [← hl]; exact reachable_of_edge (.high rfl)) with ⟨hs1, hs2, _, _⟩
          exact symm hs2
      rw [that]
      exact this
termination_by O

lemma OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.toTree = U.toTree := by
  intro h1 h2
  cases U_root_def : U.1.root with
  | terminal b =>
    simp only [Pointer.equiv] at h2
    have := h2.1 b U_root_def
    simp_all [OBdd.toTree_terminal']
  | node j =>
    simp only [Pointer.equiv] at h2
    have := h2.2 j U_root_def
    rcases this with ⟨j', hj', hjj'⟩
    rw [OBdd.toTree_node U_root_def]
    rw [OBdd.toTree_node hj']
    have := h1 j (by simp [U_root_def]; left)
    rcases this with ⟨hj, hev, hel, heh⟩
    congr 1
    · simp_all [hjj']; apply Fin.eq_of_val_eq; exact hev
    · apply toTree_eq_toTree_of_ordered_heap_all_reachable_eq
      · intro jj hrjj
        simp only [low_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact oedge_of_low.2
      · simp_all [OBdd.low, Bdd.low]
        exact Pointer.equiv_symm hel
    · apply toTree_eq_toTree_of_ordered_heap_all_reachable_eq
      · intro jj hrjj
        simp only [high_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact oedge_of_high.2
      · simp_all [OBdd.high, Bdd.high]
        exact Pointer.equiv_symm heh
termination_by O

lemma OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.evaluate = U.evaluate := by
  intro h1 h2
  ext I
  simp only [OBdd.evaluate, Function.comp_apply]
  rw [toTree_eq_toTree_of_ordered_heap_all_reachable_eq O U h1 h2]


namespace RawBdd

def RawPointer := Bool ⊕ Nat

structure RawNode (n) where
  va : Fin n
  lo : RawPointer
  hi : RawPointer

def RawPointer.Bounded (m : Nat) (p : RawPointer) := ∀ {i}, p = .inr i → i < m

def RawPointer.bounded_of_le {p : RawPointer} (hm : p.Bounded m) (h : m ≤ m') : p.Bounded m' := by
  intro i hi
  cases hp : p with
  | inl val => simp_all
  | inr val =>
    have := hm hp
    simp_all
    injection hi with heq
    subst heq
    omega

def RawPointer.cook (p : RawPointer) (h : p.Bounded m) : Pointer m :=
  match p with
  | .inl b => .terminal b
  | .inr i => .node ⟨i, h rfl⟩

lemma RawPointer.cook_equiv {h1 : RawPointer.Bounded m1 p} {h2 : RawPointer.Bounded m2 p} : Pointer.equiv (RawPointer.cook p h1) (RawPointer.cook p h2) := by
  simp only [Pointer.equiv]
  constructor
  · intro b hb
    cases p <;> simp_all [RawPointer.cook]
  · intro j hj
    cases p with
    | inl val => contradiction
    | inr val =>
      simp only [Bounded] at h1 h2
      simp only [cook, Pointer.node.injEq] at hj
      rw [Fin.eq_mk_iff_val_eq] at hj
      simp only at hj
      subst hj
      use ⟨j.1, h2 rfl⟩
      simp [RawPointer.cook]

def RawPointer.fromPointer : Pointer m → RawPointer
  | .terminal b => .inl b
  | .node j => .inr j.1

def RawNode.Bounded (m : Nat) (N : RawNode n) := N.lo.Bounded m ∧ N.hi.Bounded m

def RawNode.bounded_of_le {N : RawNode n} (hm : N.Bounded m) (h : m ≤ m') : N.Bounded m' :=
  ⟨RawPointer.bounded_of_le hm.1 h, RawPointer.bounded_of_le hm.2 h⟩

def RawNode.cook (N : RawNode n) (h : N.Bounded m) : Node n m := ⟨N.va, N.lo.cook h.1, N.hi.cook h.2⟩

lemma RawNode.cook_equiv : Node.equiv (RawNode.cook N h1) (RawNode.cook N h2) := by
  simp only [Node.equiv]
  constructor
  · rfl
  · rcases h1 with ⟨h11, h12⟩
    rcases h2 with ⟨h21, h22⟩
    constructor
    · apply RawPointer.cook_equiv <;> assumption
    · apply RawPointer.cook_equiv <;> assumption

def cook_heap (v : Vector (RawNode n) c) (hh : ∀ i : Fin c, v[i].Bounded i) : Vector (Node n c) c :=
  Vector.ofFn (fun i ↦ v[i].cook (RawNode.bounded_of_le (hh i) (by omega)))

def toVar_or (M : Vector (Node n m) m) : Pointer m → Nat → Nat
  | .terminal _, i => i
  | .node j, _     => M[j].var


lemma cook_low {rn : RawNode n} {h1} {h2} : rn.lo.cook (m := m) h1 = (rn.cook h2).low := rfl

lemma cook_high {rn : RawNode n} {h1} {h2} : rn.hi.cook (m := m) h1 = (rn.cook h2).high := rfl

lemma cook_inj {p q : RawPointer} {hp} {hq} : p.cook (m := m) hp = q.cook hq → p = q := by
  intro h
  cases p <;> cases q <;> simp_all [RawPointer.cook]

lemma cook_aux {p : RawPointer} {h1} {h2} : p.cook h1 = .node j → p.cook h2 = .node ⟨j, hj⟩ := by
  intro h
  cases p with
  | inl val => simp_all [RawPointer.cook]
  | inr val =>
    simp_all [RawPointer.cook]
    rw [Fin.eq_mk_iff_val_eq] at h
    exact h

private lemma push_ordered_aux {v : Vector (RawNode n) m} {h0} {h2} :
    Pointer.Reachable (cook_heap (v.push N) h2) (RawPointer.cook p h3) q →
    ∀ j, q = .node j →
    ∃ hj : j.1 < m, Pointer.Reachable (cook_heap v h0) (p.cook h1) (.node ⟨j.1, hj⟩) := by
  intro h
  induction h with
  | refl =>
    intro i hi
    cases p with
    | inl val => contradiction
    | inr val =>
      simp [RawPointer.cook] at hi
      subst hi
      simp only
      use h1 rfl
      simp [RawPointer.cook]
      left
  | tail r e ih =>
    intro j hj
    rename_i b c
    cases e with
    | low heq =>
      rename_i jb
      have := h2 jb
      simp only [RawNode.Bounded] at this
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn] at heq
      subst hj
      have that : (v.push N)[jb].lo = .inr j.1 := by
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) _ by rfl] at heq
        rw [← cook_low] at heq
        exact cook_inj heq
        apply RawPointer.bounded_of_le this.1
        omega
        simp [RawPointer.Bounded]
        intro i hi
        injection hi with heq
        rw [← heq]
        omega
      have : RawPointer.Bounded (↑jb) (v.push N)[jb].lo := this.1
      have := this that
      use lt_of_lt_of_le this (Nat.le_of_lt_succ jb.2)
      rcases (ih jb rfl) with ⟨r1, r2⟩
      trans .node ⟨jb.1, r1⟩
      · exact r2
      · simp_rw [Vector.getElem_push_lt r1] at heq
        right
        left
        left
        simp [cook_heap, RawNode.cook]
        simp [cook_heap, RawNode.cook] at heq
        exact cook_aux heq
    | high heq =>
      rename_i jb
      have := h2 jb
      simp only [RawNode.Bounded] at this
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn] at heq
      subst hj
      have that : (v.push N)[jb].hi = .inr j.1 := by
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) _ by rfl] at heq
        rw [← cook_high] at heq
        exact cook_inj heq
        apply RawPointer.bounded_of_le this.2
        omega
        simp [RawPointer.Bounded]
        intro i hi
        injection hi with heq
        rw [← heq]
        omega
      have : RawPointer.Bounded (↑jb) (v.push N)[jb].hi := this.2
      have := this that
      use lt_of_lt_of_le this (Nat.le_of_lt_succ jb.2)
      rcases (ih jb rfl) with ⟨r1, r2⟩
      trans .node ⟨jb.1, r1⟩
      · exact r2
      · simp_rw [Vector.getElem_push_lt r1] at heq
        right
        left
        right
        simp [cook_heap, RawNode.cook]
        simp [cook_heap, RawNode.cook] at heq
        exact cook_aux heq

lemma push_ordered : Bdd.Ordered ⟨cook_heap v h0, RawPointer.cook p h1⟩ → Bdd.Ordered ⟨cook_heap (v.push N) h2, RawPointer.cook p h3⟩ := by
  intro h
  apply Bdd.ordered_of_ordered_heap_all_reachable_eq ⟨⟨cook_heap v h0, RawPointer.cook p h1⟩, h⟩
  · intro j hj
    rcases (push_ordered_aux hj (h2 := h2) (h1 := h1) (h0 := h0) j rfl) with ⟨r1, r2⟩
    use r1
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_lt r1,
      RawNode.cook_equiv]
  · intro j hj
    simp_all only
    simp [RawPointer.cook] at hj
    split at hj
    next heq => contradiction
    next heq =>
      simp only [Pointer.node.injEq] at hj
      subst hj
      use h1 rfl
      simp [RawPointer.cook]

lemma push_evaluate {v : Vector _ _} {h0} {h1} {ho : Bdd.Ordered _} {hu : Bdd.Ordered ⟨cook_heap v h1, RawPointer.cook p hq⟩} :
    OBdd.evaluate ⟨⟨cook_heap (v.push N) h0, RawPointer.cook p hp⟩, ho⟩ =
    OBdd.evaluate ⟨⟨cook_heap v h1, RawPointer.cook p hq⟩, hu⟩ := by
  apply OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
  · simp only [Fin.getElem_fin]
    intro j hj
    use (by omega)
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Fin.is_lt, Vector.getElem_push_lt]
    exact RawNode.cook_equiv
  · exact RawPointer.cook_equiv (h2 := hp)

end RawBdd
