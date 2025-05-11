import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Basic
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Vector

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

instance Bdd.instToString : ToString (Bdd n m) := ⟨fun B => "⟨" ++ (toString B.heap) ++ ", " ++ (toString B.root)  ++ "⟩"⟩

open Bdd

inductive Edge (w : Vector (Node n m) m) : Pointer m → Pointer m → Prop where
  | low  : w[j].low  = p → Edge w (node j) p
  | high : w[j].high = p → Edge w (node j) p

/-- Terminals have no outgoing edges. -/
lemma not_terminal_edge {q} : ¬ Edge w (terminal b) q := by
  intro contra
  contradiction

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
def Bdd.RelevantPointer {n m} (B : Bdd n m) := { q // Reachable B.heap B.root q}

instance Bdd.instDecidableEqRelevantPointer : DecidableEq (Bdd.RelevantPointer B) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.eq_iff)

def Bdd.toRelevantPointer {n m} (B : Bdd n m) : B.RelevantPointer :=
  ⟨B.root, Relation.ReflTransGen.refl⟩

/-- The `Edge` relation lifted to `RelevantPointer`s. -/
@[simp]
def Bdd.RelevantEdge (B : Bdd n m) (p q : B.RelevantPointer) := Edge B.heap p.1 q.1

lemma Bdd.RelevantEdge_from_Edge_Reachable
  {B : Bdd n m} (e : Edge B.heap p q)
  (hp : Reachable B.heap B.root p) (hq : Reachable B.heap B.root q) :
  RelevantEdge B ⟨p, hp⟩ ⟨q, hq⟩ := e

/-- The `MayPrecede` relation lifted to `RelevantPointer`s. -/
@[simp]
def Bdd.RelevantMayPrecede (B : Bdd n m) (p q : B.RelevantPointer) := MayPrecede B.heap p.1 q.1

/-- A BDD is `Ordered` if all edges relevant from the root respect the variable ordering. -/
@[simp]
def Bdd.Ordered {n m} (B : Bdd n m) := Subrelation (RelevantEdge B) (RelevantMayPrecede B)

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

def OBdd n m := { B : Bdd n m // Ordered B }

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
  have : Subrelation (flip (@OEdge n m)) (InvImage Nat.lt OBdd.rav) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
    simp_all only [Ordered]
    rw [← h1] at h2
    let ys := y.toRelevantPointer
    let xs : y.RelevantPointer := ⟨x.root, Relation.ReflTransGen.tail Relation.ReflTransGen.refl h2⟩
    have h3 : RelevantEdge y ys xs := h2
    apply hy at h3
    simp only [RelevantMayPrecede, Bdd.toRelevantPointer, xs, ys] at h3
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
  | leaf   : Bool  → DecisionTree _
  | branch : Fin n → DecisionTree n → DecisionTree n → DecisionTree n
deriving DecidableEq

lemma Bdd.ordered_of_reachable' {B : Bdd n m} :
    B.Ordered → Reachable B.heap B.root p → Ordered ⟨B.heap, p⟩ := by
  intro h1 h2
  rintro ⟨x, hx⟩ ⟨y, hy⟩ e
  simp_all only [Ordered, RelevantEdge, RelevantMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  exact h1 (RelevantEdge_from_Edge_Reachable e (Relation.ReflTransGen.trans h2 hx) (Relation.ReflTransGen.trans h2 hy))

lemma Bdd.ordered_of_reachable {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → Ordered {heap := O.1.heap, root := p} := ordered_of_reachable' O.2

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

def DecisionTree.evaluate : DecisionTree n → Vector Bool n → Bool
  | leaf b, _ => b
  | branch j l h, v => if v[j] then h.evaluate v else l.evaluate v

def DecisionTree.lift : n ≤ n' → DecisionTree n → DecisionTree n'
  | _, leaf b => .leaf b
  | e, branch j l h => .branch ⟨j.1, by omega⟩ (l.lift e) (h.lift e)

lemma DecisionTree.lift_injective {n n' : Nat} {h : n ≤ n'} : Function.Injective (DecisionTree.lift h) := by
  intro x y hxy
  cases x with
  | leaf _ =>
    cases y with
    | leaf _ => simp only [lift] at hxy; simp_all
    | branch _ _ _ => contradiction
  | branch _ _ _ =>
    cases y with
    | leaf _ => contradiction
    | branch _ _ _ =>
      simp only [lift] at hxy
      injection hxy with a b c
      rw [lift_injective b, lift_injective c]
      simp_all only [Fin.mk.injEq, branch.injEq, and_self, and_true]
      ext
      simp_all only

def OBdd.evaluate : OBdd n m → Vector Bool n → Bool := DecisionTree.evaluate ∘ OBdd.toTree

lemma OBdd.evaluate_cast {O : OBdd n m} (h : n = n') : (h ▸ O).evaluate I = O.evaluate (h ▸ I) := by
  subst h
  rfl

def OBdd.HSimilar (O : OBdd n m) (U : OBdd n m') := O.toTree = U.toTree

def OBdd.Similar : OBdd n m → OBdd n m → Prop := HSimilar

/-- Similarity of `Ordered` BDDs is decidable. -/
instance OBdd.instDecidableSimilar {n m} : DecidableRel (β := OBdd n m) OBdd.Similar :=
  fun O U ↦ decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar, HSimilar])

instance OBdd.instDecidableHSimilar (O : OBdd n m) (U : OBdd n m') : Decidable (OBdd.HSimilar O U) :=
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

instance OBdd.Similar.instReflexive : Reflexive (α := OBdd n m) OBdd.Similar := instEquivalence.refl

instance OBdd.Similar.instSymmetric : Symmetric (α := OBdd n m) OBdd.Similar := fun _ _ ↦ instEquivalence.symm

instance OBdd.Similar.instTransitive : Transitive (α := OBdd n m) OBdd.Similar := fun _ _ _ ↦ instEquivalence.trans

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
@[simp]
def OBdd.Reduced {n m} (O : OBdd n m) : Prop
  -- No redundant pointers.
  := NoRedundancy O.1
  -- Similarity implies pointer-equality.
   ∧ Subrelation (SimilarRP O) (InvImage Eq Subtype.val)

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
instance my_decidableRel_of_invImage2 {r : β → β → Prop} [DecidableRel r] {f : α → β} :
    DecidableRel (InvImage r f) :=
  fun a b ↦ decidable_of_decidable_of_iff (show (r (f a) (f b)) ↔ _ by simp [InvImage])

/-- `Reduced` is decidable. -/
instance OBdd.instReducedDecidable {n m} : DecidablePred (α := OBdd n m) Reduced :=
  fun _ ↦ (instDecidableAnd (dp := Fintype.decidableForallFintype) (dq := Fintype.decidableForallFintype))

/-- The output of equal constant functions with inhabited domain is equal. -/
lemma eq_of_constant_eq {α β} {c c' : β} [Inhabited α] :
    Function.const α c = Function.const α c' → c = c' :=
  fun h ↦ (show (Function.const α c) default = (Function.const α c') default by rw [h])

instance Vec.instInhabited {n} [Inhabited α] : Inhabited (Vector α n) := ⟨Vector.replicate n default⟩

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
      _ = q.1    := Eq.symm (eq_terminal_of_relevant (by rw [← h]) q)

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

/-- `f.independentOf i` if the output of `f` does not depend on the value of the `i`th input. -/
def independentOf (f : Vector α n → β) (i : Fin n) := ∀ a v, f v = f (Vector.set v i a)

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

lemma OBdd.var_lt_high_var {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.var < (O.high h).var := by
  have e := Bdd.edge_of_high (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.high h).1.root, reachable_of_edge e⟩ e

lemma OBdd.var_lt_low_var  {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.var < (O.low  h).var := by
  have e := Bdd.edge_of_low (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.low h).1.root, reachable_of_edge e⟩ e

lemma OBdd.Independence' (O : OBdd n m) (i : Fin O.var) : independentOf (OBdd.evaluate O) ⟨i.1, Fin.val_lt_of_le i (Fin.is_le _)⟩ := by
  cases O_root_def : O.1.root with
  | terminal _ =>
    intro b I
    simp [evaluate_terminal' O_root_def]
  | node j =>
    intro b I
    simp only
    rw [OBdd.evaluate_node'' O_root_def]
    simp only
    rcases i with ⟨i, hi⟩
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      symm
      apply Vector.getElem_set_ne
      have : O.1.heap[j].var = O.var := by simp [var, Bdd.var, O_root_def, toVar_node_eq]
      rw [this]
      exact Nat.ne_of_lt hi
    · refine (Independence' (O.high O_root_def) ⟨i, ?_⟩) b I
      trans O.var
      · exact hi
      · exact var_lt_high_var
    · refine (Independence' (O.low  O_root_def) ⟨i, ?_⟩) b I
      trans O.var
      · exact hi
      · exact var_lt_low_var
termination_by O

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

lemma OBdd.size_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.size = 1 + (O.low h).size + (O.high h).size := by
  simp only [size, Function.comp_apply, toTree_node h]
  rfl

lemma OBdd.evaluate_high_eq_evaluate_low_of_independentOf_root {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    independentOf O.evaluate O.1.heap[j].var → (O.high h).evaluate = (O.low h).evaluate := by
  intro i
  ext I
  trans O.evaluate I
  · rw [i true I]
    rw [evaluate_node'' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
    exact (Independence' (O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); simp; rw [h]; simp)⟩) true I
  · rw [i false I]
    rw [evaluate_node'' h]
    simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
    symm
    exact (Independence' (O := O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var  (O := O); simp; rw [h]; simp)⟩) false I

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
  apply Independence' (O.high h) ⟨O.1.heap[j].var, (by convert var_lt_high_var (O := O); simp; rw [h]; simp)⟩

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
  apply Independence' (O.low h) ⟨O.1.heap[j].var, (by convert var_lt_low_var (O := O); simp; rw [h]; simp)⟩

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

lemma OBdd.not_reduced_of_iso_high_low {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
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

lemma OBdd.Similar_of_Isomorphism {O U : OBdd n m} : O.Isomorphism U → O.Similar U := by
  rintro ⟨f, h1, h2⟩
  cases O_root_def : O.1.root with
  | terminal b =>
    have := ((h2 O.1.toRelevantPointer).2 b O_root_def).2
    cases U_root_def : U.1.root with
    | terminal c =>
      simp only [Similar, HSimilar]
      rw [toTree_terminal' O_root_def, toTree_terminal' U_root_def]
      simp only [DecisionTree.leaf.injEq]
      -- need to show that f (O.1.root) = U.1.root
      sorry
    | node i => sorry
  | node j => sorry

def OBdd.terminal_hiso {O : OBdd n m} {U : OBdd n' m'} : O.1.root = terminal b → U.1.root = terminal b → O.HIsomorphism U := fun ho hu ↦
  ⟨fun _ ↦ ⟨terminal b, by rw [hu]; left⟩, by sorry⟩

def OBdd.terminal_iso {O U : OBdd n m} : O.1.root = terminal b → U.1.root = terminal b → O.Isomorphism U := terminal_hiso

def OBdd.node_iso {O U : OBdd n m} :
  O.Reduced' → U.Reduced' →
  (ho : O.1.root = node j) → (hu : U.1.root = node i) →
  (O.low ho).Isomorphism (U.low hu) →
  (O.high ho).Isomorphism (U.high hu) →
  O.Isomorphism U := sorry

lemma OBdd.high_reduced' {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced' → (O.high h).Reduced' := by
  sorry

lemma OBdd.low_reduced' {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} : O.Reduced' → (O.low h).Reduced' := by
  sorry

lemma OBdd.reduced_of_relevant' {O : OBdd n m} (S : O.1.RelevantPointer):
    O.Reduced' → OBdd.Reduced' ⟨{heap := O.1.heap, root := S.1}, ordered_of_relevant O S⟩ := by
  sorry

lemma OBdd.Isomorphism_of_Similiar {O U : OBdd n m} : O.Reduced' → U.Reduced' → O.Similar U → O.Isomorphism U := by
  intro ho hu sim
  cases O_root_def : O.1.root with
  | terminal b =>
    have : U.1.root = terminal b := sorry
    exact terminal_iso O_root_def this
  | node j =>
    have : ∃ i, U.1.root = node i := sorry
    rcases this with ⟨i, U_root_def⟩
    have liso := Isomorphism_of_Similiar (low_reduced'  (h := O_root_def) ho) (low_reduced'  (h := U_root_def) hu) sorry
    have hiso := Isomorphism_of_Similiar (high_reduced' (h := O_root_def) ho) (high_reduced' (h := U_root_def) hu) sorry
    exact node_iso ho hu O_root_def U_root_def liso hiso
termination_by O.size + U.size
decreasing_by all_goals simp only [size_node O_root_def, size_node U_root_def]; linarith

lemma OBdd.reduced_iff_reduced' (O : OBdd n m) : O.Reduced ↔ O.Reduced' := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · exact h1
    · intro p q iso
      apply h2
      exact Similar_of_Isomorphism iso
  · intro h
    constructor
    · exact h.1
    · intro p q sim
      apply h.2
      exact Isomorphism_of_Similiar (reduced_of_relevant' p h)  (reduced_of_relevant' q h) sim

/-- Reduced OBDDs are canonical.  -/
theorem OBdd.HCanonicity {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'}:
    O.Reduced → U.Reduced → O.evaluate = U.evaluate → O.HSimilar U := by
  intro O_reduced U_reduced h
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
      absurd U_reduced
      apply not_reduced_of_iso_high_low U_root_def
      apply HCanonicity (high_reduced U_reduced) (low_reduced U_reduced) this
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
      apply not_reduced_of_iso_high_low O_root_def
      apply HCanonicity (high_reduced O_reduced) (low_reduced O_reduced) this
    | node i =>
      simp only [Similar, HSimilar, InvImage]
      rw [toTree_node O_root_def, toTree_node U_root_def]
      simp only [Ordered, DecisionTree.branch.injEq]
      have same_var : O.1.heap[j].var = U.1.heap[i].var := by
        apply eq_iff_le_not_lt.mpr
        · constructor
          · apply le_of_not_lt
            intro contra
            have := Independence' O ⟨U.1.heap[i].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [O_root_def]; simpa⟩
            rw [h] at this
            simp only [Fin.eta] at this
            simp only [independentOf] at this
            have that : OBdd.Similar (U.high U_root_def) (U.low U_root_def) :=
              HCanonicity (high_reduced U_reduced) (low_reduced U_reduced) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
            apply U_reduced.1 U.1.toRelevantPointer
            simp [toRelevantPointer]
            rw [U_root_def]
            constructor
            have iso : SimilarRP U ⟨(U.high U_root_def).1.root, reachable_of_edge (edge_of_high (h := U_root_def) U.1)⟩
                                   ⟨(U.low  U_root_def).1.root, reachable_of_edge (edge_of_low  (h := U_root_def) U.1)⟩ := that
            exact (symm (U_reduced.2 iso))
          · intro contra
            have := Independence' U ⟨O.1.heap[j].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [U_root_def]; simpa⟩
            rw [← h] at this
            simp only [Ordered, Fin.eta] at this
            simp only [independentOf] at this
            have that : OBdd.Similar (O.high O_root_def) (O.low O_root_def) :=
              HCanonicity (high_reduced O_reduced) (low_reduced O_reduced) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
            apply O_reduced.1 O.1.toRelevantPointer
            simp [toRelevantPointer]
            rw [O_root_def]
            constructor
            have iso : SimilarRP O ⟨(O.high O_root_def).1.root, reachable_of_edge (edge_of_high (h := O_root_def) O.1)⟩
                                   ⟨(O.low  O_root_def).1.root, reachable_of_edge (edge_of_low  (h := O_root_def) O.1)⟩ := that
            exact (symm (O_reduced.2 iso))
      constructor
      · assumption
      · constructor
        · apply HCanonicity (low_reduced  O_reduced) (low_reduced  U_reduced) (evaluate_low_eq_of_evaluate_eq_and_var_eq'  h same_var)
        · apply HCanonicity (high_reduced O_reduced) (high_reduced U_reduced) (evaluate_high_eq_of_evaluate_eq_and_var_eq' h same_var)
termination_by O.size + U.size
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
    refine not_reduced_of_iso_high_low O_root_def ?_ R
    have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
      ext I
      trans b
      · simp [evaluate_high_eq_evaluate_set_true, h]
      · simp [evaluate_low_eq_evaluate_set_false, h]
    exact HCanonicity (high_reduced R) (low_reduced R) this


theorem OBdd.Canonicity_reverse {O : OBdd n m} {U : OBdd n m'}:
    O.Reduced → U.Reduced → O.HSimilar U → O.evaluate = U.evaluate := by
  intro _ _ h
  simp only [Similar, HSimilar] at h
  simp only [evaluate, Function.comp_apply]
  rw [h]

def OBdd.collect_helper (O : OBdd n m) : Vector Bool m × List (Fin m) → Vector Bool m × List (Fin m) :=
  match h : O.1.root with
  | terminal _ => id
  | node j =>
    fun I ↦ if I.1.get j then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩)
termination_by O

/-- Return a list of all reachable node indices. -/
def OBdd.collect : OBdd n m → List (Fin m) :=
  fun O ↦ (collect_helper O ⟨Vector.replicate m false, []⟩).2

lemma OBdd.collect_helper_terminal {v : Vector (Node n m) m} {h : Bdd.Ordered {heap := v, root := terminal b}} :
    collect_helper ⟨{heap := v, root := terminal b}, h⟩ I = I := by
  conv =>
    lhs
    unfold collect_helper
  congr

lemma OBdd.collect_helper_terminal' (O : OBdd n m) (h : O.1.root = terminal b) :
    collect_helper O I = I := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only at h
  have := collect_helper_terminal (h := (show Bdd.Ordered {heap := M, root := terminal b} by simp_rw [← h]; exact o)) (I := I)
  simp_rw [h]
  assumption

lemma OBdd.collect_helper_node {v : Vector (Node n m) m} {h : Bdd.Ordered {heap := v, root := node j}} :
    collect_helper ⟨{heap := v, root := node j}, h⟩ I =
      if I.1[j]
      then I
      else collect_helper ⟨{heap := v, root := v[j].high}, ordered_of_relevant ⟨{heap := v, root := node j}, h⟩ ⟨v[j].high, reachable_of_edge (Edge.high rfl)⟩⟩
                          (collect_helper ⟨{heap := v, root := v[j].low}, ordered_of_relevant ⟨{heap := v, root := node j}, h⟩ ⟨v[j].low, reachable_of_edge (Edge.low rfl)⟩⟩
                                          ⟨I.1.set j true, j :: I.2⟩) := by
  conv =>
    lhs
    unfold collect_helper
  congr

lemma OBdd.collect_helper_node' (O : OBdd n m) {j : Fin m} (h : O.1.root = node j) :
    collect_helper O I = if I.1[j] then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩) := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only at h
  have := collect_helper_node (h := (show Bdd.Ordered {heap := M, root := node j} by simp_rw [← h]; exact o)) (I := I)
  simp_rw [h]
  assumption

theorem OBdd.collect_helper_retains_found {O : OBdd n m} {I : Vector Bool m × List (Fin m)} :
    j ∈ I.2 → j ∈ (collect_helper O I).2 := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O O_root_def]
    assumption
  | node i =>
    rw [collect_helper_node' O O_root_def]
    cases I.1[i]
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

theorem OBdd.collect_helper_retains_marked {O : OBdd n m} {I : Vector Bool m × List (Fin m)} {j : Fin m}:
    I.1[j] = true → (collect_helper O I).1[j] = true := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O O_root_def]
    assumption
  | node i =>
    rw [collect_helper_node' O O_root_def]
    cases I.1[i]
    case true  => simpa
    case false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have : ((O.low O_root_def).collect_helper (I.1.set i true, i :: I.2)).1[j] = true := by
        apply collect_helper_retains_marked
        simp only []
        cases decEq i j with
        | isFalse hf =>
          have : i.1 ≠ j.1 := by
            exact Fin.val_ne_of_ne hf
          simp only [Fin.getElem_fin]
          rw [Vector.getElem_set_ne _ _ this]
          assumption
        | isTrue ht => rw [ht]; simp
      exact collect_helper_retains_marked this
termination_by O

theorem OBdd.collect_helper_only_marks_reachable {O : OBdd n m} {I : Vector Bool m × List (Fin m)} :
    I.1[j] = false → (collect_helper O I).1[j] = true → Reachable O.1.heap O.1.root (node j) := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O O_root_def, h1] at h2; contradiction
  | node i =>
    cases decEq i j with
    | isTrue ht  => rw [ht]; exact Relation.ReflTransGen.refl
    | isFalse hf =>
      rw [collect_helper_node' O O_root_def] at h2
      cases hh : I.1[i] with
      | true =>
        rw [hh] at h2
        simp only [↓reduceIte] at h2
        rw [h1] at h2
        contradiction
      | false =>
        rw [hh] at h2
        simp at h2
        rw [← O_root_def]
        cases hhh : ((O.low O_root_def).collect_helper (I.1.set i true, i :: I.2)).1[j] with
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
            · have : i.1 ≠ j.1 := by
                exact Fin.val_ne_of_ne hf
              simp only [Fin.getElem_fin]
              rw [Vector.getElem_set_ne _ _ this]
              assumption
            · assumption
          simp at this
          trans (O.low O_root_def).1.root
          · exact reachable_of_edge (edge_of_low (h := O_root_def) O.1)
          · assumption
termination_by O

theorem OBdd.collect_helper_spec {O : OBdd n m} :
    (∀ i, (Reachable O.1.heap O.1.root (node i) → I.1[i] = true → i ∈ I.2)) →
    ∀ i, (Reachable O.1.heap O.1.root (node i) → (collect_helper O I).1[i] → i ∈ (collect_helper O I).2) := by
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
    cases hh : I.1[k] with
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
        cases hhh : I.1[j] with
        | true =>
          apply collect_helper_retains_found
          apply collect_helper_retains_found
          right
          apply h <;> assumption
        | false=>
          cases hhhh : ((O.low O_root_def).collect_helper (I.1.set k true, k :: I.2)).1[j] with
          | true =>
            have : j ∈ ((O.low O_root_def).collect_helper (I.1.set k true, k :: I.2)).2 := by
              apply collect_helper_spec
              · intro i' re' ma'
                simp at ma'
                simp at re'
                simp only
                cases decEq k i' with
                | isFalse hff =>
                  rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hff])] at ma'
                  right
                  apply h
                  exact Reachable.trans (reachable_of_edge (edge_of_low (h := O_root_def) O.1)) re'
                  exact ma'
                | isTrue  htt => rw [htt]; left
              · have : (I.1.set k true, k :: I.2).1[j] = false := by
                  simp only [Fin.getElem_fin]
                  rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hhf])]
                  exact hhh
                apply collect_helper_only_marks_reachable this hhhh
              · exact hhhh
            apply collect_helper_retains_found this
          | false=>
            apply collect_helper_spec
            · intro i' re' ma'
              simp at ma' re'
              have := h i' (Reachable.trans (reachable_of_edge (edge_of_high (h := O_root_def) O.1)) re')
              cases hhhhh : I.1[i'] with
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
                  have that : (I.1.set k true, k :: I.2).1[i'] = false := by
                    simp only [Fin.getElem_fin]
                    rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hhff])]
                    exact hhhhh
                  apply collect_helper_spec
                  · intro i'' re'' ma''
                    simp at ma''
                    simp at re''
                    simp only
                    cases decEq k i'' with
                    | isFalse hfff =>
                      rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hfff])] at ma''
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

lemma OBdd.collect_spec' {O : OBdd n m} {j : Fin m} {I : Vector Bool m × List (Fin m)} :
    Reachable O.1.heap O.1.root (node j) →
    (∀ i, (Reachable O.1.heap O.1.root (node i) → Reachable O.1.heap (node i) (node j) → I.1[i] = false)) →
    (O.collect_helper I).1[j] = true := by
  intro h1 h2
  cases O_root_def : O.1.root with
  | terminal b =>
    have : (⟨node j, h1⟩ : O.1.RelevantPointer).1  = terminal b := by
      apply eq_terminal_of_relevant
      rw [← O_root_def]
    contradiction
  | node i =>
    rw [collect_helper_node' O O_root_def]
    have : I.1[i] = false := by
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
            simp only [Fin.getElem_fin]
            rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne h])]
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
          simp only [Fin.getElem_fin]
          rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hij])]
          apply h2
          · exact Reachable.trans (reachable_of_edge (edge_of_high (h := O_root_def) O.1)) (Reachable.trans re ma)
          · exact Relation.ReflTransGen.refl
          · apply collect_spec'
            · have that : Reachable (O.low O_root_def).1.heap (O.low O_root_def).1.root (node i') := by
                apply collect_helper_only_marks_reachable (I := (I.1.set i true, i :: I.2))
                · cases decEq i i' with
                  | isFalse hff =>
                    simp only [Fin.getElem_fin]
                    rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hff])]
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
                simp only [Fin.getElem_fin]
                rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne h])]
                apply h2
                exact Reachable.trans (reachable_of_edge (edge_of_low (h := O_root_def) O.1)) re1
                exact re2
termination_by O

/-- `collect` is correct. -/
theorem OBdd.collect_spec {O : OBdd n m} {j : Fin m} : Reachable O.1.heap O.1.root (node j) → j ∈ collect O := by
  intro h
  simp [collect]
  apply collect_helper_spec
  · intro i re ma
    simp only [Fin.getElem_fin] at ma
    rw [Vector.getElem_replicate _] at ma
    contradiction
  · assumption
  · apply collect_spec' h
    intro i re1 re2
    exact List.Vector.get_replicate false i

theorem OBdd.collect_helper_spec_reverse (O : OBdd n m) (r : Pointer m) I :
    Reachable O.1.heap r O.1.root →
    (∀ i ∈ I.2, Reachable O.1.heap r (node i)) →
    ∀ i ∈ (collect_helper O I).2, Reachable O.1.heap r (node i) := by
  intro h0 h1 i h2
  cases h : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' O h] at h2
    exact h1 i h2
  | node j =>
    rw [collect_helper_node' O h] at h2
    split at h2
    next ht =>
      exact h1 i h2
    next hf =>
      cases List.instDecidableMemOfLawfulBEq i (j :: I.2) with
      | isTrue htt =>
        cases htt with
        | head as    => convert h0; symm; assumption
        | tail b hin => exact h1 i hin
      | isFalse hff =>
        cases List.instDecidableMemOfLawfulBEq i ((O.low h).collect_helper (I.1.set j true, j :: I.2)).2 with
        | isFalse hhf =>
          rw [← Bdd.high_heap_eq_heap (h := h)]
          refine collect_helper_spec_reverse (O.high h) r _ ?_ ?_ i h2
          · trans O.1.root
            · exact h0
            · exact reachable_of_edge (edge_of_high (h := h))
          · intro i' hi'
            simp only [high_heap_eq_heap]
            rw [← low_heap_eq_heap (h := h)]
            refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i' hi'
            · trans O.1.root
              · exact h0
              · exact reachable_of_edge (edge_of_low (h := h))
            · intro i'' hi''
              simp only at hi''
              cases hi'' with
              | head as     => simp only [low_heap_eq_heap]; convert h0; symm; assumption
              | tail _ hi'' =>
                simp only [low_heap_eq_heap]
                exact h1 i'' hi''
        | isTrue hht =>
          rw [← low_heap_eq_heap (h := h)]
          refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i hht
          · trans O.1.root
            · exact h0
            · exact reachable_of_edge (edge_of_low (h := h))
          · intro i' hi'
            simp only at hi'
            cases hi' with
            | head as    => simp only [low_heap_eq_heap]; convert h0; symm; assumption
            | tail _ hi' =>
              simp only [low_heap_eq_heap]
              exact h1 i' hi'
termination_by O

theorem OBdd.collect_spec_reverse {O : OBdd n m} {j : Fin m} : j ∈ collect O → Reachable O.1.heap O.1.root (node j) := by
  intro h
  simp only [collect] at h
  apply collect_helper_spec_reverse O O.1.root (Vector.replicate m false, []) (Relation.ReflTransGen.refl)
  · simp
  · assumption

theorem OBdd.collect_helper_nodup {I : Vector Bool m × List (Fin m)} {O : OBdd n m} :
    (∀ i ∈ I.2, I.1[i] = true) ∧ I.2.Nodup →
    (∀ i ∈ (collect_helper O I).2, (collect_helper O I).1[i] = true) ∧ (collect_helper O I).2.Nodup := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b => simpa [collect_helper_terminal' O O_root_def]
  | node     j =>
    rw [collect_helper_node' O O_root_def]
    split
    next heq => assumption
    next heq =>
      apply collect_helper_nodup
      apply collect_helper_nodup
      simp only [List.mem_cons, forall_eq_or_imp, List.Vector.get_set_same, true_and, List.nodup_cons]
      constructor
      · constructor
        · simp
        · intro i hi
          cases decEq j i with
          | isFalse hf =>
            simp only [Fin.getElem_fin]
            rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hf])]
            exact h.1 i hi
          | isTrue  ht => simp_all
      · constructor
        · contrapose heq
          simp_all
        · exact h.2
termination_by O

theorem OBdd.mem_collect_iff_reachable {O : OBdd n m} {j : Fin m} : j ∈ collect O ↔ Reachable O.1.heap O.1.root (node j) := ⟨collect_spec_reverse, collect_spec⟩

theorem OBdd.collect_nodup {O : OBdd n m} : (collect O).Nodup := by
  simp only [collect]
  exact (collect_helper_nodup (by simp)).2

def OBdd.numPointers : OBdd n m → Nat := List.length ∘ collect

lemma isTerminal_iff_numPointer_eq_zero {n m} {O : OBdd n m} : O.numPointers = 0 ↔ O.isTerminal := by
  constructor
  · intro h
    simp only [OBdd.numPointers, Function.comp_apply, List.length_eq_zero_iff] at h
    cases O_root_def : O.1.root with
    | terminal b => use b
    | node j =>
      have := OBdd.collect_spec (j := j) (by rw [O_root_def]; exact Relation.ReflTransGen.refl)
      rw [h] at this
      contradiction
  · rintro ⟨b, hb⟩
    simp only [OBdd.numPointers, Function.comp_apply, List.length_eq_zero_iff, OBdd.collect]
    rw [OBdd.collect_helper_terminal']
    assumption

lemma not_isTerminal_of_root_eq_node {n m} {j} {O : OBdd n m} (h : O.1.root = node j) : ¬ O.isTerminal := by
  rintro ⟨b, hb⟩
  rw [h] at hb
  contradiction

def Bool_of_numPointer_eq_zero {n m} (O : OBdd n m) (h : O.numPointers = 0) : Bool :=
  match O_root_def : O.1.root with
  | terminal b => b
  | node _ => False.elim (not_isTerminal_of_root_eq_node O_root_def (isTerminal_iff_numPointer_eq_zero.mp h))

def OBdd.OReachable {n m} := Relation.ReflTransGen (@OEdge n m)

lemma OBdd.low_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j}: O.OReachable U → O.OReachable (U.low U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_low

lemma OBdd.high_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j} : O.OReachable U → O.OReachable (U.high U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_high

def OBdd.SubBdd {n m} (O : OBdd n m) := { U // O.OReachable U }

def OBdd.toSubBdd {n m} (O : OBdd n m) : O.SubBdd := ⟨O, Relation.ReflTransGen.refl⟩

def OBdd.SubBdd.low {n m} {j} {O : OBdd n m} (S : O.SubBdd) : S.1.1.root = node j → O.SubBdd := fun h ↦
  ⟨S.1.low h, low_oreachable S.2⟩

def OBdd.SubBdd.high {n m} {j} {O : OBdd n m} (S : O.SubBdd) : S.1.1.root = node j → O.SubBdd := fun h ↦
  ⟨S.1.high h, high_oreachable S.2⟩

lemma OBdd.sub_eq_of_isTerminal {n m} {O : OBdd n m} (S : O.SubBdd) : O.isTerminal → S.1 = O := by
  rcases S with ⟨U, hU⟩
  simp only
  intro h
  apply Relation.reflTransGen_iff_eq_or_transGen.mp at hU
  cases hU with
  | inl hl => assumption
  | inr hr =>
    rcases (Relation.transGen_swap.mp hr) with e | ⟨_, e⟩ <;> exact False.elim (not_OEdge_of_isTerminal h e)

lemma OBdd.numPointers_gt_zero_of_Sub_root_eq_node {n m} {j} {O : OBdd n m} (S : O.SubBdd) : S.1.1.root = node j → O.numPointers > 0 := by
  contrapose
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
  intro h
  have := sub_eq_of_isTerminal S (isTerminal_iff_numPointer_eq_zero.mp h)
  rw [this]
  rcases isTerminal_iff_numPointer_eq_zero.mp h with ⟨b, hb⟩
  rw [hb]
  simp

instance OBdd.instNeZeroNumPointers {n m} {j} {O : OBdd n m} (S : O.SubBdd) : S.1.1.root = node j → NeZero O.numPointers := by
  intro h
  have := numPointers_gt_zero_of_Sub_root_eq_node S h
  constructor
  linarith

@[simp]
def Bdd.lift_node : n ≤ n' → Node n m → Node n' m := fun h N ↦ ⟨⟨N.var.1, by exact Fin.val_lt_of_le N.var h⟩, N.low, N.high⟩

lemma Bdd.lift_node_trivial_eq {n n' m : Nat} {h : n = n'} {N : Node n m} : lift_node (n' := n') (by rw [h]) N = h ▸ N := by
  subst h
  simp_all

@[simp]
def Bdd.lift_heap : n ≤ n' → Vector (Node n m) m → Vector (Node n' m) m := fun h v ↦ Vector.map (lift_node h) v

@[simp]
def Bdd.lift : n ≤ n' → Bdd n m → Bdd n' m := fun h B ↦ ⟨lift_heap h B.heap, B.root⟩

lemma Bdd.lift_edge_iff {n n' m : Nat} {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} : Edge B.heap p q ↔ Edge (B.lift h).heap p q := by
  constructor
  · intro e
    cases e with
    | low  _ => left;  simpa
    | high _ => right; simpa
  · intro e
    cases e with
    | low  _ => left;  simp_all
    | high _ => right; simp_all

lemma Bdd.lift_reachable_iff {n n' m : Nat} {h : n ≤ n'} {B : Bdd n m} {p : Pointer m} : Reachable B.heap B.root p ↔ Reachable (B.lift h).heap (B.lift h).root p := by
  constructor
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (lift_edge_iff.mp e)
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (lift_edge_iff.mpr e)

lemma Bdd.lift_preserves_MayPrecede {n n' m : Nat} {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} : MayPrecede (B.lift h).heap p q ↔ MayPrecede B.heap p q := by
  constructor
  · intro hm
    cases p with
    | terminal _ =>
      absurd hm
      exact not_terminal_MayPrecede
    | node j =>
      cases q with
      | terminal _ =>
        apply MayPrecede_node_terminal
      | node j' =>
        simp only [MayPrecede, Nat.succ_eq_add_one, lift, lift_heap, toVar_node_eq, Fin.getElem_fin, List.Vector.getElem_map, lift_node] at hm
        apply (Fin.natCast_lt_natCast (by omega) (by omega)).mp at hm
        simp only [MayPrecede, Nat.succ_eq_add_one, toVar_node_eq, Fin.getElem_fin]
        aesop
  · intro hm
    cases p with
    | terminal _ =>
      absurd hm
      exact not_terminal_MayPrecede
    | node j =>
      cases q with
      | terminal _ =>
        apply MayPrecede_node_terminal
      | node j' =>
        simp only [MayPrecede, Nat.succ_eq_add_one, toVar_node_eq, Fin.getElem_fin] at hm
        simp only [MayPrecede, Nat.succ_eq_add_one, lift, lift_heap, toVar_node_eq, Fin.getElem_fin, List.Vector.getElem_map, lift_node]
        simp_all only [Fin.coe_eq_castSucc, Fin.castSucc_lt_castSucc_iff, Vector.getElem_map, lift_node]
        refine (Fin.natCast_lt_natCast ?_ ?_).mpr ?_ <;> omega

lemma Bdd.lift_preserves_RelevantEdge {n n' m : Nat} {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    (∃ (hp : Reachable (B.lift h).heap (B.lift h).root p) (hq : Reachable (B.lift h).heap (B.lift h).root q), RelevantEdge (B.lift h) ⟨p, hp⟩ ⟨q, hq⟩) ↔
    (∃ (hp : Reachable B.heap B.root p) (hq : Reachable B.heap B.root q), RelevantEdge B ⟨p, hp⟩ ⟨q, hq⟩) := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    use (lift_reachable_iff.mpr hp)
    use (lift_reachable_iff.mpr hq)
    cases hr with
    | low  hl => simp at hl; left ; assumption
    | high hh => simp at hh; right; assumption
  · rintro ⟨hp, hq, hr⟩
    use (lift_reachable_iff.mp hp)
    use (lift_reachable_iff.mp hq)
    cases hr with
    | low  hl => simp at hl; left ; simpa
    | high hh => simp at hh; right; simpa

lemma Bdd.Ordered_of_lift {n n' m : Nat} {h : n ≤ n'} {B : Bdd n m} : B.Ordered → (B.lift h).Ordered := by
  rintro ho ⟨x, hx⟩ ⟨y, hy⟩ e
  apply lift_preserves_MayPrecede.mpr
  exact ho (lift_preserves_RelevantEdge.mp ⟨hx, hy, e⟩).2.2

def OBdd.lift : n ≤ n' → OBdd n m → OBdd n' m := fun h O ↦ ⟨O.1.lift h, Bdd.Ordered_of_lift O.2⟩

lemma OBdd.lift_trivial_eq {n n' m : Nat} {h : n = n'} {O : OBdd n m} : (O.lift (n' := n') (by rw [h])) = h ▸ O := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only [lift, Bdd.lift, lift_heap]
  congr
  · have : (lift_node (Eq.mpr (id (congrArg (fun _a ↦ _a ≤ n') h)) (le_refl n'))) = fun (x : Node n m) ↦ h ▸ x := by
      ext
      exact lift_node_trivial_eq
    rw [this]
    subst h
    simp only
    rcases M with ⟨V, l⟩
    simp [Vector.map, List.map_id_fun', id_eq]
  · subst h
    simp

lemma Bdd.lift_preserves_root {n n' m : Nat} {h : n ≤ n'} {B : Bdd n m} : (B.lift h).root = B.root := by simp
lemma OBdd.lift_preserves_root {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} : (O.lift h).1.root = O.1.root := Bdd.lift_preserves_root
lemma OBdd.lift_low {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (O_root_def : O.1.root = node j): (O.lift h).low O_root_def = (O.low O_root_def).lift h := by
  simp only [low, lift, Bdd.lift, lift_heap]
  simp_rw [Bdd.low_heap_eq_heap]
  simp_rw [O_root_def]
  simp [Bdd.low]

lemma OBdd.lift_high {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (O_root_def : O.1.root = node j): (O.lift h).high O_root_def = (O.high O_root_def).lift h := by
  simp only [high, lift, Bdd.lift, lift_heap]
  simp_rw [Bdd.high_heap_eq_heap]
  simp_rw [O_root_def]
  simp [Bdd.high]

lemma OBdd.NoRedundancy_of_lift {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} : O.1.NoRedundancy → (O.lift h).1.NoRedundancy := by
  rintro hnr ⟨p, hp⟩ contra
  simp only at contra
  cases p_def : p with
  | terminal _ =>
    cases contra with
    | red _ => contradiction
  | node j =>
    rw [p_def] at contra
    cases contra with
    | red red =>
      simp only [lift, Bdd.lift, lift_heap, Fin.getElem_fin, List.Vector.getElem_map, lift_node] at red
      apply hnr ⟨p, lift_reachable_iff.mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all

lemma OBdd.lift_preserves_toTree {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} : (O.lift h).toTree = O.toTree.lift h := by
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [toTree_terminal' O_root_def, DecisionTree.lift, lift, Bdd.lift]
    simp_rw [O_root_def, toTree_terminal]
  | node j =>
    simp only [toTree_node O_root_def, DecisionTree.lift]
    rw [← lift_preserves_toTree (h := h) (O := (O.low  O_root_def))]
    rw [← lift_preserves_toTree (h := h) (O := (O.high O_root_def))]
    rw [← lift_preserves_root (h := h)] at O_root_def
    simp only [toTree_node O_root_def]
    simp only [DecisionTree.branch.injEq]
    constructor
    · simp [lift]
    · constructor
      · rw [lift_low]
      · rw [lift_high]
termination_by O

private lemma vec_getElem_cast_eq {v : Vector α n} {h : n = n} {i : Nat} {hi : i < n} : v[i] = (h ▸ v)[i] := by
  rfl

lemma DecisionTree.lift_evaluate {n n' : Nat} {h : n ≤ n'} {T : DecisionTree n} {I : Vector Bool n'} :
    (DecisionTree.lift h T).evaluate I = T.evaluate ((show (min n n') = n by simpa) ▸ I.take n) := by
  cases T with
  | leaf => simp [lift, evaluate]
  | branch _ _ _ =>
    simp only [lift, evaluate]
    rw [lift_evaluate]
    rw [lift_evaluate]
    refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
    simp only [eq_iff_iff, Bool.coe_iff_coe, Fin.getElem_fin]
    rename_i a _ _
    have : (I.take n)[a.1] = I[a.1] := by
      apply Vector.getElem_take
    rw [← this]
    rcases a with ⟨a, ha⟩
    simp only
    sorry

lemma OBdd.lift_evaluate {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} {I : Vector Bool n'} :
    (O.lift h).evaluate I = O.evaluate ((show (min n n') = n by simpa) ▸ I.take n) := by
  simp only [evaluate, Function.comp_apply, lift_preserves_toTree]
  rw [DecisionTree.lift_evaluate]

lemma OBdd.SimilarRP_lift {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} {p q : Pointer m} {hp : Reachable (O.lift h).1.heap (O.lift h).1.root p} {hq : Reachable (O.lift h).1.heap (O.lift h).1.root q} :
    (O.lift h).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ → O.SimilarRP ⟨p, lift_reachable_iff.mpr hp⟩ ⟨q, lift_reachable_iff.mpr hq⟩ := by
  intro sim
  simp only [SimilarRP, Similar, HSimilar] at sim
  have : OBdd.toTree ⟨{heap := (O.lift h).1.heap, root := p}, ordered_of_reachable hp⟩ = OBdd.toTree (OBdd.lift h ⟨{heap := O.1.heap, root := p}, ordered_of_reachable (lift_reachable_iff.mpr hp)⟩) := by
    rfl
  rw [this] at sim
  have : OBdd.toTree ⟨{heap := (O.lift h).1.heap, root := q}, ordered_of_reachable hq⟩ = OBdd.toTree (OBdd.lift h ⟨{heap := O.1.heap, root := q}, ordered_of_reachable (lift_reachable_iff.mpr hq)⟩) := by
    rfl
  rw [this] at sim
  rw [lift_preserves_toTree] at sim
  rw [lift_preserves_toTree] at sim
  clear this
  clear this
  simp only [SimilarRP, Similar, HSimilar]
  rw [DecisionTree.lift_injective sim]

lemma OBdd.Reduced_of_lift {n n' m : Nat} {h : n ≤ n'} {O : OBdd n m} : O.Reduced → (O.lift h).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact NoRedundancy_of_lift r1
  · rintro _ _ sim; exact r2 (SimilarRP_lift sim)

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

lemma OBdd.numPointers_terminal {O : OBdd n m} : O.isTerminal → Fintype.card O.1.RelevantPointer = 1 := by
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

lemma OBdd.numPointers_spec {O : OBdd n m} : O.numPointers = Fintype.card { j // Reachable O.1.heap O.1.root (node j) } := by
  simp only [numPointers, Function.comp_apply]
  simp_rw [Fintype.card, Finset.univ]
  have : O.collect.length = (Multiset.ofList O.collect).card := by rfl
  rw [this]
  refine Eq.symm (Finset.card_eq_of_bijective (fun i hi ↦ ⟨O.collect.get ⟨i, hi⟩, by simp; exact collect_spec_reverse (List.getElem_mem hi)⟩) ?_ ?_ ?_)
  · rintro ⟨j, hj⟩ h
    simp only [Subtype.mk.injEq, Multiset.coe_card]
    exact List.mem_iff_getElem.mp (collect_spec hj)
  · rintro i hi
    simp only [List.get_eq_getElem]
    apply Fintype.complete
  · intro i j hi hj heq
    simp only [List.get_eq_getElem, Subtype.mk.injEq] at heq
    exact (List.Nodup.getElem_inj_iff collect_nodup).mp heq

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

lemma Bdd.ordered_of_ordered_heap_not_reachable_set {O : OBdd n m} :
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
    · simp only [low]
      sorry
      -- simp only [Vector.get_set_of_ne' this]
      -- have that := ordered_of_ordered_heap_not_reachable_set (O := (O.low O_root_def)) i N
      -- simp only [OBdd.low_heap_eq_heap] at that
      -- simp only [OBdd.low_root_eq_low] at that
      -- apply that
      -- intro contra
      -- apply unr
      -- trans O.1.heap[j].low
      -- · right
      --   left
      --   rw [O_root_def]
      --   left
      --   rfl
      -- · exact contra
    · simp only [Nat.succ_eq_add_one, var, low]
      sorry
      -- rw [Vec.get_set_of_ne' this N]
      -- rw [toVar_heap_set this]
      -- have that : toVar O.1.heap (node j) < toVar O.1.heap O.1.heap[j].low := by
      --   exact @O.2 ⟨node j, (by rw [O_root_def]; left)⟩
      --              ⟨O.1.heap[j].low, (by trans (node j); rw [O_root_def]; left; right; left; left; rfl)⟩
      --              (by left; rfl)
      -- convert that using 1
      -- cases low_def : O.1.heap[j].low with
      -- | terminal bl => simp
      -- | node jl =>
      --   simp only [toVar]
      --   simp only [Nat.succ_eq_add_one, Ordered, Fin.coe_eq_castSucc, Fin.castSucc_inj]
      --   rw [Vec.get_set_of_ne']
      --   intro contra
      --   rw [contra] at unr
      --   apply unr
      --   trans (node j)
      --   · rw [O_root_def]; left
      --   · rw [← low_def]; right; left; left; rfl
    · simp only [high]
      sorry
      -- simp only [Vec.get_set_of_ne' this]
      -- have that := ordered_of_ordered_heap_not_reachable_set (O := (O.high O_root_def)) i N
      -- simp only [OBdd.high_heap_eq_heap] at that
      -- simp only [OBdd.high_root_eq_high] at that
      -- apply that
      -- intro contra
      -- apply unr
      -- trans O.1.heap[j].high
      -- · right
      --   left
      --   rw [O_root_def]
      --   right
      --   rfl
      -- · exact contra
    · simp only [Nat.succ_eq_add_one, var, high]
      sorry
      -- rw [Vec.get_set_of_ne' this N]
      -- rw [toVar_heap_set this]
      -- have that : toVar O.1.heap (node j) < toVar O.1.heap O.1.heap[j].high := by
      --   exact @O.2 ⟨node j, (by rw [O_root_def]; left)⟩
      --              ⟨O.1.heap[j].high, (by trans (node j); rw [O_root_def]; left; right; left; right; rfl)⟩
      --              (by right; rfl)
      -- convert that using 1
      -- cases high_def : O.1.heap[j].high with
      -- | terminal bh => simp
      -- | node bh =>
      --   simp only [toVar]
      --   simp only [Nat.succ_eq_add_one, Ordered, Fin.coe_eq_castSucc, Fin.castSucc_inj]
      --   rw [Vec.get_set_of_ne']
      --   intro contra
      --   rw [contra] at unr
      --   apply unr
      --   trans (node j)
      --   · rw [O_root_def]; left
      --   · rw [← high_def]; right; left; right; rfl
termination_by O
