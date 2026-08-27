module

import all Bdd.Basic
import all Bdd.Size

section not_used
open Pointer Bdd

inductive Pointer.le {m} : Pointer m → Pointer m → Prop where
  | terminal_le_terminal {b c} : b ≤ c → le (terminal b) (terminal c)
  | terminal_le_node {b j} : le (terminal b) (node j)
  | node_le_node {j i} : j ≤ i → le (node j) (node i)

instance Pointer.instLE : LE (Pointer m) := {le := Pointer.le}

instance Pointer.instDecidableLe {m} : DecidableLE (Pointer m) :=
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

@[simp]
def Pointer.MayPrecede {n m} (M : Vector (Node n m) m) (p q : Pointer m) := toVar M p < toVar M q

/-- Terminals must not precede other pointers. -/
@[simp, grind .]
lemma Pointer.not_terminal_mayPrecede : ¬ MayPrecede M (terminal b) p := by
  cases p with
  | terminal _ => simp [MayPrecede]
  | node     j => exact not_lt.mpr (Fin.le_last _)

/-- Non-terminals may precede terminals. -/
lemma Pointer.MayPrecede_node_terminal {n m} (w : Vector (Node n m) m) {j b} : MayPrecede w (node j) (terminal b) := by
  simp only [MayPrecede, Nat.succ_eq_add_one, toVar, Fin.getElem_fin]
  refine Fin.mk_lt_of_lt_val ?_
  simp only [Fin.val_last, Fin.is_lt]

def OBdd.OReachable {n m} := Relation.ReflTransGen (@OEdge n m)

lemma OBdd.low_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j}:
    O.OReachable U → O.OReachable (U.low U_root_def) :=
  fun h ↦ Relation.ReflTransGen.tail h oedge_of_low

lemma OBdd.high_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j} :
    O.OReachable U → O.OReachable (U.high U_root_def) :=
  fun h ↦ Relation.ReflTransGen.tail h oedge_of_high

lemma aux {O : OBdd n m} {i : Fin m} :
    O.1.heap[i.1].var = Fin.castPred (toVar O.1.heap (node i)) (Fin.exists_castSucc_eq.mp ⟨O.1.heap[i.1].var, by simp [toVar]; rfl⟩) :=
  by simp [toVar]

/-- The output of equal constant functions with inhabited domain is equal. -/
lemma eq_of_constant_eq {α β} {c c' : β} [Inhabited α] :
    Function.const α c = Function.const α c' → c = c' :=
  fun h ↦ (show (Function.const α c) default = (Function.const α c') default by rw [h])

lemma OBdd.reachable_node_iff {n m j} {O : OBdd n m} (h : O.1.root = node j) :
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
        · exact O.bdd.reachable_low h
        · exact r.1
      | inr r =>
        cases r with
        | inl r =>
          trans (O.high h).1.root
          · exact O.bdd.reachable_high h
          · exact r.1
        | inr r =>
          trans (O.high h).1.root
          · exact O.bdd.reachable_high h
          · exact r.2

/-- Similarity of `Ordered` BDDs is decidable. -/
instance OBdd.instDecidableSimilar {n m} : DecidableRel (α  := OBdd n m) (β := OBdd n m) OBdd.Similar :=
  fun O U ↦ decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar])

-- FIXME: Use the instance from Sim.lean instead.
instance OBdd.instDecidableHSimilar {n m m'} (O : OBdd n m) (U : OBdd n m') : Decidable (OBdd.Similar O U) :=
  decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar])

@[no_expose]
instance OBdd.instDecidableSimilarRP : Decidable (OBdd.SimilarRP l r) := by
  simp only [OBdd.SimilarRP]; infer_instance

instance OBdd.instFintypeRelevantPointer {n m} (O : OBdd n m) : Fintype (O.1.RelevantPointer) := by
  convert Subtype.fintype _ <;> infer_instance

@[implicit_reducible]
def Pointer.decidableEitherReachable {n m} (O U : OBdd n m) (h : O.1.heap = U.1.heap) :
    DecidablePred (fun q ↦ (Reachable O.1.heap O.1.root q) ∨ (Reachable O.1.heap U.1.root q)) := by
  intro p
  simp
  cases OBdd.instDecidableReachable O p with
  | isFalse hf =>
    cases OBdd.instDecidableReachable U p with
    | isFalse hhf =>
      apply isFalse
      simp_all [or_self, not_false_eq_true]
    | isTrue  hht =>
      apply isTrue
      simp_all only [or_true]
  | isTrue  ht =>
    apply isTrue
    simp_all only [true_or]

@[implicit_reducible]
def OBdd.fintypeEitherRelevantPointer (O U : OBdd n m) (h : O.1.heap = U.1.heap) :
    Fintype { q // Reachable O.1.heap O.1.root q ∨ Reachable O.1.heap U.1.root q } := by
  convert Subtype.fintype _
  · exact decidableEitherReachable O U h
  · infer_instance

@[no_expose]
instance OBdd.instFintypeReachableFromNode (O : OBdd n m) (h : O.1.root = node j) :
    Fintype { q // q = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root q ∨ Reachable O.1.heap (O.high h).1.root q) } := by
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

/-- The inverse image of a decidable relation is decidable. -/
instance my_decidableRel_of_invImage2 {r : β → β → Prop} [DecidableRel r] {f : α → β} :
    DecidableRel (InvImage r f) :=
  fun a b ↦ decidable_of_decidable_of_iff (show (r (f a) (f b)) ↔ _ by simp [InvImage])

instance Bdd.instDecidableEqRelevantPointer : DecidableEq (Bdd.RelevantPointer B) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.ext_iff)

/-- `Reduced` is decidable. -/
@[no_expose]
instance OBdd.instReducedDecidable {n m} : DecidablePred (α := OBdd n m) Reduced :=
  fun _ ↦ (instDecidableAnd (dp := Fintype.decidableForallFintype) (dq := Fintype.decidableForallFintype))

/-- An acyclicity lemma: an edge from `O` to `U` implies that `O` is not reachable from `U`.  -/
lemma OBdd.not_oedge_reachable {n m} {O U : OBdd n m}: OEdge O U → ¬ Reachable O.1.heap U.1.root O.1.root := by
  rintro ⟨same_heap, e⟩ contra
  apply Relation.reflTransGen_iff_eq_or_transGen.mp at contra
  cases contra with
  | inl h =>
    rw [← h] at e
    exact Bdd.no_self_edge_of_ordered O.ordered O.bdd.relevant_root e
  | inr h =>
    apply Relation.TransGen.head'_iff.mp at h
    rcases h with ⟨c, h1, h2⟩
    rw [same_heap] at h1
    let V : OBdd n m := ⟨{heap := U.1.heap, root := c}, ordered_of_edge U.ordered h1⟩
    have : c = V.1.root := rfl
    rw [this] at h1 h2
    apply not_oedge_reachable ⟨by rfl, h1⟩
    trans O.1.root
    rw [same_heap] at h2; exact h2
    rw [← same_heap]; exact Reachable.ofEdge e
termination_by O

lemma OBdd.eq_root_disjoint_reachable_low_or_high {O : OBdd n m} (h : O.1.root = node j) :
    Disjoint
      (· = O.1.root)
      (fun p ↦ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)) := by
  intro P h1 h2 p hp
  specialize h1 p hp
  specialize h2 p hp
  simp_all only
  cases h2 with
  | inl l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_low l
  | inr l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_high l

/-- The `Edge` relation lifted to `RelevantPointer`s. -/
@[simp]
abbrev Bdd.RelevantEdge {n m} (B : Bdd n m) (p q : B.RelevantPointer) :=
  Edge B.heap p.1 q.1

lemma Bdd.relevantEdge_of_edge_of_reachable {n m}  {B : Bdd n m} {p q}
    (e : Edge B.heap p q) (hp : Reachable B.heap B.root p) :
  RelevantEdge B ⟨p, hp⟩ ⟨q, .snoc hp e⟩ := e

@[simp]
def RelevantPointer.var {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := p.1.toVar B.heap

@[simp]
def RelevantPointer.gap {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := n - (RelevantPointer.var p)

theorem RelevantEdge.flip_wellFounded (o : Ordered B) : WellFounded (flip (RelevantEdge B)) := by
  have : Subrelation (flip (RelevantEdge B)) (InvImage Nat.lt RelevantPointer.gap) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ e
    simp_all only [InvImage, flip, RelevantPointer.gap]
    apply Nat.sub_lt_sub_left
    cases e <;> simp
    simp [B.ordered_iff'.1 o y x hy e]
  exact Subrelation.wf this (InvImage.wf _ (Nat.lt_wfRel.wf))

instance RelevantEdge.instWellFoundedRelation {n m} (O : OBdd n m) : WellFoundedRelation O.1.RelevantPointer where
  rel := flip O.1.RelevantEdge
  wf  := (RelevantEdge.flip_wellFounded O.2)

lemma OBdd.reachable_from_node_iff' {n m j p} {O : OBdd n m} (h : O.1.root = node j) :
    Reachable O.1.heap O.1.root p ↔ p = O.1.root ∨ (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p) := by
  constructor
  · intro r
    cases r with
    | refl => left; rfl
    | cons e r =>
      rename_i q
      right
      rw [h] at e
      cases e with
      | low =>
        left
        rw [low_root_eq_low]
        exact r
      | high =>
        right
        rw [high_root_eq_high]
        exact r
  · intro r
    cases r with
    | inl r =>
      rw [r]
      left
    | inr r =>
      simp only [low_root_eq_low, high_root_eq_high] at r
      cases r with
      | inl r => exact .trans (O.bdd.reachable_low h) r
      | inr r => exact .trans (O.bdd.reachable_high h) r

lemma OBdd.card_reachable_node' {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card {p // Reachable O.1.heap O.1.root p} =
  Fintype.card {p // p = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)} := by
  apply Fintype.card_congr'
  conv =>
    lhs
    arg 1
    ext
    rw [reachable_from_node_iff' h]

lemma OBdd.card_reachable_node {n m j} {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card { q // Reachable O.1.heap O.1.root q } =
  1 + Fintype.card { q // Reachable (O.low h).1.heap (O.low h).1.root q ∨ Reachable (O.high h).1.heap (O.high h).1.root q } := by
  rw [card_reachable_node' h]
  rw [@Fintype.card_subtype_or_disjoint _ _ _ (eq_root_disjoint_reachable_low_or_high h) ..]
  · simp only [Fintype.card_unique, low_heap_eq_heap, add_right_inj]
    apply @Fintype.card_congr' ..
    · apply fintypeEitherRelevantPointer (O.low h) (O.high h); simp
    · simp
  · exact Fintype.subtypeEq O.1.root

@[no_expose, implicit_reducible]
instance OBdd.instDecidableReachable' {n m} (O : OBdd n m) (p : O.1.RelevantPointer) q :
    Decidable (Reachable O.1.heap p.val q) := by
  rcases p with ⟨p, hp⟩
  match p with
  | terminal b =>
    exact decidable_of_iff _ Reachable.terminal_iff.symm
  | node j =>
    let high := O.1.heap[j].high
    let low := O.1.heap[j].low
    suffices Decidable (q = node j ∨ Reachable O.bdd.heap high q ∨ Reachable O.bdd.heap low q) from
      decidable_of_iff _ Bdd.reachable_node_iff.symm
    refine @instDecidableOr _ _ ?_ (@instDecidableOr _ _ ?_ ?_)
    · exact decEq ..
    · have hr : Reachable O.1.heap O.1.root high :=
        Reachable.snoc hp Edge.high
      exact OBdd.instDecidableReachable' O ⟨high, hr⟩ q
    · have hr : Reachable O.1.heap O.1.root low :=
        Reachable.snoc hp Edge.low
      exact OBdd.instDecidableReachable' O ⟨low, hr⟩ q
termination_by p
decreasing_by
  all_goals simp_all only [flip, Bdd.RelevantEdge]
  · exact Edge.high
  · exact Edge.low

def OBdd.isTerminal {n m} (O : OBdd n m) := ∃ b, O.1.root = terminal b

lemma not_OEdge_of_isTerminal {O : OBdd n m}: O.isTerminal → ¬ OEdge O U := by
  rintro ⟨b, h⟩ ⟨_, contra⟩
  rw [h] at contra
  exact not_terminal_edge contra

lemma not_isTerminal_of_root_eq_node {n m} {j} {O : OBdd n m} (h : O.1.root = node j) : ¬ O.isTerminal := by
  rintro ⟨b, hb⟩
  rw [h] at hb
  contradiction

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

/-- The `OEdge` relation between Ordered BDDs is well-founded. -/
theorem OEdge.wellFounded {n m} : @WellFounded (OBdd n m) OEdge := by
  suffices s : Subrelation (@OEdge n m) (InvImage Nat.lt (OBdd.var ·)) from
    Subrelation.wf s (InvImage.wf _ (Nat.lt_wfRel.wf))
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
  simp_all only
  simp only [InvImage, OBdd.var, Nat.lt_eq, Fin.val_fin_lt, var]
  simp only [ordered_iff'] at hx
  rw [← h1] at h2 ⊢
  exact hx x.root y.root .refl h2

/-- The only reduced BDD that denotes a constant function is the terminal BDD. -/
theorem OBdd.terminal_of_constant (O : OBdd n m) :
    O.Reduced → O.evaluate = (fun _ ↦ b) → O.1.root = terminal b := by
  intro R h
  cases O_root_def : O.1.root
  case terminal b' =>
    grind only [OBdd.evaluate_terminal O_root_def]
  case node j =>
    exfalso
    refine not_reduced_of_sim_high_low O_root_def ?_ R
    have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
      ext I
      trans b
      · simp [evaluate_high_eq_evaluate_set_true, h]
      · simp [evaluate_low_eq_evaluate_set_false, h]
    exact OBdd.Canonicity (high_reduced R) (low_reduced R) this

lemma OBdd.reduced_var_dependent {n m} {O : OBdd n m} {p : Fin n} :
    O.Reduced → (∀ i : Fin p, Nary.IndependentOf (O.evaluate) ⟨i.1, by omega⟩) → p.1 ≤ O.1.var.1 := by
  intro hr hp
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp only [Nat.succ_eq_add_one, Bdd.var, O_root_def, Pointer.toVar_terminal]
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
    · simp only [Bdd.var, O_root_def, Pointer.toVar_node, Fin.eta] at this
      have := this true I
      rw [this]
      rw [OBdd.evaluate_node' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [↓reduceIte]
      suffices s : Nary.IndependentOf (O.high O_root_def).evaluate O.1.heap[j.1].var by rw [← s true I]
      refine independentOf_lt_root (O.high O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_high_var
      simp only [O.var_node O_root_def, Fin.getElem_fin]
    · symm
      simp only [Bdd.var, O_root_def, Pointer.toVar_node, Fin.eta] at this
      have := this false I
      rw [this]
      rw [OBdd.evaluate_node' O_root_def]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      simp only [Bool.false_eq_true, ↓reduceIte]
      suffices s : Nary.IndependentOf (O.low O_root_def).evaluate O.1.heap[j.1].var by rw [s false I]
      refine independentOf_lt_root (O.low O_root_def) ⟨O.1.heap[j.1].var.1, ?_⟩
      convert OBdd.var_lt_low_var
      simp only [O.var_node O_root_def, Fin.getElem_fin]

lemma Bdd.ordered_of_ordered_heap_not_reachable_set (O : OBdd n m) :
    ∀ i N, ¬ Reachable O.1.heap O.1.root (node i) → Ordered ⟨O.1.heap.set i N, O.1.root⟩ := by
  intro i N unr
  induction O using OBdd.init_inductionOn with
  | base b O' h1 h2 => exact ordered_of_terminal h2
  | step O' j h1 h2 ih_low ih_high =>
    have h3 : i ≠ j := by
      intro contra
      rw [contra] at unr
      rw [h2] at unr
      apply unr
      left
    apply ordered_of_low_high_ordered (by rw [h2])
    · simp only [low, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      apply ih_low
      intro h4
      apply unr
      trans O'.1.heap[j].low
      · exact O'.bdd.reachable_low h2
      · exact h4
    · simp only [var_eq, low, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      rw [h2, toVar_heap_set h3]
      have h4 : toVar O'.1.heap (node j) < toVar O'.1.heap O'.1.heap[j].low :=
        ordered_iff'.1 O'.ordered (node j) O'.1.heap[j].low (h2 ▸ .refl) Edge.low
      convert h4 using 1
      cases low_def : O.1.heap[j].low with
      | terminal bl =>
        simp_all only [Fin.getElem_fin, toVar_terminal]
      | node jl =>
        simp only [← h1, Fin.getElem_fin] at low_def
        simp only [low_def, Fin.getElem_fin]
        simp only [Fin.ext_iff, toVar_node, Fin.getElem_fin]
        rw [Vector.getElem_set_ne i.2 jl.2]
        simp only [ne_eq, Fin.val_inj]
        intro rfl
        apply unr
        rw [← low_def]
        exact O'.bdd.reachable_low h2
    · simp only [high, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      apply ih_high
      intro h4
      apply unr
      trans O'.1.heap[j].high
      · exact O'.bdd.reachable_high h2
      · exact h4
    · simp only [var_eq, high, Fin.getElem_fin]
      rw [Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne h3)]
      rw [h2, toVar_heap_set h3]
      have h4 : toVar O'.1.heap (node j) < toVar O'.1.heap O'.1.heap[j].high :=
        ordered_iff'.1 O'.ordered (node j) O'.1.heap[j].high (h2 ▸ .refl) Edge.high
      convert h4 using 1
      cases high_def : O.1.heap[j].high with
      | terminal bl =>
        simp_all only [Fin.getElem_fin, toVar_terminal]
      | node jl =>
        simp only [← h1, Fin.getElem_fin] at high_def
        simp only [high_def, Fin.getElem_fin]
        simp only [Fin.ext_iff, toVar_node, Fin.getElem_fin]
        rw [Vector.getElem_set_ne i.2 jl.2]
        simp only [ne_eq, Fin.val_inj]
        intro rfl
        apply unr
        rw [← high_def]
        exact O'.bdd.reachable_high h2

lemma OBdd.ordered_of_edge {n m} {O : OBdd n m} (p : Pointer m) :
    Edge O.bdd.heap O.bdd.root p → Bdd.Ordered {heap := O.bdd.heap, root := p} := by
  intro e
  exact ordered_of_relevant O ⟨p, Reachable.ofEdge e⟩

lemma OBdd.evaluate_eq_of_forall_usesVar {O : OBdd n m} {I J : Vector Bool n} :
    (∀ i, O.1.usesVar i → I[i] = J[i]) → O.evaluate I = O.evaluate J := by
  intro h
  apply Nary.eq_of_forall_dependency_getElem_eq
  rintro ⟨i, hi⟩
  apply h
  simp only [Nary.DependsOn, Nary.IndependentOf, not_forall] at hi
  rcases hi with ⟨b, v, hbv⟩
  apply usesVar_of_dependsOn hbv

namespace Size

lemma isTerminal_iff_size_eq_zero {n m} {O : OBdd n m} : size O = 0 ↔ O.isTerminal := by
  constructor
  · intro h
    simp only [size, Function.comp_apply, List.length_eq_zero_iff] at h
    cases O_root_def : O.1.root with
    | terminal b => use b
    | node j =>
      have := Collect.collect_spec (j := j) (by rw [O_root_def]; exact Pointer.Reachable.refl)
      rw [h] at this
      contradiction
  · rintro ⟨b, hb⟩
    simp [size, Collect.collect_terminal hb]

def bool_of_size_eq_zero {n m} (O : OBdd n m) (h : size O = 0) : Bool :=
  match O_root_def : O.1.root with
  | .terminal b => b
  | .node _ => False.elim (not_isTerminal_of_root_eq_node O_root_def (isTerminal_iff_size_eq_zero.mp h))

end Size
