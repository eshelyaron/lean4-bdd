import Bdd.Basic
import Bdd.Collect
import Bdd.Trim

open Pointer
open Bdd

def OBdd.discover_helper : List (Fin m) → Vector (Node n m ) m → Vector (List (Fin m)) n → Vector (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => discover_helper tail v (I.set v[head].var (head :: I[v[head].var]))

lemma OBdd.discover_helper_retains_found (O : OBdd n m) {I : Vector (List (Fin m)) n} {i : Fin n}: j ∈ I[i] → j ∈ (discover_helper l v I)[i] := by
  intro h
  cases l with
  | nil => assumption
  | cons head tail =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    cases decEq v[head.1].var i with
    | isFalse hf =>
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hf])]
      assumption
    | isTrue  ht =>
      subst ht
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_self]
      right
      assumption

lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vector (List (Fin m)) n} :
    j ∈ l → j ∈ (discover_helper l v I).get v[j].var := by
  intro h
  cases h with
  | head as =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_set_self]
    left
  | tail b ih =>
    simp [discover_helper]
    apply discover_helper_spec O ih

/-- Return a vector whose `v`th entry is a list of node indices with variable index `v`.

This is a subroutine of `reduce`.  -/
def OBdd.discover (O : OBdd n m) : Vector (List (Fin m)) n := discover_helper (Collect.collect O) O.1.heap (Vector.replicate n [])

/-- `discover` is correct. -/
theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (discover O).get O.1.heap[j].var :=
  (discover_helper_spec O) ∘ Collect.collect_spec

/-- `discover` is correct. -/
theorem OBdd.discover_spec_reverse {O : OBdd n m} {j : Fin m} :
    j ∈ (discover O).get i → (Reachable O.1.heap O.1.root (node j)) ∧ O.1.heap[j].var = i := sorry

namespace Reduce
structure State (n) (m) where
  out : Vector (Node n m) m
  ids : Vector (Pointer m) m
  nid : Fin m

def initial {n m : Nat} : State n.succ m.succ :=
  ⟨ (Vector.replicate m.succ {var := 0, low := terminal false, high := terminal true}),
    (Vector.replicate m.succ (terminal false)),
    Fin.last m
  ⟩

def get_out : StateM (State n m) (Vector (Node n m) m) := get >>= fun s ↦ pure s.out

def get_id : Pointer m → StateM (State n m) (Pointer m)
  | terminal b => pure (terminal b)
  | node j => get >>= fun s ↦ pure (s.ids[j])

def set_id : Fin m → Pointer m → StateM (State n m) Unit :=
  fun j p ↦ get >>= fun s ↦ set (⟨s.out, s.ids.set j p, s.nid⟩ : State n m)

def set_id_to_nid : Fin m → StateM (State n m) Unit :=
  fun j ↦ get >>= fun s ↦ set_id j (node s.nid)

def set_out {n m : Nat} : Node n.succ m.succ → StateM (State n.succ m.succ) Unit :=
  fun N ↦ get >>= fun s ↦
    have : (s.nid.1 + 1) % m.succ < m.succ := by simp [Nat.mod_lt]
    set (⟨s.out.set ((s.nid.1 + 1) % m.succ) N, s.ids, s.nid + 1⟩ : State n.succ m.succ)

@[simp]
lemma set_out_preserves_ids {n m : Nat} {s : State n.succ m.succ} {p : Node n.succ m.succ} : (set_out p s).2.ids = s.ids := by
  simp [set_out, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]

@[simp]
lemma set_out_preserves_id {n m : Nat} {s : State n.succ m.succ} {p : Node n.succ m.succ} {j : Pointer m.succ}: (get_id j (set_out p s).2).1 = (get_id j s).1 := by
  nth_rw 1 [get_id.eq_def]
  split
  next =>
    simp only [pure, StateT.pure, get_id]
  next =>
    simp only [bind, StateT.bind, pure, get, getThe, MonadStateOf.get, StateT.get, StateT.pure, get_id]
    rw [set_out_preserves_ids]

def populate_queue (v : Vector (Node n m) m) (acc : List ((Pointer m × Pointer m) × Fin m)) : List (Fin m) → StateM (State n m) (List ((Pointer m × Pointer m) × Fin m))
  | [] => pure acc
  | j :: tail => do
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    if decide (lid = hid)
    then
      -- `node j` is redundant in the original BDD.
      --  Reduce it by mapping it to its child `lid` in the output BDD.
      set_id j lid
      populate_queue v acc tail
    else populate_queue v (⟨⟨lid, hid⟩, j⟩ :: acc) tail

def process_record {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) : (Pointer m.succ × Pointer m.succ) × Fin m.succ → StateM (State n.succ m.succ) (Pointer m.succ × Pointer m.succ) := fun ⟨key, j⟩ ↦ do
  if key = curkey
  then
    -- isomorphism in original BDD, reduce.
    set_id_to_nid j
    pure curkey
  else
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    set_out ⟨v[j].var, lid, hid⟩
    set_id_to_nid j
    pure key

def process_queue {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) :
  List ((Pointer m.succ × Pointer m.succ) × Fin m.succ) → StateM (State n.succ m.succ) Unit
  | [] => pure ()
  | head :: tail => do
    let newkey ← process_record v curkey head
    process_queue v newkey tail

def step {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) Unit := do
  let Q ← populate_queue v [] vlist[i]
  process_queue v ⟨node 0, node 0⟩ (List.mergeSort Q)

def loop {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) (Bdd n.succ m.succ) := do
  step v vlist i
  match h : i.1 - v[r].var.1 with
  | Nat.zero =>
    let out ← get_out
    let rid ← get_id (node r)
    pure {heap := out, root := rid}
  | Nat.succ j =>
    loop v r vlist ⟨(j + v[r].var.1), by omega⟩
termination_by i.1 - v[r].var.1
decreasing_by simp_all

theorem loop_induction {n m : Nat} {motive : Bdd n.succ m.succ → Prop}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) (s : State n.succ m.succ)
    (one : i.1 - v[r].var.1 = 0 → motive {heap := (step v vlist i s).2.out, root := (get_id (node r) (step v vlist i s).2).1})
    (two : ∀ (d : Nat), (h : i.1 - v[r].var.1 = d.succ) → motive (loop v r vlist ⟨(d + v[r].var.1), by omega⟩ (step v vlist i s).2).1) :
    motive (loop v r vlist i s).1 := by
  unfold loop
  split
  next h =>
    simp only [bind, StateT.bind, get_out, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
    split
    next s1 heq =>
      split
      next p s2 hheq =>
        have s1_def : s1 = (step v vlist i s).2 := by rw [heq]
        convert (one h)
        rw [← s1_def, hheq]
  next d h =>
    simp only [bind, StateT.bind, get_out, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
    split
    next s1 heq =>
      convert (two d h)
      rw [heq]

def reduce {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ :=
  match O.1.root with
  | terminal _ => O.1 -- Terminals are already reduced.
  | node r => (StateT.run (loop O.1.heap r (OBdd.discover O) n) initial).1

def GoodNid {n m : Nat} (O : OBdd n.succ m.succ)  (s : State n.succ m.succ) : Prop :=
    ∀ (j : Fin m.succ), j < s.nid + 1 →
    let B : Bdd n.succ m.succ := {heap := s.out, root := node j}
      ∃ (hB : B.Ordered), OBdd.Reduced ⟨B, hB⟩
    ∧ ∃ (j' : Fin m.succ) (hj : Reachable O.1.heap O.1.root (node j')), (get_id (node j') s).1 = (node j)
    ∧ OBdd.evaluate ⟨B, hB⟩ = OBdd.evaluate ⟨{heap := O.1.heap, root := node j'}, ordered_of_relevant O ⟨node j', hj⟩⟩

def GoodInputPointer {n m : Nat} (O : OBdd n.succ m.succ) (s : State n.succ m.succ) (j : Fin m.succ) (hj : Reachable O.1.heap O.1.root (node j)) : Prop :=
    let p := (get_id (node j) s).1
    let B : Bdd n.succ m.succ := {heap := s.out, root := p}
    ∃ (hB : B.Ordered), OBdd.Reduced ⟨B, hB⟩
    ∧ OBdd.evaluate ⟨{heap := O.1.heap, root := node j}, ordered_of_relevant O ⟨node j, hj⟩⟩ = OBdd.evaluate ⟨B, hB⟩

def GoodVar {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) : Prop :=
    ∀ (j : Fin m.succ), (hj : Reachable O.1.heap O.1.root (node j)) → i < O.1.heap[j].var → GoodInputPointer O s j hj

def GreatVar {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) : Prop :=
    ∀ (j : Fin m.succ), (hj : Reachable O.1.heap O.1.root (node j)) → i ≤ O.1.heap[j].var → GoodInputPointer O s j hj

lemma GoodNid_of_initial {n m : Nat} {O : OBdd n.succ m.succ} : GoodNid O initial := by
  intro _ h
  simp [initial] at h

lemma GoodVar_of_initial {n m : Nat} {O : OBdd n.succ m.succ} : GoodVar O n initial := by
  intro _ _ contra
  apply Fin.ne_last_of_lt at contra
  simp at contra

def Invariant {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) : Prop :=
  GoodNid O s ∧ GoodVar O i s

def Invariant' {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) : Prop :=
  GoodNid O s ∧ GreatVar O i s

lemma Invariant_of_Invariant' {n m : Nat} {O : OBdd n.succ m.succ} {i i' : Fin n.succ} {s : State n.succ m.succ} :
    Invariant' O i s → i.1 = i'.1.succ → Invariant O i' s := by
  intro h1 h2
  constructor
  · exact h1.1
  · intro j hj h
    apply h1.2
    omega

lemma Invariant_of_initial {n m : Nat} (O : OBdd n.succ m.succ) : Invariant O n initial :=
 ⟨GoodNid_of_initial, GoodVar_of_initial⟩

@[simp]
lemma get_id_preserves_state : (get_id p s).2 = s := by
  simp [get_id]
  split <;> rfl

@[simp]
lemma set_id_preserves_nid : (set_id j p s).2.nid = s.nid := by
  simp [set_id, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]

@[simp]
lemma set_id_preserves_out : (set_id j p s).2.out = s.out := by
  simp [set_id, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]

@[simp]
lemma set_id_to_nid_preserves_nid : (set_id_to_nid j s).2.nid = s.nid := by
  simp [set_id_to_nid, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]

@[simp]
lemma set_id_to_nid_preserves_out : (set_id_to_nid j s).2.out = s.out := by
  simp [set_id_to_nid, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]

lemma set_id_to_nid_preserves_GoodNid {n m : Nat} {j : Fin m.succ} {O : OBdd n.succ m.succ} {s : State n.succ m.succ} :
   (get_id (node j) s).1 = terminal false → GoodNid O s → GoodNid O (set_id_to_nid j s).2 := by
  intro hj h
  simp only [set_id_to_nid, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set_id, set, StateT.set, pure]
  intro jj hjj
  rcases h jj hjj with ⟨o, hh, jo, hjo, hhh1, hhh2⟩
  use o
  constructor
  · exact hh
  · use jo
    use hjo
    constructor
    · rw [← hhh1]
      simp only [get_id, get, getThe, MonadStateOf.get, bind, StateT.bind, pure, StateT.pure, StateT.get, Fin.getElem_fin]
      apply Vector.getElem_set_ne
      intro contra
      apply Fin.eq_of_val_eq at contra
      rw [contra] at hj
      rw [hj] at hhh1
      contradiction
    · assumption

lemma set_out_preserves_ordered {n m : Nat} {j : Fin m.succ} {s : State n.succ m.succ} {N : Node n.succ m.succ}:
    Bdd.Ordered {heap := s.out, root := node j} → Bdd.Ordered {heap := (set_out N s).2.out, root := node j} := by
  intro h
  simp only [set_out, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure]
  intro x y e
  sorry

-- def populate_queue (v : Vec (Node n m) m) (acc : List ((Pointer m × Pointer m) × Fin m)) : List (Fin m) → StateM (State n m) (List ((Pointer m × Pointer m) × Fin m))
--   | [] => pure acc
--   | j :: tail => do
--     let lid ← get_id v[j].low
--     let hid ← get_id v[j].high
--     if decide (lid = hid)
--     then
--       -- `node j` is redundant in the original BDD.
--       --  Reduce it by mapping it to its child `lid` in the output BDD.
--       set_id j lid
--       populate_queue v acc tail
--     else populate_queue v (⟨⟨lid, hid⟩, j⟩ :: acc) tail

lemma get_id_set_id_of_ne (h : i ≠ j) : (get_id (node j) (set_id i p s).2).1 = (get_id (node j) s).1 := by
  apply Vector.getElem_set_ne
  · simp_all only [ne_eq, Fin.is_lt]
  · simp_all only [ne_eq, Fin.is_lt, Fin.val_ne_of_ne h, not_false_eq_true]

lemma populate_queue_preserves_invariant_helper {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (nodes : List (Fin m.succ)) :
    (∀ j ∈ nodes, O.1.heap[j].var = i ∧ (get_id (node j) s).1 = terminal false) →
    List.Nodup nodes →
    Invariant O i s → Invariant O i (populate_queue O.1.heap acc nodes s).2 := by
  rintro hi nd h
  unfold populate_queue
  split
  next => simp [pure, StateT.pure]; assumption
  next head tail =>
    simp only [Nat.succ_eq_add_one, bind, StateT.bind, Ordered.eq_1, decide_eq_true_eq]
    split
    next lid s' hsl =>
      have ss' : s' = s := by
        calc s'
          _ = (lid, s').2 := rfl
          _ = (get_id O.1.heap[head].low s).2 := by rw [hsl]
          _ = s := get_id_preserves_state
      symm at ss'
      subst ss'
      split
      next hid s' hsh =>
        have ss' : s' = s := by
          calc s'
            _ = (lid, s').2 := rfl
            _ = (get_id O.1.heap[head].high s).2 := by rw [hsh]
            _ = s := get_id_preserves_state
        symm at ss'
        subst ss'
        split
        next ht =>
          simp only [StateT.bind, Id.bind_eq]
          apply populate_queue_preserves_invariant_helper
          · intros j hj
            have head_nin_tail : head ∉ tail := (List.nodup_cons.mp nd).1
            have head_ne_j : head ≠ j := by
              intro contra
              rw [contra] at head_nin_tail
              exact head_nin_tail hj
            rw [get_id_set_id_of_ne head_ne_j]
            apply hi
            right
            assumption
          · exact List.Nodup.of_cons nd
          · constructor
            · simp only [GoodNid]
              simp only [set_id_preserves_nid, set_id_preserves_out]
              intro j hj
              rcases h.1 j hj with ⟨o, r, j', hj', h1, h2⟩
              have head_ne_j' : head ≠ j' := by
                intro contra
                have := (hi j' (by rw [contra]; left)).2
                rw [this] at h1
                contradiction
              use o
              constructor
              · assumption
              · use j'
                use hj'
                constructor
                · rw [get_id_set_id_of_ne head_ne_j']
                  assumption
                · assumption
            · simp only [GoodVar, GoodInputPointer]
              intro j hj hh
              have head_ne_j : head ≠ j := by
                intro contra
                have := (hi head (by left)).1
                rw [contra] at this
                rw [this] at hh
                exact (lt_self_iff_false i).mp hh
              rcases h.2 j hj hh with ⟨o, h1, h2⟩
              simp only [set_id_preserves_nid, set_id_preserves_out]
              rw [get_id_set_id_of_ne head_ne_j]
              use o
        next hf =>
          apply populate_queue_preserves_invariant_helper
          · intros; apply hi; right; assumption
          · exact List.Nodup.of_cons nd
          · assumption

lemma populate_queue_preserves_invariant {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) :
    (∀ j ∈ O.discover[i], (get_id (node j) s).1 = terminal false) →
    Invariant O i s → Invariant O i (populate_queue O.1.heap [] (O.discover)[i] s).2 := by
  intro h
  apply populate_queue_preserves_invariant_helper
  · intro j hj
    constructor
    · sorry
    · apply h j hj
  . sorry

-- lemma populate_queue_spec {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) :
--     (∀ j ∈ O.discover[i], (get_id (node j) s).1 = terminal false) →
--     Invariant O i s →
--     ∀ j ∈ O.discover[i],
--       let ⟨Q, s1⟩ := populate_queue O.1.heap [] O.discover[i] s
--       ∃ rcrd ∈ Q,
--         let l := ({heap := s1.out, root := rcrd.1.1} : Bdd n.succ m.succ)
--         let h := ({heap := s1.out, root := rcrd.1.2} : Bdd n.succ m.succ)
--         (∃ (hl : Bdd.Ordered l) (hh : Bdd.Ordered h),
--         OBdd.evaluate ⟨{heap := O.1.heap, root := node j}, ordered_of_relevant O ⟨node j, sorry⟩⟩ =
--         fun I ↦ if I[O.1.heap[j].var] then (OBdd.evaluate ⟨h, hh⟩ I) else  (OBdd.evaluate ⟨l, hl⟩ I)) := by
--   sorry

lemma populate_queue_accumulates {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (s : State n.succ m.succ) (r : (Pointer m.succ × Pointer m.succ) × Fin m.succ) (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (nodes : List (Fin m.succ)) :
    r ∈ acc → r ∈ (populate_queue v acc nodes s).1 := by
  intro hrin
  cases nodes with
  | nil => simp only [Nat.succ_eq_add_one, populate_queue, pure, StateT.pure]; assumption
  | cons head tail =>
    simp only [Nat.succ_eq_add_one, populate_queue, bind, StateT.bind, decide_eq_true_eq]
    split
    next lid s1 lheq =>
      split
      next hid s2 hheq =>
        split
        next ht =>
          exact populate_queue_accumulates v (set_id head lid s2).2 r acc tail hrin
        next hf =>
          exact populate_queue_accumulates v s2 r _ tail (.tail _ hrin)

lemma populate_queue_spec_helper2 {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (nodes : List (Fin m.succ)) :
    (hnodes : ∀ j ∈ nodes, (get_id (node j) s).1 = terminal false ∧ Reachable O.1.heap O.1.root (node j) ∧ i = O.1.heap[j].var) →
    Invariant O i s →
    ∀ j (hjin : j ∈ nodes),
      let ⟨Q, s1⟩ := populate_queue O.1.heap acc nodes s
      ∃ rcrd ∈ Q,
        let l := ({heap := s1.out, root := rcrd.1.1} : Bdd n.succ m.succ)
        let h := ({heap := s1.out, root := rcrd.1.2} : Bdd n.succ m.succ)
        (∃ (hl : Bdd.Ordered l) (hh : Bdd.Ordered h),
        OBdd.evaluate ⟨{heap := O.1.heap, root := node j}, ordered_of_relevant O ⟨node j, (hnodes j hjin).2.1⟩⟩ =
        fun I ↦ if I[O.1.heap[j].var] then (OBdd.evaluate ⟨h, hh⟩ I) else  (OBdd.evaluate ⟨l, hl⟩ I)) := by
  intro hnodes hinv j hjin
  split
  next Q s3 heq =>
    unfold populate_queue at heq
    split at heq
    next => contradiction
    next head tail =>
      simp only [bind, StateT.bind, decide_eq_true_eq] at heq
      split at heq
      next lid s1 lheq =>
        split at heq
        next hid s2 hheq =>
          split at heq
          next ht =>
            simp only [Nat.succ_eq_add_one, StateT.bind, Ordered.eq_1, Id.bind_eq] at heq
            sorry
          next hf =>
            cases hjin with
            | head as =>
              use ((lid, hid), j)
              constructor
              · have : (populate_queue O.1.heap (((lid, hid), j) :: acc) tail s2).1 = Q := by rw [heq]
                rw [← this]
                apply populate_queue_accumulates
                left
              · simp only
                sorry
            | tail b hjin =>
              have that : ∀ j ∈ tail, (get_id (node j) s2).1 = terminal false ∧ Reachable O.1.heap O.1.root (node j) ∧ i = O.1.heap[j].var := by
                intro j' hj'
                constructor
                · sorry
                · exact (hnodes j' (.tail _ hj')).2
              have hinv2 : Invariant O i s2 := by
                have : s2 = (get_id O.1.heap[head].high s1).2 := by rw [hheq]
                rw [this]
                rw [get_id_preserves_state]
                have : s1 = (get_id O.1.heap[head].low s).2 := by rw [lheq]
                rw [this]
                rw [get_id_preserves_state]
                assumption
              have := populate_queue_spec_helper2 O i s2 (((lid, hid), head) :: acc) tail that hinv2 j hjin
              rw [heq] at this
              simp only at this
              assumption

lemma populate_queue_spec_helper {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (nodes : List (Fin m.succ)) :
    (hnodes : ∀ j ∈ nodes, (get_id (node j) s).1 = terminal false ∧ Reachable O.1.heap O.1.root (node j) ∧ i = O.1.heap[j].var) →
    Invariant O i s →
    ∀ j (hjin : j ∈ nodes),
      let ⟨Q, s1⟩ := populate_queue O.1.heap acc nodes s
      (∃ rcrd ∈ Q, rcrd.2 = j ∧ rcrd.1.1 = (get_id O.1.heap[j].low s1).1 ∧ rcrd.1.2 = (get_id O.1.heap[j].high s1).1) ∨
      (GoodInputPointer O s1 j (hnodes j hjin).2.1) := by
  intro hnodes hinv j hjin
  split
  next Q s3 heq =>
    unfold populate_queue at heq
    split at heq
    next => contradiction
    next head tail =>
      simp only [bind, StateT.bind, decide_eq_true_eq] at heq
      split at heq
      next lid s1 lheq =>
        split at heq
        next hid s2 hheq =>
          split at heq
          next ht =>
            simp only [Nat.succ_eq_add_one, StateT.bind, Ordered.eq_1, Id.bind_eq] at heq
            right
            sorry
          next hf =>
            left
            cases hjin with
            | head as =>
              use ((lid, hid), j)
              constructor
              · have : (populate_queue O.1.heap (((lid, hid), j) :: acc) tail s2).1 = Q := by rw [heq]
                rw [← this]
                apply populate_queue_accumulates
                left
              · constructor
                · rfl
                · constructor
                  · simp only; sorry
                  · simp only; sorry
            | tail b hjin =>
              have that : ∀ j ∈ tail, (get_id (node j) s2).1 = terminal false ∧ Reachable O.1.heap O.1.root (node j) ∧ i = O.1.heap[j].var := by
                intro j' hj'
                constructor
                · sorry
                · exact (hnodes j' (.tail _ hj')).2
              have hinv2 : Invariant O i s2 := by
                have : s2 = (get_id O.1.heap[head].high s1).2 := by rw [hheq]
                rw [this]
                rw [get_id_preserves_state]
                have : s1 = (get_id O.1.heap[head].low s).2 := by rw [lheq]
                rw [this]
                rw [get_id_preserves_state]
                assumption
              have := populate_queue_spec_helper O i s2 (((lid, hid), head) :: acc) tail that hinv2 j hjin
              rw [heq] at this
              simp only at this
              sorry--assumption

-- XXX Also look at bv_decide

lemma populate_queue_spec {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) :
    (∀ (j : Fin m.succ) (hj : Reachable O.1.heap O.1.root (node j)), i = O.1.heap[j].var → (get_id (node j) s).1 = terminal false) →
    Invariant O i s →
    ∀ (j : Fin m.succ) (hj : Reachable O.1.heap O.1.root (node j)), i = O.1.heap[j].var →
      let ⟨Q, s1⟩ := populate_queue O.1.heap [] O.discover[i] s
      (∃ rcrd ∈ Q, rcrd.2 = j ∧ rcrd.1.1 = (get_id O.1.heap[j].low s1).1 ∧ rcrd.1.2 = (get_id O.1.heap[j].high s1).1) ∨
      (GoodInputPointer O s1 j hj) := by
  intro hids hinv j hj hi
  have hjin : j ∈ O.discover[i] := by
    rw [hi]
    exact OBdd.discover_spec hj
  sorry

-- def process_queue {n m : Nat} (v : Vec (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) :
--   List ((Pointer m.succ × Pointer m.succ) × Fin m.succ) → StateM (State n.succ m.succ) Unit
--   | [] => pure ()
--   | head :: tail => do
--     let newkey ← process_record v curkey head
--     process_queue v newkey tail

-- def process_record {n m : Nat} (v : Vec (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) : (Pointer m.succ × Pointer m.succ) × Fin m.succ → StateM (State n.succ m.succ) (Pointer m.succ × Pointer m.succ) := fun ⟨key, j⟩ ↦ do
--   if key = curkey
--   then
--     -- isomorphism in original BDD, reduce.
--     set_id_to_nid j
--     pure curkey
--   else
--     let lid ← get_id v[j].low
--     let hid ← get_id v[j].high
--     set_out ⟨v[j].var, lid, hid⟩
--     set_id_to_nid j
--     pure key

lemma process_record_spec {n m : Nat} (O : OBdd n.succ m.succ) (curkey : Pointer m.succ × Pointer m.succ) (rcrd : (Pointer m.succ × Pointer m.succ) × Fin m.succ) (s : State n.succ m.succ) :
    (get_id (node rcrd.2) s).1 = terminal false → GoodNid O s → GoodNid O (process_record O.1.heap curkey rcrd s).2 := by
  intro hf h
  unfold process_record
  split
  next k j =>
    split
    next hh =>
      simp only [bind, StateT.bind]
      split
      next s1 heq =>
        simp only [pure, StateT.pure]
        rw [show s1 = (set_id_to_nid j s).2 by rw [heq]]
        exact set_id_to_nid_preserves_GoodNid hf h
    next hk =>
      simp only [bind, StateT.bind]
      split
      next lid s1 heq =>
        split
        next hid s2 heqq =>
          split
          next s3 heqqq =>
            split
            next s4 heqqqq =>
              simp [pure, StateT.pure]
              rw [show s4 = (set_id_to_nid j s3).2 by rw [heqqqq]]
              have s3_def : s3 = (set_out { var := O.1.heap[j].var, low := lid, high := hid } s2).2 := by rw [heqqq]
              have s2_def : s2 = (get_id O.1.heap[j].high s1).2 := by rw [heqq]
              have s1_def : s1 = (get_id O.1.heap[j].low s).2 := by rw [heq]
              apply set_id_to_nid_preserves_GoodNid
              · simp only at hf
                simp only [s3_def, set_out_preserves_id, s2_def, get_id_preserves_state, s1_def]
                assumption
              · intro jj hjj
                cases Fin.decLt jj s3.nid with
                | isFalse hf => sorry
                | isTrue ht =>
                  have s3_nid_def : s3.nid = s.nid + 1 := by
                    simp [set_out, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, get_id_preserves_state, *]
                  rw [s3_nid_def] at ht
                  rcases h jj ht with ⟨ho, hh⟩
                  have : Bdd.Ordered { heap := s2.out, root := node jj } := by
                    simpa only [s2_def, get_id_preserves_state, s1_def]
                  nth_rw 1 [s3_def]

                  sorry


lemma process_queue_spec {n m : Nat} (O : OBdd n.succ m.succ) (curkey : Pointer m.succ × Pointer m.succ) (Q : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (s : State n.succ m.succ) :
    GoodNid O s →  GoodNid O (process_queue O.1.heap curkey Q s).2 := by
  intro h
  unfold process_queue
  split
  next =>
    simp only [pure, StateT.pure]
    sorry
  next head tail =>
    simp only [bind, StateT.bind]
    split
    next p s1 heq =>
      apply process_queue_spec
      sorry


def step_spec {n m : Nat} {O : OBdd n.succ m.succ} {i : Fin n.succ} {s : State n.succ m.succ} :
    Invariant O i s → Invariant' O i (step O.1.heap O.discover i s).2 := by
  intro hinv
  simp only [step, bind, StateT.bind]
  split
  next Q s1 heq =>
    generalize s2_def : (process_queue O.1.heap (node 0, node 0) (Q.mergeSort fun a b ↦ decide (a ≤ b)) s1).2 = s2
    constructor
    · intro j hj

      sorry
    · sorry

def loop_spec_helper_ordered {n m : Nat} {O : OBdd n.succ m.succ} {r} {i} {s} :
    Invariant O i s →
    O.1.root = node r →
    (loop O.1.heap r O.discover i s).1.Ordered := by
  intro hinv O_root_def
  unfold loop
  split
  next h =>
    simp only [bind, StateT.bind, get_out, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, get_id]
    split
    next s1 hh =>
      simp only
      have : Invariant' O i s1 := by convert step_spec hinv; rw [hh]
      have := (this.2 r (by rw [O_root_def]; left) (Nat.sub_eq_zero_iff_le.mp h))
      cases this with
      | intro w h =>
        simp only [get_id, bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get] at w
        assumption
  next d h =>
    simp only [bind, StateT.bind]
    split
    next s1 hh =>
      refine loop_spec_helper_ordered ?_ O_root_def
      generalize ddef : (⟨(d + O.1.heap[r].var.1), by omega⟩ : Fin n.succ) = i'
      have := (Nat.lt_of_sub_eq_succ h)
      have := (Nat.sub_eq_iff_eq_add (Nat.le_of_lt this)).mp h
      have hii' : i.1 = i'.1.succ := by rw [this, ← ddef]; simp only; omega
      have inv' : Invariant' O i s1 := by convert step_spec hinv; rw [hh]
      apply Invariant_of_Invariant' inv' hii'
termination_by i.1 - O.1.heap[r].var.1
decreasing_by simp_all

def loop_spec_helper' {n m : Nat} {O : OBdd n.succ m.succ} {r} {i} {s} :
    Invariant O i s →
    O.1.root = node r →
    let R := (loop O.1.heap r O.discover i s).1
    ∃ (ho : R.Ordered), OBdd.Reduced ⟨R, ho⟩ ∧ O.evaluate = OBdd.evaluate ⟨R, ho⟩ := by
  intro hinv O_root_def
  apply loop_induction (motive := fun R ↦ ∃ (ho : R.Ordered), OBdd.Reduced ⟨R, ho⟩ ∧ O.evaluate = OBdd.evaluate ⟨R, ho⟩)
  · intro h
    have : (loop O.1.heap r O.discover i s).1.Ordered := loop_spec_helper_ordered hinv O_root_def
    unfold loop at this
    split at this
    next hh =>
      use this
      have : Invariant' O i (step O.1.heap O.discover i s).2 := by convert step_spec hinv
      have := (this.2 r (by rw [O_root_def]; left) (Nat.sub_eq_zero_iff_le.mp h))
      cases this with
      | intro w hhh =>
        constructor
        · exact hhh.1
        · convert hhh.2; simp_rw [← O_root_def]; rfl
    next d contra => rw [h] at contra; contradiction
  · intro d h
    apply loop_spec_helper' ?_ O_root_def
    generalize ddef : (⟨(d + O.1.heap[r].var.1), by omega⟩ : Fin n.succ) = i'
    have := (Nat.lt_of_sub_eq_succ h)
    have := (Nat.sub_eq_iff_eq_add (Nat.le_of_lt this)).mp h
    have hii' : i.1 = i'.1.succ := by rw [this, ← ddef]; simp only; omega
    have inv' : Invariant' O i (step O.1.heap O.discover i s).2 := by convert step_spec hinv
    apply Invariant_of_Invariant' inv' hii'
termination_by i.1 - O.1.heap[r].var.1
decreasing_by simp_all

-- def loop_spec_helper {n m : Nat} {O : OBdd n.succ m.succ} {r} {i} {s} :
--     Invariant O i s →
--     O.1.root = node r →
--     let R := (loop O.1.heap r O.discover i s).1
--     ∃ (ho : R.Ordered), OBdd.Reduced ⟨R, ho⟩ := by
--   intro hinv O_root_def
--   use loop_spec_helper_ordered hinv O_root_def
--   split_ands
--   · simp only
--     unfold loop
--     split
--     next h =>
--       simp only [bind, StateT.bind, get_out, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, get_id]
--       split
--       next s1 hh =>
--         simp only
--         have hinv' : Invariant' O i s1 := by convert step_spec hinv; rw [hh]
--         exact (hinv'.2 r (by rw [O_root_def]; left) (Nat.sub_eq_zero_iff_le.mp h)).2.1.1
--     next j h =>
--       simp only [bind, StateT.bind]
--       split
--       next s1 hh =>
--         refine (loop_spec_helper ?_ O_root_def).2.1
--         generalize ddef : (⟨(j + O.1.heap[r].var.1), by omega⟩ : Fin n.succ) = i'
--         have := (Nat.lt_of_sub_eq_succ h)
--         have := (Nat.sub_eq_iff_eq_add (Nat.le_of_lt this)).mp h
--         have hii' : i.1 = i'.1.succ := by rw [this, ← ddef]; simp only; omega
--         have inv' : Invariant' O i s1 := by convert step_spec hinv; rw [hh]
--         apply Invariant_of_Invariant' inv' hii'
--   · -- simp only [bind, StateT.bind, get_out, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, get_id]
--     -- simp only [Nat.succ_eq_add_one, Ordered.eq_1, Nat.zero_eq]
--     simp only [Subrelation, OBdd.SimilarRP, InvImage, OBdd.Similar]
--     sorry
--     -- simp only loop
--     -- simp only [bind, StateT.bind, get_out, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, get_id]

--     -- sorry
-- termination_by i.1 - O.1.heap[r].var.1
-- decreasing_by simp_all


-- def loop_spec_helper {n m : Nat} {O : OBdd n.succ m.succ} {r} {i} {s} :
--     Invariant O i s →
--     O.1.root = node r →
--     let R := (loop O.1.heap r O.discover i s).1
--     ∃ (ho : R.Ordered), OBdd.Reduced ⟨R, ho⟩ := by
--   intro hinv O_root_def
--   have : (loop O.1.heap r O.discover i s).1.Ordered := loop_spec_helper_ordered hinv O_root_def
--   unfold loop
--   split
--   next h =>
--     unfold loop at this
--     split at this
--     next hh =>
--       use this
--       simp only [bind, StateT.bind, get_out, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, get_id]
--       split_ands
--       simp only
--       split
--       next s1 hh =>
--         simp only
--         have : Invariant O (i - 1) s1 := by convert step_spec hinv; rw [hh]
--         sorry
--       sorry
--     sorry
--   next d h => sorry

--   cases h : (i.1 - O.1.heap[r].var.1) with
--   | zero =>
--     unfold loop
--     split

--     simp only [bind, StateT.bind]
--     use sorry
--     sorry
-- --    simp only [get_out, get, getThe, MonadStateOf.get, pure, StateT.pure, bind, StateT.bind, StateT.get]

--   | succ d =>
--     unfold loop
--     split
-- def loop {n m : Nat} (v : Vec (Node n.succ m.succ) m.succ) (r : Fin m.succ) (vlist : Vec (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) (Bdd n.succ m.succ) := do
--   step v vlist i
--   match h : i.1 - v[r].var.1 with
--   | Nat.zero =>
--     let out ← get_out
--     let rid ← get_id (node r)
--     pure {heap := out, root := rid}
--   | Nat.succ j =>
--     loop v r vlist ⟨(j + v[r].var.1), by omega⟩
-- termination_by i.1 - v[r].var.1
-- decreasing_by simp_all

def loop_spec {n m : Nat} {O : OBdd n.succ m.succ} {r} :
    O.1.root = node r →
    let R := (loop O.1.heap r O.discover n initial).1
    ∃ (ho : R.Ordered), OBdd.Reduced ⟨R, ho⟩ ∧ O.evaluate = OBdd.evaluate ⟨R, ho⟩ :=
  loop_spec_helper' (Invariant_of_initial O)

def reduce_spec {n m : Nat} {O : OBdd n.succ m.succ} : ∃ (ho : (reduce O).Ordered), (OBdd.Reduced ⟨reduce O, ho⟩ ∧ O.evaluate = OBdd.evaluate ⟨reduce O, ho⟩) := by
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [reduce]
    simp_rw [O_root_def]
    use Bdd.Ordered_of_terminal' O_root_def
    constructor
    · apply OBdd.reduced_of_terminal
      simp only [OBdd.isTerminal]
      use b
    · rfl
  | node j =>
    simp only [reduce]
    simp_rw [O_root_def]
    simp only [StateT.run]
    exact loop_spec O_root_def

def reduce' {n m : Nat} (O : OBdd n m) : OBdd n m :=
  match n with
  | .zero => O
  | .succ _ =>
    match m with
    | .zero => O
    | .succ _ => ⟨reduce O, reduce_spec.1⟩

lemma reduce'_spec {O : OBdd n m} :
    OBdd.Reduced (reduce' O) ∧ O.evaluate = (reduce' O).evaluate := by
  simp only [reduce']
  split
  next O =>
    constructor
    · apply OBdd.reduced_of_terminal
      rcases O with ⟨⟨heap, root⟩, o⟩
      simp at heap
      cases root with
      | terminal b => use b
      | node j =>
        rcases heap[j] with ⟨⟨_, c⟩ , _, _⟩
        simp_all only [not_lt_zero']
    · rfl
  next n O =>
    split
    next O _ =>
      constructor
      · apply OBdd.reduced_of_terminal
        rcases O with ⟨⟨heap, root⟩, o⟩
        simp only [Nat.succ_eq_add_one, Nat.zero_eq] at heap
        cases root with
        | terminal b => use b
        | node j =>
          absurd j.2
          simp [not_lt_zero']
      · rfl
    next O _ => exact (reduce_spec (O := O)).2

private def reduce'' {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ × Fin m.succ :=
  match O.1.root with
  | terminal _ => ⟨O.1, 0⟩ -- Terminals are already reduced.
  | node r =>
    let ⟨B, S⟩ := (StateT.run (loop O.1.heap r (OBdd.discover O) n) initial)
    ⟨B, S.nid + 1⟩

private def zero_vars_to_bool : Bdd 0 m → Bool := fun B ↦
  match B.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ B.heap[j].var.2)

def oreduce (O : OBdd n m) : Σ k, OBdd n k :=
  match n with
  | .zero => ⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal (zero_vars_to_bool O.1)⟩, Bdd.Ordered_of_terminal⟩⟩
  | .succ _ =>
    match m with
    | .zero => ⟨0, O⟩
    | .succ _ =>
      let ⟨B, k⟩ := reduce'' O
      ⟨k, ⟨Trim.trim B sorry sorry, Trim.trim_ordered sorry⟩⟩

lemma oreduce_reduced {O : OBdd n m} : OBdd.Reduced (oreduce O).2 := sorry

@[simp]
lemma oreduce_evaluate {O : OBdd n m} : (oreduce O).2.evaluate = O.evaluate := sorry

-- lemma populate_queue_spec {n m : Nat} (O : OBdd n.succ m.succ) (i : Fin n.succ) (s : State n.succ m.succ) :
--     (∀ (j : Fin m.succ) (hj : Reachable O.1.heap O.1.root (node j)), i = O.1.heap[j].var → (get_id (node j) s).1 = terminal false) →
--     Invariant O i s →
--     ∀ (j : Fin m.succ) (hj : Reachable O.1.heap O.1.root (node j)), i = O.1.heap[j].var →
--       let ⟨Q, s1⟩ := populate_queue O.1.heap [] O.discover[i] s
--       (∃ rcrd ∈ Q,
--         rcrd.2 = j ∧
--         let l := ({heap := s1.out, root := rcrd.1.1} : Bdd n.succ m.succ)
--         let h := ({heap := s1.out, root := rcrd.1.2} : Bdd n.succ m.succ)
--         -- XXX FIXME
--         (∃ (hl : Bdd.Ordered l) (hh : Bdd.Ordered h),
--         OBdd.evaluate ⟨{heap := O.1.heap, root := node j}, ordered_of_relevant O ⟨node j, hj⟩⟩ =
--         fun I ↦ if I[O.1.heap[j].var] then (OBdd.evaluate ⟨h, hh⟩ I) else  (OBdd.evaluate ⟨l, hl⟩ I))) := by
--   intro hids hinv j hj hi
--   have : j ∈ O.discover[i] := sorry
--   split
--   next Q s1 hdef =>
--     cases h : O.discover[i]
--     case nil => rw [h] at this; contradiction
--     case cons head tail =>
--       rw [h] at this
--       cases this with
--       | head as => sorry
--       | tail b _ => sorry

end Reduce
