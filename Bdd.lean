-- This module serves as the root of the `Bdd` library.
-- Import modules here that should be built as part of the library.
import Bdd.Basic
import Mathlib.Data.Vector.Basic
open Nat
open List renaming Vector → Vec

def Pointer n := Bool ⊕ Fin n

example : Pointer 0 := .inl true

def Node n := Fin n × Pointer n × Pointer n

-- def Proper (v : Vec (Node n) n) := (∀ (i j : Fin n), v[i].2.1 = .inr j ∨ v[i].2.2 = .inr j → v[i].1 < v[j].1)

-- inductive Alright : List (Node n) → Prop where
--   | nil : Alright List.nil
--   | cons_both (v vl vh : Fin n) : v ≤ vl → v ≤ vh → Alright t → Alright (⟨v, .inr vl, .inr vh⟩ :: t)
--   | cons_low  (v vl : Fin n) : v < vl → Alright t → Alright (⟨v, .inr vl, .inl _⟩ :: t)
--   | cons_high (v vh : Fin n) : v < vh → Alright t → Alright (⟨v, .inl _, .inr vh⟩ :: t)
--   | cons_term (v : Fin n) : Alright t → Alright (⟨v, .inl _, .inl _⟩ :: t)

-- def Proper : Vec (Node n) n → Prop := Alright ∘ Vec.toList

-- def RespectsOrder (v : Vec (Node n) n) := (∀ node ∈ v, ∀ j, (node.2.1 = .inr j ∨ node.2.2 = .inr j → node.1 < v[j].1))
instance myVec.Membership : Membership α (Vec α n) := by
  constructor
  exact Membership.mem ∘ Vec.toList

def Node.RespectsOrder (v : Vec (Node n) n) (node : Node n) := ∀ (j : Fin n), (node.2.1 = .inr j ∨ node.2.2 = .inr j → node.1 < v[j].1)
def RespectsOrder (v : Vec (Node n) n) := (∀ node ∈ v, node.RespectsOrder v)

instance Vec.decidableBAll (p : α → Prop) [DecidablePred p] :
    ∀ v : Vec α n, Decidable (∀ x, x ∈ v → p x) := by
  intro v
  exact (List.decidableBAll p v.toList)

-- instance List.decidableBAll' (p : α → Prop) [DecidablePred p] :
--     ∀ l : List α, ∀ h : l.length = n, Decidable (∀ (j : Fin n), p l[j]) := by
--   intro l h
--   induction l generalizing n
--   case nil => apply isTrue; simp at h; subst h; simp
--   case cons head tail ih =>
--     cases n
--     case zero => apply isTrue; simp
--     case succ m =>
--       rename_i dec
--       cases (dec head)
--       case isFalse hh => apply isFalse; simp; use 0; assumption
--       case isTrue  hh =>
--         simp at h
--         cases (ih h)
--         case isFalse hhh =>
--           apply isFalse
--           simp at hhh
--           rcases hhh with ⟨w, hw⟩
--           simp
--           use (w+1)
--           simp
--           assumption
--         case isTrue hhh =>
--           simp_all
--           apply isTrue
--           rintro ⟨j, hj⟩
--           simp
--           cases j
--           case zero => simp_all
--           case succ i => simp_all; simp at hj; apply hhh ⟨i, hj⟩

instance foodec (v : Vec (Node n) n) (node : Node n) (j : Fin n) :
  Decidable (node.2.1 = Sum.inr j ∨ node.2.2 = Sum.inr j → node.1 < v[j].1) :=
  match node with
  | ⟨nv, nl, nh⟩ =>
    match nl with
    | .inl _ =>
      match nh with
      | .inl _ => isTrue (fun contra ↦ match contra with
                            | .inl hh => by contradiction
                            | .inr hh => by contradiction)
      | .inr i => match decEq i j with
        | isFalse h => isTrue (fun contra ↦ match contra with
                                 | .inl hh => by contradiction
                                 | .inr hh => by injection hh; contradiction)
        | isTrue  h =>
          match decLt nv v[j].1 with
          | isFalse hh => isFalse (fun contra ↦ hh (contra (.inr (by simp; congr))))
          | isTrue  hh => isTrue (fun hhh ↦ hh)
    | .inr i => match decEq i j with
      | isFalse h => match nh with
        | .inl _ => isTrue (fun contra ↦ match contra with
                            | .inl hh => (by injection hh; contradiction)
                            | .inr hh => (by simp at hh))
        | .inr k => match decEq k j with
          | isFalse hhh => isTrue (fun contra ↦ match contra with
                                    | .inl hhhh => (by injection hhhh; contradiction)
                                    | .inr hhhh => (by injection hhhh; contradiction))
          | isTrue hhh => match decLt nv v[j].1 with
            | isFalse h5 => isFalse (fun contra ↦ h5 (contra (.inr (by simp; congr))))
            | isTrue h5 => isTrue (fun h6 ↦ (by simp; assumption))
      | isTrue h => match decLt nv v[j].1 with
        | isFalse hh => isFalse (fun contra ↦ hh (contra (.inl (by simp; congr))))
        | isTrue hh => isTrue (fun hhh ↦ hh)

  -- rcases node with ⟨nv, nl, nh⟩
  -- cases nl
  -- case inl =>
  --   cases nh
  --   case inl => simp_all; apply isTrue; simp
  --   case inr i =>
  --     simp_all
  --     cases decEq i j
  --     case isFalse h =>
  --       apply isTrue
  --       intro contra
  --       injection contra
  --       contradiction
  --     case isTrue h =>
  --     cases decLt nv v[j].1
  --     case isFalse hh =>
  --       apply isFalse
  --       intro contra
  --       rw [h] at contra
  --       simp_all
  --     case isTrue hh =>
  --       apply isTrue
  --       intro hhh
  --       assumption
  -- case inr i =>
  --   cases decEq i j
  --   case isFalse h =>
  --     cases nh
  --     case inl => simp_all; apply isTrue; intro contra; injection contra; contradiction
  --     case inr k =>
  --       cases decEq k j
  --       case isFalse hh =>
  --         apply isTrue
  --         intro contra
  --         cases contra <;> rename_i hhh <;> injection hhh <;> contradiction
  --       case isTrue hh =>
  --         cases decLt nv v[j].1
  --         case isFalse hhh =>
  --           apply isFalse
  --           intro contra
  --           apply hhh
  --           apply contra
  --           right
  --           rw [hh]
  --         case isTrue hhh =>
  --           apply isTrue
  --           intro
  --           assumption
  --   case isTrue h =>
  --   rw [h]
  --   simp
  --   exact decLt nv v[j].1

instance Node.RespectsOrder.instDecidable : Decidable (Node.RespectsOrder v node) := by
  apply decidableForallFin

instance RespectsOrder.instDecidable : Decidable (RespectsOrder v) := by
  exact (Vec.decidableBAll (fun node ↦ node.RespectsOrder v) v)

-- instance Alright.instDecidable : Decidable (Alright l) := by
--   induction l
--   case nil => exact isTrue Alright.nil
--   case cons head tail ih =>
--     cases ih
--     case isFalse h =>
--       apply isFalse
--       intro contra
--       cases contra <;> contradiction
--     case isTrue h =>
--       rcases head with ⟨v, pl, ph⟩
--       cases pl
--       case inl =>
--         cases ph
--         case inl =>
--           apply isTrue
--           apply Alright.cons_term
--           assumption
--         case inr w =>
--           cases Fin.decLt v w
--           case isFalse hh =>
--             apply isFalse
--             intro contra
--             cases contra
--             contradiction
--           case isTrue hh =>
--             apply isTrue
--             apply Alright.cons_high <;> assumption
--       case inr w =>
--         cases Fin.decLt v w
--         case isFalse hh =>
--           apply isFalse
--           intro contra
--           cases contra <;> contradiction
--         case isTrue hh =>
--           cases ph
--           case inl =>
--             apply isTrue
--             apply Alright.cons_low <;> assumption
--           case inr u =>
--             cases Fin.decLt v u
--             case isFalse hhh =>
--               apply isFalse
--               intro contra
--               cases contra
--               contradiction
--             case isTrue hhh =>
--               apply isTrue
--               apply Alright.cons_both <;> assumption




-- instance Proper.instDecidable : Decidable (Proper v) := by
--   cases @Alright.instDecidable _ v.toList
--   case isTrue  h => apply isTrue  h
--   case isFalse h => apply isFalse h


def Ws (n : Nat) := { v : Vec (Node n) n // RespectsOrder v }

def OrderedBdd (n : Nat) := Ws n × Pointer n

example : OrderedBdd 4 :=
 ⟨⟨⟨[             ⟨0, .inr 1, .inr 2⟩,
    ⟨1, .inl false, .inr 3⟩, ⟨1, .inr 3, .inl true⟩,
              ⟨2, .inl false, .inl true⟩],
  rfl⟩,
  by decide⟩, .inr 0⟩

def Node.var  : Node n → Fin n     | ⟨v, _, _⟩ => v
def Node.low  : Node n → Pointer n | ⟨_, l, _⟩ => l
def Node.high : Node n → Pointer n | ⟨_, _, h⟩ => h

mutual
inductive Node.Isomorphic {w : Ws n} : Node n → Node n → Prop where
  | mk {nl nr : Node n} :
    nl.var = nr.var → nl.low.Isomorphic nr.low → nl.high.Isomorphic nr.high → nl.Isomorphic nr

inductive Pointer.Isomorphic {w : Ws n} : Pointer n → Pointer n → Prop where
  | eq : Pointer.Isomorphic (.inl b) (.inl b)
  | re : w.1[i].Isomorphic w.1[j] → Pointer.Isomorphic (.inr i) (.inr j)
end

inductive Pointer.Edge {w : Ws n} : Pointer n → Pointer n → Prop where
  | low  : w.1[j].low  = p → Edge (.inr j) p
  | high : w.1[j].high = p → Edge (.inr j) p

def Pointer.Subgraphs {w : Ws n} (p : Pointer n) := {q // Relation.ReflTransGen (@Edge n w) p q}

def Node.isRedundant (node : Node n) : Prop := node.low = node.high

inductive Pointer.isRedundant {w : Ws n} : Pointer n → Prop where
  | red : w.1[j].isRedundant → isRedundant (.inr j)

def Pointer.Reduced {w : Ws n} (p : Pointer n) : Prop :=
  ∀ (q : @Subgraphs n w p), 
    (¬ @isRedundant n w q.1 ∧ ∀ (r : @Subgraphs n w p),
                                @Isomorphic n w q.1 r.1 → q.1 = r.1)


def foo : OrderedBdd 4 :=
 ⟨⟨⟨[             ⟨0, .inr 1, .inr 2⟩,
    ⟨1, .inl false, .inr 3⟩, ⟨1, .inr 3, .inl true⟩,
              ⟨2, .inl false, .inl true⟩],
  rfl⟩,
  by decide⟩, .inr 0⟩

example : @Pointer.Reduced 4 foo.1 foo.2 := by
  simp [Pointer.Reduced, foo, Pointer.isRedundant]
  rintro ⟨q, hq⟩
  induction hq
  case refl => 
    simp_all
    constructor
    case left =>
      intro contra
      cases contra
      case red contra =>
        simp [Pointer.isRedundant, foo] at contra
        cases contra
    case right =>
      rintro ⟨r, h⟩
      sorry
  case tail b c d e f => sorry
-- def Workspace n := ∃ (v : Vector (Node n) n), ((i : Fin n) → (j : Fin n) → v[i].2.1 = .inr j)
-- def NewBdd n := Workspace n × Pointer n

-- def NewBdd.majority : Bdd 3 :=
--   let tieBreaker := bdd 1 0 0 top bot
--   bdd 3 2 2
--    (bdd 2 0 1 top tieBreaker)
--    (bdd 2 1 0 tieBreaker bot)


inductive Bdd : Nat → Type where
  | top : Bdd 0
  | bot : Bdd 0
  | bdd (n : Nat) (hr lr : Fin n) : Bdd hr → Bdd lr → Bdd n

open Bdd

def Bdd.majority : Bdd 3 :=
  let tieBreaker := bdd 1 0 0 top bot
  bdd 3 2 2
   (bdd 2 0 1 top tieBreaker)
   (bdd 2 1 0 tieBreaker bot)

open Nat
open List renaming Vector → Vec

def Bdd.denotation : Bdd n → Vec Bool n → Bool :=
  match n with
  | zero => fun b => match b with
    | top => fun _ => true
    | bot => fun _ => false
  | succ m => fun b => match b with
    | bdd _ hr lr hb lb => fun v => match v with
      | ⟨vl, vh⟩ => match vl with
        | .cons head tail =>
          if head
          then denotation hb ⟨List.drop (m - hr) tail, (by simp at vh; simp; omega)⟩
          else denotation lb ⟨List.drop (m - lr) tail, (by simp at vh; simp; omega)⟩

def Bool.majority : Vec Bool 3 → Bool
  | ⟨[true, true, _], rfl⟩ => true
  | ⟨[true, _, true], rfl⟩ => true
  | ⟨[_, true, true], rfl⟩ => true
  | _ => false

example : Bool.majority = denotation Bdd.majority := by
  funext ⟨[a , b, c], rfl⟩
  cases a <;> cases b <;> cases c <;> simp [Bool.majority, denotation, majority]

inductive Bdd.OccursDirect {m n} : Bdd m → Bdd n → Prop where
  | high : OccursDirect b (bdd n ⟨m, _⟩ _ b _)
  | low  : OccursDirect b (bdd n _ ⟨m, _⟩ _ b)

inductive Bdd.Occurs {m n} : Bdd m → Bdd n → Prop where
  | refl {h : m = n} : Occurs b (h ▸ b)
  | trans (d) : OccursDirect d b → Occurs s d → Occurs s b

def Bdd.SubBdd (m : ℕ) (b : Bdd n) :=
  { s : Bdd m // Occurs s b }

def Bdd.Terminal : Bdd n → Prop
  | _ => n = 0

def Bdd.Foreign (b : Bdd n) (c : Bdd m) : Prop :=
  ∀ k, ∀ (s : Bdd k), (Occurs s b → Occurs s c → Terminal s)

inductive Bdd.Reduced : Bdd n → Prop where
  | topterm : Reduced top
  | botterm : Reduced bot
  | nonterm : Reduced hb → Reduced lb → Foreign hb lb → Reduced (bdd _ _ _ hb lb)

lemma Bdd.top_of_occurs_top : s.Occurs top → s = top := by
intro h
cases s with
| top => simp
| bot => contradiction
| bdd _ _ _ _ _ => contradiction

def Bdd.maxVar : Bdd n → Nat
  | _ => n

theorem Bdd.reduced_of_sup_reduced : Occurs s b → Reduced b → Reduced s := by
  intro o
  induction o with
  | refl => intro h; convert h; simp
  | trans d hd hs ih =>
    intro h
    apply ih
    cases h with
    | topterm => contradiction
    | botterm => contradiction
    | nonterm rhb rlb fhl => cases hd <;> assumption

theorem Bdd.canonicity {n} {b c : Bdd n}: Reduced b → Reduced c → denotation b = denotation c → b = c := by
  intro br cr h
  induction n with
  | zero => cases b with
    | top => cases c with
      | top => rfl
      | bot =>
        simp [denotation] at h;
        have := congrFun h ⟨[], rfl⟩
        contradiction
      | bdd _ hr lr _ _ =>
        cases cr
        cases hr
        cases lr
        contradiction
    | bot => cases c with
      | bot => rfl
      | top =>
        simp [denotation] at h;
        have := congrFun h ⟨[], rfl⟩
        contradiction
      | bdd _ hr lr _ _ =>
        cases cr
        cases hr
        cases lr
        contradiction
    | bdd _ hr lr _ _ =>
      cases hr
      cases lr
      contradiction
  | succ m ih => sorry

theorem Bdd.canonicity' {n} {b c : Bdd n}: Reduced b → Reduced c → denotation b = denotation c → b = c := by
  intro br cr h
  induction n using Nat.strong_induction_on with
  | h m ih =>
    cases b with
    | top => cases c with
      | top => rfl
      | bot =>
        simp [denotation] at h;
        have := congrFun h ⟨[], rfl⟩
        contradiction
      | bdd _ hr lr _ _ =>
        cases cr
        cases hr
        cases lr
        contradiction
    | bot => cases c with
      | bot => rfl
      | top =>
        simp [denotation] at h;
        have := congrFun h ⟨[], rfl⟩
        contradiction
      | bdd _ hr lr _ _ =>
        cases cr
        cases hr
        cases lr
        contradiction
    | bdd _ bhr blr bhb blb =>
      cases m with
      | zero => cases bhr; contradiction
      | succ p =>
        cases c with
        | bdd _ chr clr chb clb =>
          -- this is a good place to work from
          simp_all [denotation]
          constructor
          by_contra! contra
          rw [Fin.ne_iff_vne] at contra
          rw [Nat.ne_iff_lt_or_gt] at contra
          cases contra with
          | inl contra =>
            apply Nat.exists_eq_add_of_lt at contra
            cases contra with
            | intro k hk =>
              simp_all
              have : ∀ (v : Vec Bool p), (bhb.denotation ⟨(List.drop (p - bhr) v.1), (by simp; omega)⟩ = chb.denotation (⟨List.drop (p - (bhr + k + 1)) v.1, (by simp; omega)⟩)) := by sorry
              sorry
          | inr contra => sorry
          sorry
