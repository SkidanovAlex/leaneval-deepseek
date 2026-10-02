import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

set_option autoImplicit false
open scoped BigOperators

namespace Commons.Combinatorics.Factor

universe u

namespace GfTight

abbrev Pad {V : Type*} (f g : V → ℕ) : Type _ := Σ v : V, Fin (f v - g v - 1)

def PadAdj {V : Type*} (G : SimpleGraph V) (f g : V → ℕ) : V ⊕ Pad f g → V ⊕ Pad f g → Prop
  | Sum.inl u, Sum.inl v => G.Adj u v
  | Sum.inl v, Sum.inr p => p.1 = v
  | Sum.inr p, Sum.inl v => p.1 = v
  | Sum.inr _, Sum.inr _ => False

instance instDecidableRelPadAdj {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f g : V → ℕ) : DecidableRel (PadAdj G f g) := fun a b => by
  rcases a with u | p <;> rcases b with v | q
  · exact inferInstanceAs (Decidable (G.Adj u v))
  · exact inferInstanceAs (Decidable (q.1 = u))
  · exact inferInstanceAs (Decidable (p.1 = v))
  · exact isFalse (fun h => h)

abbrev edgeFinset {α β : Type*} (R : α → β → Prop) [DecidableRel R]
    (X : Finset α) (Y : Finset β) : Finset (α × β) := (X.product Y).filter (fun q => R q.1 q.2)

lemma PadAdj_symm {V : Type*} (G : SimpleGraph V) (f g : V → ℕ) : Std.Symm (PadAdj G f g) :=
  ⟨by rintro (u | p) (v | q) h
      · exact h.symm
      · exact h
      · exact h
      · exact h.elim⟩

lemma PadAdj_irrefl {V : Type*} (G : SimpleGraph V) (f g : V → ℕ) : Std.Irrefl (PadAdj G f g) :=
  ⟨by rintro (v | p) h
      · exact G.irrefl h
      · exact h⟩

def PadGraph {V : Type*} (G : SimpleGraph V) (f g : V → ℕ) : SimpleGraph (V ⊕ Pad f g) :=
  SimpleGraph.mk (PadAdj G f g) (PadAdj_symm G f g) (PadAdj_irrefl G f g)

instance instDecidableRelPadGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f g : V → ℕ) : DecidableRel (PadGraph G f g).Adj := instDecidableRelPadAdj G f g

def PadH {V : Type*} (f g : V → ℕ) : V ⊕ Pad f g → ℕ
  | Sum.inl v => f v - 1
  | Sum.inr _ => 0

variable {V : Type*} [Fintype V] [DecidableEq V]

def sumNbrSplit {α β : Type*} (Q : α ⊕ β → α ⊕ β → Prop) (a : α) :
    {z : α ⊕ β // Q (Sum.inl a) z} ≃
      {b : α // Q (Sum.inl a) (Sum.inl b)} ⊕ {c : β // Q (Sum.inl a) (Sum.inr c)} where
  toFun z := match z with
    | ⟨Sum.inl b, hz⟩ => Sum.inl ⟨b, hz⟩
    | ⟨Sum.inr c, hz⟩ => Sum.inr ⟨c, hz⟩
  invFun x := match x with
    | Sum.inl b => ⟨Sum.inl b.1, b.2⟩
    | Sum.inr c => ⟨Sum.inr c.1, c.2⟩
  left_inv z := by rcases z with ⟨(b|c), hz⟩ <;> rfl
  right_inv x := by rcases x with b | c <;> rfl

lemma pad_fiber_card (f g : V → ℕ) (v : V) :
    Nat.card {p : Pad f g // p.1 = v} = f v - g v - 1 := by
  rw [Nat.card_congr (Equiv.sigmaSubtype (β := fun v : V => Fin (f v - g v - 1)) v)]
  simp

lemma nbr_card (G : SimpleGraph V) (f g : V → ℕ) (v : V) :
    Nat.card {z : V ⊕ Pad f g // PadAdj G f g (Sum.inl v) z}
      = Nat.card {w : V // G.Adj v w} + (f v - g v - 1) := by
  have h1 : Nat.card {b : V // PadAdj G f g (Sum.inl v) (Sum.inl b)}
      = Nat.card {w : V // G.Adj v w} := rfl
  have h2 : Nat.card {c : Pad f g // PadAdj G f g (Sum.inl v) (Sum.inr c)} = f v - g v - 1 := by
    rw [show Nat.card {c : Pad f g // PadAdj G f g (Sum.inl v) (Sum.inr c)}
          = Nat.card {p : Pad f g // p.1 = v} from rfl, pad_fiber_card]
  rw [Nat.card_congr (sumNbrSplit (PadAdj G f g) v), Nat.card_sum, h1, h2]

def nbrEquivR (G : SimpleGraph V) (f g : V → ℕ) (p : Pad f g) :
    {z : V ⊕ Pad f g // PadAdj G f g (Sum.inr p) z} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨Sum.inl p.1, rfl⟩
  left_inv z := by
    obtain ⟨w, hz⟩ := z
    rcases w with v | q
    · exact Subtype.ext (congrArg Sum.inl (show p.1 = v from hz))
    · exact (show False from hz).elim
  right_inv x := Subsingleton.elim _ _

lemma nbr_card_r (G : SimpleGraph V) (f g : V → ℕ) (p : Pad f g) :
    Nat.card {z : V ⊕ Pad f g // PadAdj G f g (Sum.inr p) z} = 1 := by
  rw [Nat.card_congr (nbrEquivR G f g p)]
  simp

lemma PadH_succ_le_deg (G : SimpleGraph V) (f g : V → ℕ) (hgf : ∀ v, g v < f v)
    (hf : ∀ v, f v ≤ Nat.card {w : V // G.Adj v w}) :
    ∀ w, PadH f g w + 1 ≤ Nat.card {z : V ⊕ Pad f g // PadAdj G f g w z} := by
  intro w
  rcases w with v | p
  · have hfv : 1 ≤ f v := by have := hgf v; omega
    have h1 : PadH f g (Sum.inl v) + 1 = f v := by simp only [PadH]; omega
    rw [h1, nbr_card G f g v]
    have := hf v
    omega
  · have h1 : PadH f g (Sum.inr p) + 1 = 1 := by simp only [PadH]
    rw [h1, nbr_card_r G f g p]

noncomputable def leftPart (f g : V → ℕ) (X : Finset (V ⊕ Pad f g)) : Finset V :=
  X.preimage Sum.inl (fun _ _ _ _ h => Sum.inl.inj h)

noncomputable def rightPart (f g : V → ℕ) (X : Finset (V ⊕ Pad f g)) : Finset (Pad f g) :=
  X.preimage Sum.inr (fun _ _ _ _ h => Sum.inr.inj h)

lemma mem_leftPart (f g : V → ℕ) (X : Finset (V ⊕ Pad f g)) (v : V) :
    v ∈ leftPart f g X ↔ Sum.inl v ∈ X := Finset.mem_preimage

lemma mem_rightPart (f g : V → ℕ) (X : Finset (V ⊕ Pad f g)) (p : Pad f g) :
    p ∈ rightPart f g X ↔ Sum.inr p ∈ X := Finset.mem_preimage

lemma disjSum_decomp (f g : V → ℕ) (X : Finset (V ⊕ Pad f g)) :
    X = (leftPart f g X).disjSum (rightPart f g X) := by
  ext z
  rcases z with v | p
  · rw [Finset.mem_disjSum]
    constructor
    · intro h
      exact Or.inl ⟨v, (mem_leftPart f g X v).mpr h, rfl⟩
    · rintro (⟨a, ha, h⟩ | ⟨b, hb, h⟩)
      · rw [mem_leftPart f g X] at ha
        rwa [Sum.inl.inj h] at ha
      · exact absurd h (by simp)
  · rw [Finset.mem_disjSum]
    constructor
    · intro h
      exact Or.inr ⟨p, (mem_rightPart f g X p).mpr h, rfl⟩
    · rintro (⟨a, ha, h⟩ | ⟨b, hb, h⟩)
      · exact absurd h (by simp)
      · rw [mem_rightPart f g X] at hb
        rwa [Sum.inr.inj h] at hb

lemma filter_disjSum (f g : V → ℕ) (Y : Finset (V ⊕ Pad f g)) (P : V ⊕ Pad f g → Prop)
    [DecidablePred P] :
    Y.filter P
      = ((leftPart f g Y).filter (fun v => P (Sum.inl v))).disjSum
          ((rightPart f g Y).filter (fun p => P (Sum.inr p))) := by
  rw [disjSum_decomp f g Y]
  ext z
  rcases z with v | p <;>
    simp [Finset.mem_disjSum, mem_leftPart, mem_rightPart, Finset.mem_filter]

lemma card_filter_product {α β : Type*} (R : α → β → Prop) [DecidableRel R]
    (X : Finset α) (Y : Finset β) :
    (edgeFinset R X Y).card = ∑ x ∈ X, (Y.filter (R x)).card := by
  rw [Finset.card_filter]
  conv_lhs => rw [show X.product Y = X ×ˢ Y from rfl]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.card_filter]

lemma card_edgeFinset_le {α β : Type*} (R : α → β → Prop) [DecidableRel R]
    (X : Finset α) (Y : Finset β) (h : ∀ b ∈ Y, (X.filter (fun a => R a b)).card ≤ 1) :
    (edgeFinset R X Y).card ≤ Y.card := by
  rw [card_filter_product R X Y, Finset.card_eq_sum_ones]
  calc (∑ a ∈ X, (Y.filter (R a)).card)
      = ∑ a ∈ X, ∑ b ∈ Y, (if R a b then 1 else 0) := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.card_filter]
    _ = ∑ b ∈ Y, ∑ a ∈ X, (if R a b then 1 else 0) := Finset.sum_comm
    _ = ∑ b ∈ Y, (X.filter (fun a => R a b)).card := by
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.card_filter]
    _ ≤ ∑ b ∈ Y, 1 := Finset.sum_le_sum h

lemma sum_disj_split {M : Type*} [AddCommMonoid M] (f g : V → ℕ) (X : Finset (V ⊕ Pad f g))
    (φ : V ⊕ Pad f g → M) :
    X.sum φ = (leftPart f g X).sum (fun v => φ (Sum.inl v))
                + (rightPart f g X).sum (fun p => φ (Sum.inr p)) := by
  conv_lhs => rw [disjSum_decomp f g X]
  rw [Finset.sum_disjSum]

lemma filter_inl_inl (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ) (Yl : Finset V) (v : V) :
    Yl.filter (fun w => PadAdj G f g (Sum.inl v) (Sum.inl w)) = Yl.filter (fun w => G.Adj v w) := by
  apply Finset.ext; intro w; rw [Finset.mem_filter, Finset.mem_filter]; simp only [PadAdj]

lemma filter_inl_inr (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)
    (Yr : Finset (Pad f g)) (v : V) :
    Yr.filter (fun q => PadAdj G f g (Sum.inl v) (Sum.inr q)) = Yr.filter (fun q => q.1 = v) := by
  apply Finset.ext; intro q; rw [Finset.mem_filter, Finset.mem_filter]; simp only [PadAdj]

lemma card_le_split (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ) (X Y : Finset (V ⊕ Pad f g)) :
    (edgeFinset (PadAdj G f g) X Y).card
      ≤ (edgeFinset (fun a b : V => G.Adj a b) (leftPart f g X) (leftPart f g Y)).card
        + (rightPart f g X).card + (rightPart f g Y).card := by
  classical
  have hterm : ∀ v, (Y.filter (fun y => PadAdj G f g (Sum.inl v) y)).card
      = ((leftPart f g Y).filter (fun w => G.Adj v w)).card
        + ((rightPart f g Y).filter (fun q => q.1 = v)).card := by
    intro v
    rw [filter_disjSum f g Y (fun y => PadAdj G f g (Sum.inl v) y), Finset.card_disjSum,
        filter_inl_inl G f g (leftPart f g Y) v, filter_inl_inr G f g (rightPart f g Y) v]
  have hA : (∑ v ∈ leftPart f g X, (Y.filter (fun y => PadAdj G f g (Sum.inl v) y)).card)
      ≤ (edgeFinset (fun a b : V => G.Adj a b) (leftPart f g X) (leftPart f g Y)).card
        + (rightPart f g Y).card := by
    calc (∑ v ∈ leftPart f g X, (Y.filter (fun y => PadAdj G f g (Sum.inl v) y)).card)
        = ∑ v ∈ leftPart f g X, (((leftPart f g Y).filter (fun w => G.Adj v w)).card
            + ((rightPart f g Y).filter (fun q => q.1 = v)).card) :=
          Finset.sum_congr rfl (fun v _ => hterm v)
      _ = (∑ v ∈ leftPart f g X, ((leftPart f g Y).filter (fun w => G.Adj v w)).card)
            + ∑ v ∈ leftPart f g X, ((rightPart f g Y).filter (fun q => q.1 = v)).card :=
          Finset.sum_add_distrib
      _ ≤ (edgeFinset (fun a b : V => G.Adj a b) (leftPart f g X) (leftPart f g Y)).card
            + (rightPart f g Y).card := by
          apply add_le_add
          · rw [card_filter_product (fun a b : V => G.Adj a b) (leftPart f g X) (leftPart f g Y)]
          · rw [show (∑ v ∈ leftPart f g X, ((rightPart f g Y).filter (fun q => q.1 = v)).card)
                = (edgeFinset (fun v (q : Pad f g) => q.1 = v) (leftPart f g X)
                    (rightPart f g Y)).card
              from (card_filter_product (fun v (q : Pad f g) => q.1 = v) (leftPart f g X)
                    (rightPart f g Y)).symm]
            apply card_edgeFinset_le
            intro b _
            have hsub : (leftPart f g X).filter (fun a => b.1 = a) ⊆ ({b.1} : Finset V) := by
              intro a ha
              rw [Finset.mem_singleton]
              exact (Finset.mem_filter.mp ha).2.symm
            calc ((leftPart f g X).filter (fun a => b.1 = a)).card ≤ ({b.1} : Finset V).card :=
                  Finset.card_le_card hsub
              _ = 1 := Finset.card_singleton _
  have hB : (∑ p ∈ rightPart f g X, (Y.filter (fun y => PadAdj G f g (Sum.inr p) y)).card)
      ≤ (rightPart f g X).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro p _
    have hsub : Y.filter (fun y => PadAdj G f g (Sum.inr p) y)
        ⊆ ({Sum.inl p.1} : Finset (V ⊕ Pad f g)) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      obtain ⟨hyY, hadj⟩ := hy
      rcases y with v | q
      · rw [Finset.mem_singleton]
        exact congrArg Sum.inl (show v = p.1 from (show p.1 = v from hadj).symm)
      · exact (show False from hadj).elim
    calc (Y.filter (fun y => PadAdj G f g (Sum.inr p) y)).card
        ≤ ({Sum.inl p.1} : Finset (V ⊕ Pad f g)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  calc (edgeFinset (PadAdj G f g) X Y).card
      = (∑ v ∈ leftPart f g X, (Y.filter (fun y => PadAdj G f g (Sum.inl v) y)).card)
          + ∑ p ∈ rightPart f g X, (Y.filter (fun y => PadAdj G f g (Sum.inr p) y)).card := by
        rw [card_filter_product (PadAdj G f g) X Y]
        conv_lhs => rw [sum_disj_split f g X]
    _ ≤ ((edgeFinset (fun a b : V => G.Adj a b) (leftPart f g X) (leftPart f g Y)).card
            + (rightPart f g Y).card) + (rightPart f g X).card := add_le_add hA hB
    _ = (edgeFinset (fun a b : V => G.Adj a b) (leftPart f g X) (leftPart f g Y)).card
          + (rightPart f g X).card + (rightPart f g Y).card := by ring

lemma sum_phi_eq (G : SimpleGraph V) (f g : V → ℕ) (hgf : ∀ v, g v < f v)
    (X : Finset (V ⊕ Pad f g)) :
    X.sum (fun s => ((PadH f g s : ℤ) + 1))
      = (leftPart f g X).sum (fun v => (f v : ℤ)) + ((rightPart f g X).card : ℤ) := by
  rw [sum_disj_split f g X (fun s => ((PadH f g s : ℤ) + 1))]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    simp only [PadH]
    have := hgf v
    omega
  · rw [Finset.card_eq_sum_ones]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    simp only [PadH]
    norm_num

lemma sum_psi_eq (G : SimpleGraph V) (f g : V → ℕ) (hgf : ∀ v, g v < f v)
    (X : Finset (V ⊕ Pad f g)) :
    X.sum (fun s => ((Nat.card {z : V ⊕ Pad f g // PadAdj G f g s z} : ℤ) - (PadH f g s : ℤ)))
      = (leftPart f g X).sum (fun v => ((Nat.card {w : V // G.Adj v w} : ℤ) - (g v : ℤ)))
        + ((rightPart f g X).card : ℤ) := by
  rw [sum_disj_split f g X (fun s => ((Nat.card {z : V ⊕ Pad f g // PadAdj G f g s z} : ℤ)
        - (PadH f g s : ℤ)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    rw [nbr_card G f g v]
    simp only [PadH]
    have := hgf v
    omega
  · rw [Finset.card_eq_sum_ones]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    rw [nbr_card_r G f g p]
    simp only [PadH]
    norm_num

theorem hall_cond (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ) (hgf : ∀ v, g v < f v)
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (edgeFinset (fun a b : V => G.Adj a b) S T).card
        ≤ (S.sum (fun s => (f s : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (g t : ℤ)))) :
    ∀ X Y : Finset (V ⊕ Pad f g), Disjoint X Y →
      ((edgeFinset (PadAdj G f g) X Y).card : ℤ)
        ≤ (X.sum (fun s => ((PadH f g s : ℤ) + 1)))
          + Y.sum (fun t => ((Nat.card {z : V ⊕ Pad f g // PadAdj G f g t z} : ℤ)
              - (PadH f g t : ℤ))) := by
  intro X Y hXY
  classical
  have hXYl : Disjoint (leftPart f g X) (leftPart f g Y) := by
    rw [Finset.disjoint_left] at hXY ⊢
    intro v hv hvY
    exact hXY ((mem_leftPart f g X v).mp hv) ((mem_leftPart f g Y v).mp hvY)
  have hstep := card_le_split G f g X Y
  have hlov' := hlov (leftPart f g X) (leftPart f g Y) hXYl
  rw [sum_phi_eq G f g hgf X, sum_psi_eq G f g hgf Y]
  have hstep' : ((edgeFinset (PadAdj G f g) X Y).card : ℤ)
      ≤ ((edgeFinset (fun a b : V => G.Adj a b) (leftPart f g X) (leftPart f g Y)).card : ℤ)
        + ((rightPart f g X).card : ℤ) + ((rightPart f g Y).card : ℤ) := by
    exact_mod_cast hstep
  linarith [hstep', hlov']

theorem gf_factor_of_tight_univ (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)
    (hgf : ∀ v, g v < f v)
    (hf : ∀ v, f v ≤ Nat.card {w : V // G.Adj v w})
    (hT : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (h : W → ℕ),
      (∀ w, h w + 1 ≤ Nat.card {z : W // H.Adj w z}) →
      (∀ S T : Finset W, Disjoint S T →
        (((S.product T).filter (fun p => H.Adj p.1 p.2)).card : ℤ)
          ≤ (S.sum (fun s => ((h s : ℤ) + 1)))
            + T.sum (fun t => ((Nat.card {z : W // H.Adj t z} : ℤ) - (h t : ℤ)))) →
      ∃ R : H.Subgraph, ∀ w, (h w : ℤ) ≤ (Nat.card {z : W // R.Adj w z} : ℤ) ∧
        (Nat.card {z : W // R.Adj w z} : ℤ) ≤ (h w : ℤ) + 1)
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℤ) ≤
        (S.sum (fun s => (f s : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (g t : ℤ)))) :
    ∃ R : G.Subgraph, ∀ v, (g v : ℤ) ≤ (Nat.card {w : V // R.Adj v w} : ℤ) ∧
      (Nat.card {w : V // R.Adj v w} : ℤ) ≤ (f v : ℤ) := by
  classical
  obtain ⟨R, hR⟩ := hT (W := V ⊕ Pad f g) (H := PadGraph G f g) (h := PadH f g)
      (PadH_succ_le_deg G f g hgf hf)
      (hall_cond G f g hgf hlov)
  refine ⟨⟨Set.univ, (fun u w => R.Adj (Sum.inl u) (Sum.inl w)), ?_, ?_, ?_⟩, fun v => ?_⟩
  · intro u w h; exact R.adj_sub h
  · intro u w _; exact Set.mem_univ u
  · exact ⟨fun u w h => h.symm⟩
  · show (g v : ℤ) ≤ (Nat.card {w : V // R.Adj (Sum.inl v) (Sum.inl w)} : ℤ) ∧
      (Nat.card {w : V // R.Adj (Sum.inl v) (Sum.inl w)} : ℤ) ≤ (f v : ℤ)
    have hR1 := (hR (Sum.inl v)).1
    have hR2 := (hR (Sum.inl v)).2
    simp only [PadH] at hR1 hR2
    have hsplit : Nat.card {z : V ⊕ Pad f g // R.Adj (Sum.inl v) z}
        = Nat.card {w : V // R.Adj (Sum.inl v) (Sum.inl w)}
          + Nat.card {p : Pad f g // R.Adj (Sum.inl v) (Sum.inr p)} :=
      (Nat.card_congr (sumNbrSplit (fun a b => R.Adj a b) v)).trans Nat.card_sum
    have hk : Nat.card {p : Pad f g // R.Adj (Sum.inl v) (Sum.inr p)} ≤ f v - g v - 1 := by
      have hinj : Nat.card {p : Pad f g // R.Adj (Sum.inl v) (Sum.inr p)}
          ≤ Nat.card {p : Pad f g // p.1 = v} :=
        Nat.card_le_card_of_injective (fun p => ⟨p.1, (show p.1.1 = v from R.adj_sub p.2)⟩)
          (fun a b h => Subtype.ext (Subtype.mk.inj h))
      rwa [pad_fiber_card f g v] at hinj
    have hgf' : g v + 1 ≤ f v := by have := hgf v; omega
    have hfv : 1 ≤ f v := by omega
    have hD : (Nat.card {w : V // R.Adj (Sum.inl v) (Sum.inl w)} : ℤ)
        = (Nat.card {z : V ⊕ Pad f g // R.Adj (Sum.inl v) z} : ℤ)
          - (Nat.card {p : Pad f g // R.Adj (Sum.inl v) (Sum.inr p)} : ℤ) := by
      rw [hsplit]; push_cast; ring
    constructor <;> omega

end GfTight

namespace GfTight

/-- The graph obtained by transporting `G` along an equivalence. -/
def transGraph {V V' : Type*} (e : V ≃ V') (G : SimpleGraph V) : SimpleGraph V' :=
  SimpleGraph.mk (fun a b => G.Adj (e.symm a) (e.symm b))
    ⟨fun _ _ h => h.symm⟩ ⟨fun _ h => G.irrefl h⟩

@[simp] lemma transGraph_adj {V V' : Type*} (e : V ≃ V') (G : SimpleGraph V) (a b : V') :
    (transGraph e G).Adj a b = G.Adj (e.symm a) (e.symm b) := rfl

instance instDecidableRelTransGraph {V V' : Type*} (e : V ≃ V') (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel (transGraph e G).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj (e.symm a) (e.symm b)))

lemma nbr_card_transport {V V' : Type*} (e : V ≃ V') (G : SimpleGraph V) (x : V') :
    Nat.card {a : V' // (transGraph e G).Adj x a} = Nat.card {b : V // G.Adj (e.symm x) b} :=
  Nat.card_congr (Equiv.subtypeEquiv e.symm (fun _ => Iff.rfl))

lemma edges_transport {V V' : Type*} (e : V ≃ V') (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V') :
    (edgeFinset (transGraph e G).Adj S T).card
      = (edgeFinset G.Adj (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding)).card := by
  rw [card_filter_product (transGraph e G).Adj S T,
      card_filter_product G.Adj (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding)]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  rw [show (Finset.filter (G.Adj (e.symm.toEmbedding a)) (Finset.map e.symm.toEmbedding T))
        = (T.filter (fun b => G.Adj (e.symm.toEmbedding a) (e.symm.toEmbedding b))).map e.symm.toEmbedding
      from Finset.filter_map (s := T) (p := G.Adj (e.symm.toEmbedding a)), Finset.card_map]
  apply congrArg Finset.card
  apply Finset.ext
  intro b
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [transGraph_adj, Equiv.toEmbedding_apply]

lemma hlov_transport {V V' : Type*} [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V']
    (e : V ≃ V') (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (edgeFinset G.Adj S T).card
        ≤ (S.sum (fun s => (f s : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (g t : ℤ)))) :
    ∀ S T : Finset V', Disjoint S T →
      (edgeFinset (transGraph e G).Adj S T).card
        ≤ (S.sum (fun s => (f (e.symm s) : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V' // (transGraph e G).Adj t y} : ℤ)
              - (g (e.symm t) : ℤ))) := by
  intro S T hST
  have hdisj : Disjoint (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding) := by
    rw [Finset.disjoint_left] at hST ⊢
    intro a ha haT
    rw [Finset.mem_map] at ha haT
    obtain ⟨a1, ha1, rfl⟩ := ha
    obtain ⟨a2, ha2, h2⟩ := haT
    have key : a1 = a2 := e.symm.injective h2.symm
    exact hST ha1 (key ▸ ha2)
  have h := hlov (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding) hdisj
  rw [edges_transport e G S T]
  have h1 : S.sum (fun s => (f (e.symm s) : ℤ))
      = (S.map e.symm.toEmbedding).sum (fun s => (f s : ℤ)) :=
    (Finset.sum_map S e.symm.toEmbedding (fun s => (f s : ℤ))).symm
  have h2 : T.sum (fun t => ((Nat.card {y : V' // (transGraph e G).Adj t y} : ℤ)
        - (g (e.symm t) : ℤ)))
      = (T.map e.symm.toEmbedding).sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ)
          - (g t : ℤ))) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro t _
    rw [nbr_card_transport e G t]
    simp only [Equiv.toEmbedding_apply]
  rw [h1, h2]
  exact h

lemma subgraph_transport {V V' : Type*} [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V']
    (e : V ≃ V') (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)
    (hR : ∃ R : (transGraph e G).Subgraph, ∀ a,
      (g (e.symm a) : ℤ) ≤ (Nat.card {w : V' // R.Adj a w} : ℤ) ∧
        (Nat.card {w : V' // R.Adj a w} : ℤ) ≤ (f (e.symm a) : ℤ)) :
    ∃ R : G.Subgraph, ∀ v, (g v : ℤ) ≤ (Nat.card {w : V // R.Adj v w} : ℤ) ∧
      (Nat.card {w : V // R.Adj v w} : ℤ) ≤ (f v : ℤ) := by
  obtain ⟨R', hR'⟩ := hR
  refine ⟨⟨Set.univ, (fun u v => R'.Adj (e u) (e v)), ?_, ?_, ?_⟩, fun v => ?_⟩
  · intro u v h; simpa using R'.adj_sub h
  · intro u v _; exact Set.mem_univ u
  · exact ⟨fun u v h => h.symm⟩
  · have hcard : Nat.card {w : V // R'.Adj (e v) (e w)} = Nat.card {w : V' // R'.Adj (e v) w} :=
      Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
    rw [hcard]
    simpa using hR' (e v)

end GfTight

open GfTight

theorem gf_factor_of_tight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)
    (hgf : ∀ v, g v < f v)
    (hf : ∀ v, f v ≤ Nat.card {w : V // G.Adj v w})
    (hT : ∀ {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (h : W → ℕ),
      (∀ w, h w + 1 ≤ Nat.card {z : W // H.Adj w z}) →
      (∀ S T : Finset W, Disjoint S T →
        (((S.product T).filter (fun p => H.Adj p.1 p.2)).card : ℤ)
          ≤ (S.sum (fun s => ((h s : ℤ) + 1)))
            + T.sum (fun t => ((Nat.card {z : W // H.Adj t z} : ℤ) - (h t : ℤ)))) →
      ∃ R : H.Subgraph, ∀ w, (h w : ℤ) ≤ (Nat.card {z : W // R.Adj w z} : ℤ) ∧
        (Nat.card {z : W // R.Adj w z} : ℤ) ≤ (h w : ℤ) + 1)
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℤ) ≤
        (S.sum (fun s => (f s : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (g t : ℤ)))) :
    ∃ R : G.Subgraph, ∀ v, (g v : ℤ) ≤ (Nat.card {w : V // R.Adj v w} : ℤ) ∧
      (Nat.card {w : V // R.Adj v w} : ℤ) ≤ (f v : ℤ) := by
  classical
  let V' := ULift (Fin (Fintype.card V))
  let e : V ≃ V' := (Fintype.equivFin V).trans Equiv.ulift.symm
  haveI : Fintype V' := inferInstance
  haveI : DecidableEq V' := inferInstance
  have hgf' : ∀ a, g (e.symm a) < f (e.symm a) := fun a => hgf (e.symm a)
  have hf' : ∀ a, f (e.symm a) ≤ Nat.card {w : V' // (transGraph e G).Adj a w} := by
    intro a
    rw [nbr_card_transport e G a]
    exact hf (e.symm a)
  have hlov' := hlov_transport e G f g hlov
  exact subgraph_transport e G f g
    (gf_factor_of_tight_univ V' (transGraph e G) (fun a => f (e.symm a)) (fun a => g (e.symm a))
      hgf' hf' hT hlov')

end Commons.Combinatorics.Factor
