import Submission.EFL.Comm.GfFactorOfTight
import Submission.EFL.Comm.GfFactorTight
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Zify

namespace Commons.Combinatorics.Factor

/-- **Lovász's `(g,f)`-factor theorem** (the strict case `g < f`).

The general `(g,f)`-case is reduced to the tight `(h,h+1)`-case on the graph `G`
with `f v - g v - 1` pendant vertices added at each vertex `v` (the construction
`gf_factor_of_tight`), and the tight case on that augmented graph is `gf_factor_tight`. -/
theorem lovasz_gf_factor_formula {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)
    (hgf : ∀ v, g v < f v)
    (hf : ∀ v, f v ≤ Nat.card {w : V // G.Adj v w})
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℤ) ≤
        (S.sum (fun s => (f s : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (g t : ℤ)))) :
    ∃ R : G.Subgraph, ∀ v, (g v : ℤ) ≤ (Nat.card {w : V // R.Adj v w} : ℤ) ∧
      (Nat.card {w : V // R.Adj v w} : ℤ) ≤ (f v : ℤ) :=
  GfTight.gf_factor_of_tight_univ V G f g hgf hf
    (fun {W : Type _} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (h : W → ℕ) (hh : ∀ w, h w + 1 ≤ Nat.card {z : W // H.Adj w z})
        (hl : ∀ S T : Finset W, Disjoint S T →
          (((S.product T).filter (fun p => H.Adj p.1 p.2)).card : ℤ)
            ≤ (S.sum (fun s => ((h s : ℤ) + 1)))
              + T.sum (fun t => ((Nat.card {z : W // H.Adj t z} : ℤ) - (h t : ℤ)))) =>
      gf_factor_tight H h hh hl) hlov

end Commons.Combinatorics.Factor


/-!
# Lovász's `(g,f)`-factor theorem

We prove `Commons.Combinatorics.Factor.lovasz_gf_factor_nat`.

The proof strategy is the classical one: the `(g,f)`-factor problem is reduced to the
existence of an exact factor in an auxiliary *hub* graph (Tutte's construction), which in
turn is controlled by Tutte's `f`-factor theorem.

This file currently contains the auxiliary hub-graph construction and the reduction
"factor of the hub graph ⟹ `(g,f)`-subgraph of `G`".
-/

open scoped BigOperators

namespace Commons.Combinatorics.Factor

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices `b_{x,i}` (`i < f x - g x`) that mediate between the hub and `x`. -/
abbrev BInd (f g : V → ℕ) := Σ x : V, Fin (f x - g x)
/-- The hub graph has vertices `V`, the `b`-vertices, and one hub vertex `k`. -/
abbrev HubV (f g : V → ℕ) := V ⊕ (BInd f g ⊕ PUnit)

variable (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)

/-- Adjacency of the hub graph: the graph `G`, the edges `b - x`, and the edges `b - k`. -/
def HubAdj : HubV f g → HubV f g → Prop
  | Sum.inl u, Sum.inl v => G.Adj u v
  | Sum.inl v, Sum.inr (Sum.inl ⟨x, _⟩) => v = x
  | Sum.inr (Sum.inl ⟨x, _⟩), Sum.inl v => v = x
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => True
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => True
  | _, _ => False

lemma HubAdj_symm : Std.Symm (HubAdj G f g) := by
  constructor
  rintro (u | (b | k)) (v | (c | l)) h <;> simp_all [HubAdj] <;> tauto

lemma HubAdj_irrefl : Std.Irrefl (HubAdj G f g) :=
  Std.Irrefl.mk (by
    rintro (u | (b | k)) h
    · exact G.irrefl h
    · simp [HubAdj] at h
    · simp [HubAdj] at h)

/-- The hub graph. -/
def HubG : SimpleGraph (HubV f g) :=
  SimpleGraph.mk (HubAdj G f g) (HubAdj_symm G f g) (HubAdj_irrefl G f g)

/-- Target degree function on the hub graph: `x ↦ f x`, `b`-vertices `↦ 1`, hub `↦ M`. -/
def fHub (M : ℕ) : HubV f g → ℕ
  | Sum.inl v => f v
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => M

/-- The `V`-subgraph extracted from a subgraph of the hub graph. -/
def FOf (F : (HubG G f g).Subgraph) : G.Subgraph where
  verts := Set.univ
  Adj u v := F.Adj (Sum.inl u) (Sum.inl v)
  adj_sub := by intro u v h; exact F.adj_sub h
  edge_vert := by intro _ _ _; exact Set.mem_univ _
  symm := Std.Symm.mk (fun u v h => F.adj_symm h)

/-- The `b`-neighbours of `x` in a hub subgraph. -/
abbrev Bnbrs (F : (HubG G f g).Subgraph) (x : V) : Type _ :=
  {i : Fin (f x - g x) // F.Adj (Sum.inl x) (Sum.inr (Sum.inl (⟨x, i⟩ : BInd f g)))}

lemma card_bnbrs_le (F : (HubG G f g).Subgraph) (x : V) :
    Nat.card (Bnbrs G f g F x) ≤ f x - g x := by
  have h := Nat.card_le_card_of_injective (α := Bnbrs G f g F x) (β := Fin (f x - g x))
    (fun i => i.1) (fun a b hab => Subtype.ext hab)
  simpa using h

lemma adj_hub_inl_inr (x x0 : V) (i : Fin (f x0 - g x0)) :
    (HubG G f g).Adj (Sum.inl x) (Sum.inr (Sum.inl (⟨x0, i⟩ : BInd f g))) ↔ x = x0 :=
  Iff.rfl

lemma adj_hub_inl_unit (x : V) (k : PUnit) :
    (HubG G f g).Adj (Sum.inl x) (Sum.inr (Sum.inr k)) ↔ False := Iff.rfl

lemma card_nbrs_eq (F : (HubG G f g).Subgraph) (x : V) :
    Nat.card {w : HubV f g // F.Adj (Sum.inl x) w} =
      Nat.card {y : V // F.Adj (Sum.inl x) (Sum.inl y)} + Nat.card (Bnbrs G f g F x) := by
  classical
  rw [← Nat.card_sum]
  refine Nat.card_congr ?_
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  · rintro ⟨w, hw⟩
    match w with
    | Sum.inl y => exact Sum.inl ⟨y, hw⟩
    | Sum.inr (Sum.inl b) =>
        obtain ⟨x0, i⟩ := b
        have hbx : x = x0 := (adj_hub_inl_inr G f g x x0 i).mp (F.adj_sub hw)
        subst hbx
        exact Sum.inr ⟨i, hw⟩
    | Sum.inr (Sum.inr k) => exact False.elim ((adj_hub_inl_unit G f g x k).mp (F.adj_sub hw))
  · rintro (⟨y, hy⟩ | ⟨i, hi⟩)
    · exact ⟨Sum.inl y, hy⟩
    · exact ⟨Sum.inr (Sum.inl ⟨x, i⟩), hi⟩
  · rintro ⟨w, hw⟩
    match w with
    | Sum.inl y => rfl
    | Sum.inr (Sum.inl b) =>
        obtain ⟨x0, i⟩ := b
        have hbx : x = x0 := (adj_hub_inl_inr G f g x x0 i).mp (F.adj_sub hw)
        subst hbx
        rfl
    | Sum.inr (Sum.inr k) => exact False.elim ((adj_hub_inl_unit G f g x k).mp (F.adj_sub hw))
  · rintro (⟨y, hy⟩ | ⟨i, hi⟩) <;> rfl

/-- **The reduction.** An exact factor of the hub graph with prescribed degree `M` at the hub
yields a `(g,f)`-subgraph of `G`. -/
lemma fSubgraph_of_factor (M : ℕ) (F : (HubG G f g).Subgraph)
    (hdeg : ∀ w, Nat.card {z : HubV f g // F.Adj w z} = fHub f g M w)
    (hgf : ∀ v, g v < f v) :
    ∃ R : G.Subgraph, ∀ v, (g v : ℤ) ≤ (Nat.card {w : V // R.Adj v w} : ℤ) ∧
      (Nat.card {w : V // R.Adj v w} : ℤ) ≤ (f v : ℤ) := by
  refine ⟨FOf G f g F, fun x => ?_⟩
  have hx : Nat.card {y : V // F.Adj (Sum.inl x) (Sum.inl y)}
      + Nat.card (Bnbrs G f g F x) = f x := by
    have h := hdeg (Sum.inl x)
    rw [card_nbrs_eq G f g F x] at h
    rw [show fHub f g M (Sum.inl x) = f x from rfl] at h
    exact h
  have hb := card_bnbrs_le G f g F x
  have hgy : g x ≤ Nat.card {y : V // F.Adj (Sum.inl x) (Sum.inl y)} := by
    have := hgf x; omega
  have hfy : Nat.card {y : V // F.Adj (Sum.inl x) (Sum.inl y)} ≤ f x := by omega
  have hnn : Nat.card {w : V // (FOf G f g F).Adj x w}
      = Nat.card {y : V // F.Adj (Sum.inl x) (Sum.inl y)} := rfl
  rw [hnn]
  exact ⟨by exact_mod_cast hgy, by exact_mod_cast hfy⟩

/-- **Lovász's `(g,f)`-factor theorem** (Kang–Kelly–Kühn–Methuku–Osthus, Cor. of Thm 6.6). -/
theorem lovasz_gf_factor_nat {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℕ)
    (hgf : ∀ v, g v < f v)
    (hf : ∀ v, f v ≤ Nat.card {w : V // G.Adj v w})
    (hlov : ∀ S T : Finset V, Disjoint S T →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℤ) ≤
        (S.sum (fun s => (f s : ℤ)))
          + T.sum (fun t => ((Nat.card {y : V // G.Adj t y} : ℤ) - (g t : ℤ)))) :
    ∃ R : G.Subgraph, ∀ v, (g v : ℤ) ≤ (Nat.card {w : V // R.Adj v w} : ℤ) ∧
      (Nat.card {w : V // R.Adj v w} : ℤ) ≤ (f v : ℤ) :=
  lovasz_gf_factor_formula G f g hgf hf hlov



end Commons.Combinatorics.Factor
