import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.near_pointwise_bound
import Submission.Work.FTS.EllipticEst.remov.mid_pointwise_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `slice_ang_outer`: the outer (away from `π/2`) half of the angular coercivity

This file proves `Work.FTS.EllipticEst.remov.slice_ang_outer`: on the *outer* angular window
`[0, 3π/8]` — where `tan` and all its derivatives are bounded — the top angular derivative of a
solution of the slice ODE `Lzero1 u = g` is dominated by the right-hand side of the `ℋ^k`
induction step, i.e.

`∫_{[0,3π/8]} (u^{(k+2)})² sin(2θ)^{2k-γ} ≤ C · RHS`,

where `RHS` collects `∫ (g^{(k)})² sin(2θ)^{2k-γ}`, the slots `∫ (u^{(j)})² sin(2θ)^{2j-4-γ}`
for `3 ≤ j ≤ k+1`, and the three low-order terms `∫ (u'')² sin(2θ)^{-η}`, `∫ (u')²`, `∫ (u)²`.

The argument is the *pointwise* route, which is legitimate here precisely because the window
avoids the singular endpoint `θ = π/2`:

* `Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq` rewrites the `k`-fold differentiated ODE
  as `u^{(k+2)} = ∑_{i ≤ k+1} C(k+1,i)(tan)^{(i)} u^{(k+1-i)} - 6u^{(k)} - g^{(k)}`;
* on `(0, π/8)` and on `[π/8, 3π/8]` the finitely many coefficients `(tan)^{(i)}`, `i ≤ k+1`,
  are bounded (`near_pointwise_bound`, `mid_pointwise_bound`), so

  `(u^{(k+2)})² ≤ K · (∑_{m ≤ k+1} (u^{(m)})² + (g^{(k)})²)`;
* multiplying by `sin(2θ)^{2k-γ} ≤ 1` and comparing the exponents
  (`2k - γ ≥ 2m - 4 - γ` for `m ≤ k + 2`, `2k - γ ≥ -η`, `2k - γ ≥ 0`) bounds each slot by one
  of the integrals in `RHS`; this is `slot_le_angPsi` / `sum_mul_le_angPsi`;
* the resulting pointwise domination on `[0, 3π/8]` is integrated against the honest (integrable)
  dominating density `angPsi`, giving the constant `C = K · (k+3)`.

The *singular* endpoint `θ = π/2` is not touched: `[0, 3π/8]` stays a positive distance away
from it, which is exactly why no cancellation/IBP argument is needed here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The dominating density of the right-hand side of `slice_ang_outer`: the `k`-th derivative of
`g`, the `γ`-weighted slots `∂^j u` for `3 ≤ j ≤ k+1`, the `η`-weighted second derivative of `u`,
the first derivative of `u` and `u` itself, each with its prescribed weight. -/
def angPsi (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
    + (∑ j ∈ Finset.Icc 3 (k + 1),
        (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
    + (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))
    + (deriv u θ) ^ 2 + (u θ) ^ 2

/-- Expansion of the integral of a left-associated sum of five integrable functions. -/
private lemma integral_add_assoc5 {s : Set ℝ} (f1 f2 f3 f4 f5 : ℝ → ℝ)
    (h1 : IntegrableOn f1 s) (h2 : IntegrableOn f2 s) (h3 : IntegrableOn f3 s)
    (h4 : IntegrableOn f4 s) (h5 : IntegrableOn f5 s) :
    ∫ x in s, ((((f1 x + f2 x) + f3 x) + f4 x) + f5 x)
      = ((((∫ x in s, f1 x) + (∫ x in s, f2 x)) + (∫ x in s, f3 x)) + (∫ x in s, f4 x))
        + (∫ x in s, f5 x) := by
  have h12 : IntegrableOn (fun x => f1 x + f2 x) s := h1.add h2
  have h123 : IntegrableOn (fun x => (f1 x + f2 x) + f3 x) s := h12.add h3
  have h1234 : IntegrableOn (fun x => ((f1 x + f2 x) + f3 x) + f4 x) s := h123.add h4
  rw [MeasureTheory.integral_add h1234 h5, MeasureTheory.integral_add h123 h4,
    MeasureTheory.integral_add h12 h3, MeasureTheory.integral_add h1 h2]

/-- Comparison of a single derivative slot `(u^{(m)})² sin(2θ)^{2k-γ}` (`m ≤ k+1`) with the
dominating density `angPsi` on `(0, 3π/8)`.

The three cases are `m ≤ 2`, where the factor `sin(2θ)^{2k-γ}` is simply dropped
(`sin(2θ) ≤ 1`) or estimated by `sin(2θ)^{-η}` (using `-η ≤ 2k-γ`), and `m ≥ 3`, where
`sin(2θ)^{2k-γ} = sin(2θ)^{(2m-4-γ) + 2(k+2-m)}` is dominated by the slot of weight
`2m - 4 - γ` (`sin(2θ) ≤ 1`). -/
private lemma slot_le_angPsi {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} (hγ2 : γ ≤ 5 / 4) {u g : ℝ → ℝ}
    {θ : ℝ} (hθ0 : 0 < θ) (hθ3 : θ ≤ 3 * Real.pi / 8) {m : ℕ}
    (hm : m ∈ Finset.range (k + 2)) :
    (iteratedDeriv m u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
      ≤ angPsi k γ u g θ := by
  unfold angPsi
  have hsin0 : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ3, Real.pi_pos])
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsinnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin0
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hmk : m ≤ k + 1 := by have := Finset.mem_range.mp hm; omega
  have hgt_nn : 0 ≤ (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinnn _)
  have hbs_nn : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1),
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinnn _))
  have hdt_nn : 0 ≤ (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinnn _)
  have het_nn : 0 ≤ (deriv u θ) ^ 2 := sq_nonneg _
  have hft_nn : 0 ≤ (u θ) ^ 2 := sq_nonneg _
  rcases lt_or_ge m 3 with hm3 | hm3
  · interval_cases m
    · rw [iteratedDeriv_zero]
      have hσ1 : Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) ≤ 1 :=
        Real.rpow_le_one hsinnn hsin1 (by linarith)
      have key : (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) ≤ (u θ) ^ 2 := by
        nlinarith [hσ1, sq_nonneg (u θ)]
      linarith
    · rw [iteratedDeriv_one]
      have hσ1 : Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) ≤ 1 :=
        Real.rpow_le_one hsinnn hsin1 (by linarith)
      have key : (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          ≤ (deriv u θ) ^ 2 := by
        nlinarith [hσ1, sq_nonneg (deriv u θ)]
      linarith
    · have h2 : iteratedDeriv 2 u θ = deriv (deriv u) θ := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
      rw [h2]
      have hle : Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          ≤ Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by
        refine Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1 ?_
        have := Work.Spaces.eta_pos
        linarith
      have key := mul_le_mul_of_nonneg_left hle (sq_nonneg (deriv (deriv u) θ))
      linarith
  · have hmem : m ∈ Finset.Icc 3 (k + 1) := Finset.mem_Icc.mpr ⟨hm3, hmk⟩
    have hlt : 2 * (m : ℝ) - 4 - γ ≤ 2 * (k : ℝ) - γ := by
      have : (m : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hmk
      linarith
    have hle : Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - 4 - γ) :=
      Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1 hlt
    have key1 := mul_le_mul_of_nonneg_left hle (sq_nonneg (iteratedDeriv m u θ))
    have key2 : (iteratedDeriv m u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - 4 - γ)
        ≤ ∑ j ∈ Finset.Icc 3 (k + 1),
            (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
      Finset.single_le_sum
        (f := fun j => (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
        (fun j _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinnn _)) hmem
    linarith

/-- The dominating density is nonnegative on the whole angular interval `Iθ`. -/
private lemma angPsi_nonneg {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angPsi k γ u g θ := by
  unfold angPsi
  have hsinnn : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
    linarith [hθ.2, Real.pi_pos]
  have h1 : 0 ≤ (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinnn _)
  have h2 : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1),
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinnn _))
  have h3 : 0 ≤ (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinnn _)
  have h4 : 0 ≤ (deriv u θ) ^ 2 := sq_nonneg _
  have h5 : 0 ≤ (u θ) ^ 2 := sq_nonneg _
  linarith

/-- The sum of the first `k+2` derivative slots times `sin(2θ)^{2k-γ}` is dominated by
`(k+2) · angPsi`. -/
private lemma sum_mul_le_angPsi {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} (hγ2 : γ ≤ 5 / 4) {u g : ℝ → ℝ}
    {θ : ℝ} (hθ0 : 0 < θ) (hθ3 : θ ≤ 3 * Real.pi / 8) :
    (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
      ≤ ((k : ℝ) + 2) * angPsi k γ u g θ := by
  rw [Finset.sum_mul]
  calc ∑ m ∈ Finset.range (k + 2),
        (iteratedDeriv m u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
      ≤ ∑ _m ∈ Finset.range (k + 2), angPsi k γ u g θ :=
        Finset.sum_le_sum (fun m hm => slot_le_angPsi hk hγ2 hθ0 hθ3 hm)
    _ = ((k : ℝ) + 2) * angPsi k γ u g θ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num

theorem slice_ang_outer (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Set.Icc 0 (3 * Real.pi / 8), (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨K1, hK1, hnear⟩ := near_pointwise_bound k
  obtain ⟨K2, hK2, hmid⟩ := mid_pointwise_bound k
  refine ⟨max K1 K2 * ((k : ℝ) + 3), ?_, ?_⟩
  · refine mul_pos ?_ ?_
    · exact lt_of_lt_of_le zero_lt_one (le_max_of_le_left hK1)
    · positivity
  · intro γ u g hγ1 hγ2 hu hcont hu0 hupi hg hInt_k2 hInt_gk hInt_high hInt_2 hInt_1 hInt_0
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hKnn : (0 : ℝ) ≤ max K1 K2 :=
      le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_of_le_left hK1))
    have hCnn : (0 : ℝ) ≤ max K1 K2 * ((k : ℝ) + 3) := mul_nonneg hKnn (by positivity)
    have hsub : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ := by
      intro x hx
      exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    -- the pointwise domination on the outer window
    have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) (3 * Real.pi / 8),
        (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          ≤ (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ := by
      intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · -- `θ = 0`: both sides degenerate, the left one to `0`
        have hP0 : 0 ≤ angPsi k γ u g 0 :=
          angPsi_nonneg (θ := 0) ⟨le_refl 0, by linarith [Real.pi_pos]⟩
        rw [← h0, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
        have hz : Real.rpow 0 (2 * (k : ℝ) - γ) = 0 :=
          Real.zero_rpow (by linarith : (2 * (k : ℝ) - γ) ≠ 0)
        rw [hz, mul_zero]
        exact mul_nonneg hCnn hP0
      · have hθ3 : θ ≤ 3 * Real.pi / 8 := hθ.2
        have hsin0 : 0 ≤ Real.sin (2 * θ) := by
          refine Real.sin_nonneg_of_mem_Icc ⟨by linarith, ?_⟩
          linarith [hθ3, Real.pi_pos]
        have hσnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
          Real.rpow_nonneg hsin0 _
        -- the `ℋ^k`-type bound on the top derivative from the differentiated ODE
        have hKb : (iteratedDeriv (k + 2) u θ) ^ 2
            ≤ max K1 K2 * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
                + (iteratedDeriv k g θ) ^ 2) := by
          have hSnn : 0 ≤ (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
              + (iteratedDeriv k g θ) ^ 2 :=
            add_nonneg (Finset.sum_nonneg (fun m _ => sq_nonneg _)) (sq_nonneg _)
          rcases lt_or_ge θ (Real.pi / 8) with hlt | hge
          · exact le_trans (hnear u g hu hg θ ⟨hpos, hlt⟩)
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hSnn)
          · exact le_trans (hmid u g hu hg θ ⟨hge, hθ3⟩)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hSnn)
        have hsum := sum_mul_le_angPsi (u := u) (g := g) hk hγ2 hpos hθ3
        have hgk : (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            ≤ angPsi k γ u g θ := by
          have hrest : 0 ≤ (∑ j ∈ Finset.Icc 3 (k + 1),
                (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
              + (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))
              + (deriv u θ) ^ 2 + (u θ) ^ 2 := by
            have h1 : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1),
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
              Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _))
            have h2 : 0 ≤ (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
              mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _)
            have h3 : 0 ≤ (deriv u θ) ^ 2 := sq_nonneg _
            have h4 : 0 ≤ (u θ) ^ 2 := sq_nonneg _
            linarith
          unfold angPsi
          linarith
        have hinner : ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
              + (iteratedDeriv k g θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            ≤ ((k : ℝ) + 3) * angPsi k γ u g θ := by
          have hsplit : ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
                + (iteratedDeriv k g θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
              = (∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
                + (iteratedDeriv k g θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := by
            ring
          linarith [hsum, hgk, hsplit]
        calc (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            ≤ max K1 K2 * (((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
                + (iteratedDeriv k g θ) ^ 2)
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
              calc _ ≤ (max K1 K2 * ((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
                    + (iteratedDeriv k g θ) ^ 2))
                    * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
                    mul_le_mul_of_nonneg_right hKb hσnn
                _ = max K1 K2 * (((∑ m ∈ Finset.range (k + 2), (iteratedDeriv m u θ) ^ 2)
                    + (iteratedDeriv k g θ) ^ 2)
                    * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
                    ring
          _ ≤ max K1 K2 * (((k : ℝ) + 3) * angPsi k γ u g θ) :=
              mul_le_mul_of_nonneg_left hinner hKnn
          _ = (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ := by ring
    -- integrability of the dominating density, from the hypotheses
    have hBs : MeasureTheory.IntegrableOn (fun θ => ∑ j ∈ Finset.Icc 3 (k + 1),
        (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
        Work.Spaces.Iθ :=
      MeasureTheory.integrable_finsetSum _ (fun j hj => (hInt_high j hj).integrable)
    have hPsint : MeasureTheory.IntegrableOn (angPsi k γ u g) Work.Spaces.Iθ := by
      unfold angPsi
      exact (((hInt_gk.add hBs).add hInt_2).add hInt_1).add hInt_0
    have hRint : MeasureTheory.IntegrableOn
        (fun θ => (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ) Work.Spaces.Iθ :=
      hPsint.const_mul _
    have hRintSub : MeasureTheory.IntegrableOn
        (fun θ => (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ)
        (Set.Icc (0 : ℝ) (3 * Real.pi / 8)) := hRint.mono_set hsub
    have hGint : MeasureTheory.IntegrableOn
        (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (Set.Icc (0 : ℝ) (3 * Real.pi / 8)) := hInt_k2.mono_set hsub
    have hstep1 : (∫ θ in Set.Icc (0 : ℝ) (3 * Real.pi / 8),
          (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∫ θ in Set.Icc (0 : ℝ) (3 * Real.pi / 8),
            (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ :=
      MeasureTheory.setIntegral_mono_on hGint hRintSub measurableSet_Icc hpt
    have hstep2 : (∫ θ in Set.Icc (0 : ℝ) (3 * Real.pi / 8),
          (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ := by
      refine MeasureTheory.setIntegral_mono_set hRint ?_
        (Filter.Eventually.of_forall (fun x hx => hsub hx))
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with x hx
      exact mul_nonneg hCnn (angPsi_nonneg hx)
    have hstep3 : (∫ θ in Work.Spaces.Iθ, (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ)
        = (max K1 K2 * ((k : ℝ) + 3)) * ∫ θ in Work.Spaces.Iθ, angPsi k γ u g θ :=
      MeasureTheory.integral_const_mul _ _
    -- the explicit form of the right-hand side
    have hexp : (∫ θ in Work.Spaces.Iθ, angPsi k γ u g θ)
        = ((((∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))))
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2))
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
      have h5 := integral_add_assoc5
        (fun θ => (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (fun θ => ∑ j ∈ Finset.Icc 3 (k + 1),
          (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
        (fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
        (fun θ => (deriv u θ) ^ 2) (fun θ => (u θ) ^ 2)
        hInt_gk hBs hInt_2 hInt_1 hInt_0
      have hB5 := MeasureTheory.integral_finsetSum (Finset.Icc 3 (k + 1))
        (fun j hj => (hInt_high j hj).integrable)
      rw [hB5] at h5
      exact h5
    calc (∫ θ in Set.Icc (0 : ℝ) (3 * Real.pi / 8),
          (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∫ θ in Set.Icc (0 : ℝ) (3 * Real.pi / 8),
            (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ := hstep1
      _ ≤ ∫ θ in Work.Spaces.Iθ, (max K1 K2 * ((k : ℝ) + 3)) * angPsi k γ u g θ := hstep2
      _ = (max K1 K2 * ((k : ℝ) + 3)) * ∫ θ in Work.Spaces.Iθ, angPsi k γ u g θ := hstep3
      _ = (max K1 K2 * ((k : ℝ) + 3))
            * ((∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by rw [hexp]

end Work.FTS.EllipticEst.remov
