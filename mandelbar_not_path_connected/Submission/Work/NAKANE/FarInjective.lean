/-
# `Φ` is injective near infinity

This file proves that the parameter Böttcher map `Φ` is injective on an outer annulus
`{R ≤ ‖c‖}`, assuming the Lipschitz estimate for the diagonal Böttcher series

`‖bottcherSeries x x - bottcherSeries y y‖ ≤ C ‖x - y‖ / ‖x‖²`  (`‖y - x‖ ≤ ‖x‖/2`, `r ≤ ‖x‖`)

of `Work.NAKANE.FarInj.exists_diagonal_lipschitz`.  This is the "one sheet at infinity" input of
`Work.NAKANE.InjOfFar.injOn_of_localHomeo_of_farInj`, which turns it into full injectivity of `Φ`
on the exterior of the mandelbar and hence (with (R1)) into Nakane's homeomorphism theorem.

The mechanism is elementary.  For `‖z‖ > 8` one has `Φ z = z * exp (S z)` with `S z = S(z,z)`
(`Work.NAKANE.varphiCrit_self_eq_bottcher_self`), with `‖S z‖ ≤ 4/‖z‖`
(`Work.Bottcher.Critical.norm_bottcherSeries_self_le`), so `‖Φ z - z‖ ≤ 8`.  Writing
`z₁(e^{S₁} - 1) - z₂(e^{S₂} - 1) = (z₁ - z₂)(e^{S₁} - 1) + z₂ (e^{S₁} - e^{S₂})`:

* if `4‖z₁‖ < ‖z₂‖`, the crude bound `‖Φ z - z‖ ≤ 8` gives
  `‖…‖ ≤ 16 ≤ ‖z₁ - z₂‖/2` for large `‖z₁‖`;
* if `‖z₂‖ ≤ 4‖z₁‖` and `‖z₁ - z₂‖ > ‖z₁‖/2`, the same crude bound applies;
* if `‖z₂‖ ≤ 4‖z₁‖` and `‖z₁ - z₂‖ ≤ ‖z₁‖/2`, the Lipschitz estimate gives
  `‖z₂ (e^{S₁} - e^{S₂})‖ ≤ ‖z₂‖ e^{1/2} · 2 C ‖z₁ - z₂‖ / ‖z₁‖² ≤ ‖z₁ - z₂‖/4` and
  `‖(z₁ - z₂)(e^{S₁} - 1)‖ ≤ ‖z₁ - z₂‖ · 2 · 4/‖z₁‖ ≤ ‖z₁ - z₂‖/4`.

Hence `Φ - id` is `(1/2)`-Lipschitz on `{R ≤ ‖c‖}`, and
`Work.MRMT.Found.injOn_of_lipschitz_away` yields the injectivity.
-/
import Submission.Work.NAKANE.PotentialTop
import Submission.Work.NAKANE.Asymptotic
import Submission.Work.Bottcher.Critical.Phi_isBigO_atTop
import Submission.Work.MRMT.Found.exists_homeomorph_of_localInj_proper

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The Böttcher series along the diagonal, as a function of the parameter. -/
private noncomputable def dS (z : ℂ) : ℂ := Work.Bottcher.bottcherSeries z z

private theorem dS_apply (z : ℂ) : dS z = Work.Bottcher.bottcherSeries z z := rfl

/-- The coarse diagonal bound for the Böttcher series. -/
private theorem norm_dS_le {z : ℂ} (hz : 8 ≤ ‖z‖) : ‖dS z‖ ≤ 4 / ‖z‖ := by
  have h1 := Work.Bottcher.Critical.norm_bottcherSeries_self_le z (by linarith)
  rw [dS_apply]
  have hpos : (0 : ℝ) < ‖z‖ := by linarith
  have h2 : 1 / ‖z‖ ^ 2 ≤ 1 / ‖z‖ := by
    refine one_div_le_one_div_of_le hpos ?_
    nlinarith
  have h3 : 1 / ‖z‖ ^ 3 ≤ 1 / ‖z‖ := by
    refine one_div_le_one_div_of_le hpos ?_
    nlinarith
  have h4 : (2 : ℝ) / ‖z‖ + 1 / ‖z‖ + 1 / ‖z‖ = 4 / ‖z‖ := by ring_nf
  linarith

/-- `Φ` on the diagonal is the parameter times the exponential of its Böttcher series. -/
private theorem Phi_eq_mul_exp_dS {z : ℂ} (hz : 8 < ‖z‖) :
    Work.ParamRays.Phi z = z * Complex.exp (dS z) := by
  have hzMb : z ∉ Mb := fun h => by
    have h1 := norm_le_two_of_mem_Mb h
    linarith
  rw [Phi_eq_varphiCrit hzMb, varphiCrit_self_eq_bottcher_self hz, Work.Bottcher.bottcher,
    dS_apply]

/-- The crude bound `‖Φ z - z‖ ≤ 8` far out. -/
private theorem norm_Phi_sub_le {z : ℂ} (hz : 8 < ‖z‖) :
    ‖Work.ParamRays.Phi z - z‖ ≤ 8 := by
  rw [Phi_eq_mul_exp_dS hz]
  have hS := norm_dS_le (le_of_lt hz)
  have hS1 : ‖dS z‖ ≤ 1 := by
    have hzpos : (0 : ℝ) < ‖z‖ := by linarith
    have h : 4 / ‖z‖ ≤ 1 := by
      rw [div_le_iff₀ hzpos]
      linarith
    linarith
  have h1 : z * Complex.exp (dS z) - z = z * (Complex.exp (dS z) - 1) := by ring
  rw [h1, norm_mul]
  have h2 : ‖Complex.exp (dS z) - 1‖ ≤ 2 * ‖dS z‖ := Complex.norm_exp_sub_one_le (by linarith)
  have h3 : ‖z‖ * (2 * ‖dS z‖) ≤ ‖z‖ * (2 * (4 / ‖z‖)) := by
    have := norm_nonneg z
    nlinarith
  have h4 : ‖z‖ * (2 * (4 / ‖z‖)) = 8 := by
    have hz0 : (‖z‖ : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  calc ‖z‖ * ‖Complex.exp (dS z) - 1‖ ≤ ‖z‖ * (2 * ‖dS z‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg z)
    _ ≤ ‖z‖ * (2 * (4 / ‖z‖)) := h3
    _ = 8 := h4

/-- The exponential of a small complex number is at most `2` in modulus. -/
private theorem norm_exp_le_two {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖Complex.exp w‖ ≤ 2 := by
  rw [Complex.norm_exp]
  have h1 : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have h2 : Real.exp w.re ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h4 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    have h5 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ), sq_nonneg (Real.exp (1 / 2 : ℝ) - 2)]
  linarith

/-- **`Φ - id` is `(1/2)`-Lipschitz on an outer annulus**, given the diagonal Lipschitz estimate
for the Böttcher series. -/
theorem exists_lipschitz_sub_id {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    (hlip : ∀ x y : ℂ, r ≤ ‖x‖ → ‖y - x‖ ≤ ‖x‖ / 2 →
      ‖Work.Bottcher.bottcherSeries x x - Work.Bottcher.bottcherSeries y y‖
        ≤ C * ‖x - y‖ / ‖x‖ ^ 2) :
    ∃ R : ℝ, ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖(Work.ParamRays.Phi z₁ - z₁) - (Work.ParamRays.Phi z₂ - z₂)‖ ≤ (1 / 2) * ‖z₁ - z₂‖ := by
  refine ⟨max r (max (64 * C + 64) 1024), fun z₁ z₂ h₁ h₂ => ?_⟩
  have hz1r : r ≤ ‖z₁‖ := le_trans (le_max_left _ _) h₁
  have hz2r : r ≤ ‖z₂‖ := le_trans (le_max_left _ _) h₂
  have hz1big : 64 * C + 64 ≤ ‖z₁‖ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h₁
  have hz2big : 64 * C + 64 ≤ ‖z₂‖ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h₂
  have hz1_1024 : 1024 ≤ ‖z₁‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h₁
  have hz2_1024 : 1024 ≤ ‖z₂‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h₂
  have hz1pos : (0 : ℝ) < ‖z₁‖ := by linarith
  have hz1_8 : 8 ≤ ‖z₁‖ := by linarith
  have hz1_8' : 8 < ‖z₁‖ := by linarith
  have hz2_8' : 8 < ‖z₂‖ := by linarith
  have hz2_8 : 8 ≤ ‖z₂‖ := by linarith
  have hS1 := norm_dS_le hz1_8
  have hS2 := norm_dS_le hz2_8
  have hS1_half : ‖dS z₁‖ ≤ 1 / 2 := by
    have h : 4 / ‖z₁‖ ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ hz1pos]
      linarith
    linarith
  have hS2_half : ‖dS z₂‖ ≤ 1 / 2 := by
    have h : 4 / ‖z₂‖ ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖z₂‖)]
      linarith
    linarith
  have hexp2 : ‖Complex.exp (dS z₂)‖ ≤ 2 := norm_exp_le_two hS2_half
  have hA1 := norm_Phi_sub_le hz1_8'
  have hA2 := norm_Phi_sub_le hz2_8'
  have hdecomp : (Work.ParamRays.Phi z₁ - z₁) - (Work.ParamRays.Phi z₂ - z₂)
      = (z₁ - z₂) * (Complex.exp (dS z₁) - 1)
        + z₂ * (Complex.exp (dS z₁) - Complex.exp (dS z₂)) := by
    rw [Phi_eq_mul_exp_dS hz1_8', Phi_eq_mul_exp_dS hz2_8']
    ring
  have hcrude : ‖(Work.ParamRays.Phi z₁ - z₁) - (Work.ParamRays.Phi z₂ - z₂)‖ ≤ 16 := by
    calc ‖(Work.ParamRays.Phi z₁ - z₁) - (Work.ParamRays.Phi z₂ - z₂)‖
        ≤ ‖Work.ParamRays.Phi z₁ - z₁‖ + ‖Work.ParamRays.Phi z₂ - z₂‖ := norm_sub_le _ _
      _ ≤ 8 + 8 := add_le_add hA1 hA2
      _ = 16 := by norm_num
  by_cases hbig : 4 * ‖z₁‖ < ‖z₂‖
  · -- the norms are very different: crude bounds suffice
    have hsep : 16 ≤ (1 / 2) * ‖z₁ - z₂‖ := by
      have h1 : ‖z₂‖ ≤ ‖z₁‖ + ‖z₁ - z₂‖ := by
        have h2 := norm_add_le (z₂ - z₁) z₁
        rw [show z₂ - z₁ + z₁ = z₂ by ring, norm_sub_rev z₂ z₁] at h2
        linarith
      linarith
    linarith
  · rw [not_lt] at hbig
    by_cases hsep : ‖z₂ - z₁‖ ≤ ‖z₁‖ / 2
    · -- the Lipschitz regime
      rw [hdecomp]
      have hlip12 := hlip z₁ z₂ hz1r hsep
      rw [← dS_apply, ← dS_apply] at hlip12
      have hLip1 : ‖dS z₁ - dS z₂‖ ≤ 1 := by
        have h2 : C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2 ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have h3 : ‖z₁ - z₂‖ ≤ ‖z₁‖ / 2 := by rwa [norm_sub_rev] at hsep
          nlinarith [norm_nonneg (z₁ - z₂), hz1big, hC.le, hz1pos]
        linarith
      refine le_trans (norm_add_le _ _) ?_
      have ht1 : ‖(z₁ - z₂) * (Complex.exp (dS z₁) - 1)‖ ≤ ‖z₁ - z₂‖ / 4 := by
        rw [norm_mul]
        have h2 : ‖Complex.exp (dS z₁) - 1‖ ≤ 2 * ‖dS z₁‖ :=
          Complex.norm_exp_sub_one_le (by linarith)
        have h3 : 2 * (4 / ‖z₁‖) ≤ (1 : ℝ) / 4 := by
          have h4 : (4 : ℝ) / ‖z₁‖ ≤ 1 / 8 := by
            rw [div_le_iff₀ hz1pos]
            linarith
          linarith
        have h4 : 2 * ‖dS z₁‖ ≤ (1 : ℝ) / 4 := by linarith
        calc ‖z₁ - z₂‖ * ‖Complex.exp (dS z₁) - 1‖
            ≤ ‖z₁ - z₂‖ * (2 * ‖dS z₁‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ ≤ ‖z₁ - z₂‖ * (1 / 4) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
          _ = ‖z₁ - z₂‖ / 4 := by ring
      have ht2 : ‖z₂ * (Complex.exp (dS z₁) - Complex.exp (dS z₂))‖ ≤ ‖z₁ - z₂‖ / 4 := by
        have hsplit : Complex.exp (dS z₁) - Complex.exp (dS z₂)
            = Complex.exp (dS z₂) * (Complex.exp (dS z₁ - dS z₂) - 1) := by
          rw [Complex.exp_sub]
          field_simp [Complex.exp_ne_zero]
        rw [hsplit, norm_mul, norm_mul]
        have h2 : ‖Complex.exp (dS z₁ - dS z₂) - 1‖ ≤ 2 * ‖dS z₁ - dS z₂‖ :=
          Complex.norm_exp_sub_one_le hLip1
        have h3 : ‖dS z₁ - dS z₂‖ ≤ C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2 := hlip12
        have hnn : (0 : ℝ) ≤ C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2 := by positivity
        have h4 : ‖Complex.exp (dS z₂)‖ * ‖Complex.exp (dS z₁ - dS z₂) - 1‖
            ≤ 2 * (2 * (C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2)) := by
          have h5 : (0 : ℝ) ≤ ‖Complex.exp (dS z₁ - dS z₂) - 1‖ := norm_nonneg _
          nlinarith [hexp2, h2, h3, hnn, h5]
        have h6 : ‖z₂‖ * (‖Complex.exp (dS z₂)‖ * ‖Complex.exp (dS z₁ - dS z₂) - 1‖)
            ≤ 4 * ‖z₁‖ * (2 * (2 * (C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2))) := by
          have h7 : (0 : ℝ) ≤ ‖Complex.exp (dS z₂)‖ * ‖Complex.exp (dS z₁ - dS z₂) - 1‖ :=
            mul_nonneg (norm_nonneg _) (norm_nonneg _)
          calc ‖z₂‖ * (‖Complex.exp (dS z₂)‖ * ‖Complex.exp (dS z₁ - dS z₂) - 1‖)
              ≤ 4 * ‖z₁‖ * (‖Complex.exp (dS z₂)‖ * ‖Complex.exp (dS z₁ - dS z₂) - 1‖) :=
                mul_le_mul_of_nonneg_right hbig h7
            _ ≤ 4 * ‖z₁‖ * (2 * (2 * (C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2))) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
        have h8 : 4 * ‖z₁‖ * (2 * (2 * (C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2)))
            ≤ ‖z₁ - z₂‖ / 4 := by
          have h9 : 4 * ‖z₁‖ * (2 * (2 * (C * ‖z₁ - z₂‖ / ‖z₁‖ ^ 2)))
              = 16 * C * ‖z₁ - z₂‖ / ‖z₁‖ := by
            have h10 : (‖z₁‖ : ℝ) ≠ 0 := ne_of_gt hz1pos
            field_simp
            ring
          rw [h9, div_le_iff₀ hz1pos]
          nlinarith [norm_nonneg (z₁ - z₂), hz1big, hC.le]
        linarith
      linarith
    · -- the point is far from `z₁`: crude bounds suffice
      have hsep' : ‖z₁‖ / 2 < ‖z₂ - z₁‖ := lt_of_not_ge hsep
      have hsep'' : ‖z₁‖ / 2 < ‖z₁ - z₂‖ := by rwa [norm_sub_rev] at hsep'
      have hsep16 : 16 ≤ (1 / 2) * ‖z₁ - z₂‖ := by linarith
      linarith

/-- **`Φ` is injective on an outer annulus**, given the diagonal Lipschitz estimate. -/
theorem far_injOn_of_lipschitz {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    (hlip : ∀ x y : ℂ, r ≤ ‖x‖ → ‖y - x‖ ≤ ‖x‖ / 2 →
      ‖Work.Bottcher.bottcherSeries x x - Work.Bottcher.bottcherSeries y y‖
        ≤ C * ‖x - y‖ / ‖x‖ ^ 2) :
    ∃ R : ℝ, Set.InjOn Work.ParamRays.Phi {c : ℂ | R ≤ ‖c‖} := by
  obtain ⟨R, hR⟩ := exists_lipschitz_sub_id hr hC hlip
  refine ⟨max R 0, ?_⟩
  refine Work.MRMT.Found.injOn_of_lipschitz_away (R := max R 0) (fun a b ha hb => ?_)
  exact hR a b (le_trans (le_max_left _ _) ha) (le_trans (le_max_left _ _) hb)

end Work.NAKANE
