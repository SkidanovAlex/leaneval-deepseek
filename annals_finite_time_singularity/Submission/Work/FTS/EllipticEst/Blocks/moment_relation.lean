/-
Copyright: work module for the Elgindi finite-time singularity project.

# `moment_relation`: the angular moment is an antiderivative of its `z`-derivative

This module proves `Work.FTS.EllipticEst.Blocks.moment_relation`, the analytic input that
makes the angular moment `F_*(u)(z) = ∫_θ u(z,θ) sinθcos²θ dθ` a *radial* quantity of the
paper's §EllipticRegularityEstimates

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

(`L₁₂(F)(z) = 3∫_z^∞ F_*(F)(r)/r dr`).

The proof has three formally independent parts, each isolated as a lemma above the target:

* `integral_Icc_integral_Itheta_swap` — Fubini on the box `[a,b] × Iθ`
  (`Measure.prod_restrict` + `MeasureTheory.integral_integral_swap`);
* `integral_Icc_pz_mul_sinCos2` — the radial fundamental rule of calculus on a slice
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt` applied to the `C^∞` slice of `u`
  obtained from `SmoothOpen`);
* `integrableOn_box_pz_mul_sinCos2` — joint integrability on the box of
  `∂_z u · sinθcos²θ` from the weighted `L²`-integrability of `∂_z u`
  (`hbox`): AM–GM with the factorisation
  `∂_z u · sinθcos²θ = (∂_z u · sin(2θ)^{-η/2}) · (sinθcos²θ · sin(2θ)^{η/2})`.

All three are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## Fubini on the box `[a,b] × Iθ` -/

/-- **Fubini on a radial box.**  For a function jointly integrable on `[a,b] × Iθ` the two
iterated integrals agree.  This is `MeasureTheory.integral_integral_swap` after rewriting the
restriction of the planar Lebesgue measure to the box as the product of the restrictions
(`MeasureTheory.Measure.prod_restrict`). -/
lemma integral_Icc_integral_Itheta_swap {g : ℝ → ℝ → ℝ} {a b : ℝ}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :
    ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ, g s θ)
      = ∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc a b, g s θ) := by
  have hg' : Integrable (Function.uncurry g)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hg
  exact MeasureTheory.integral_integral_swap hg'

/-! ## The radial fundamental rule of calculus on a slice -/

/-- **The `z`-slice moment.**  For `u` smooth on the open quadrant, an interior angle
`θ ∈ (0,π/2)` and `0 < a < b`, the integral over `[a,b]` of `∂_z u(·,θ) · sinθcos²θ` is
`(u b θ - u a θ) · sinθcos²θ`: the constant `sinθcos²θ` factors out of the integral and the
fundamental rule of calculus along the (smooth) radial slice does the rest. -/
lemma integral_Icc_pz_mul_sinCos2 (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u)
    {a b θ : ℝ} (ha : 0 < a) (hab : a < b) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ
      = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
  -- the radial derivative is continuous on the interval
  have hcont : ContinuousOn (fun r : ℝ => Work.Spaces.pz u r θ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact ((hu.pz).curry_z hθ).continuousOn.mono (fun r hr => lt_of_lt_of_le ha hr.1)
  -- and is the derivative of the slice at every interior point
  have hderiv : ∀ r ∈ Set.uIcc a b,
      HasDerivAt (fun r : ℝ => u r θ) (Work.Spaces.pz u r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hab.le] at hr
    exact hu.hasDerivAt_slice hθ (lt_of_lt_of_le ha hr.1)
  have hFTC : ∫ s in Set.Icc a b, Work.Spaces.pz u s θ = u b θ - u a θ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hFTC]
  exact MeasureTheory.integral_mul_const _ _

/-! ## Joint integrability of the moment integrand on the box -/

/-- **Joint integrability of `∂_z u · sinθcos²θ` on a radial box.**  From the weighted
`L²`-integrability of `∂_z u` (`hbox`, the weight being `sin(2θ)^{-η}`) and the smoothness of
`u` on the open quadrant, the product `∂_z u · sinθcos²θ` is jointly integrable on
`[a,b] × Iθ`.

The bound is the AM–GM inequality applied to the factorisation
`∂_z u · sinθcos²θ = (∂_z u · sin(2θ)^{-η/2}) · (sinθcos²θ · sin(2θ)^{η/2})`; since
`|sinθcos²θ| ≤ 1` and `0 ≤ sin(2θ) ≤ 1` on `Iθ`, the second factor is bounded by `1` and the
square of the first is `(∂_z u)² sin(2θ)^{-η}`, whence the pointwise domination
`|∂_z u · sinθcos²θ| ≤ ½ (∂_z u)² sin(2θ)^{-η} + ½`.
A.e. strong measurability comes from `SmoothOpen u`: `∂_z u` is continuous on the open
quadrant, and the box differs from the open quadrant only by null lines. -/
lemma integrableOn_box_pz_mul_sinCos2 (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hηne : -(Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  -- the box has finite measure
  have hvolFin : volume (Set.Icc a b ×ˢ Work.Spaces.Iθ) < ⊤ :=
    (isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)).measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    isFiniteMeasure_restrict.mpr hvolFin.ne
  -- the dominating function is integrable
  have hbase : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := hbox a b ha hab
  have hdom : Integrable (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2)
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (hbase.const_mul (1 / 2)).add (integrable_const (1 / 2))
  -- a.e. strong measurability, from continuity of `∂_z u` on the open quadrant
  have hsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun x hx => le_trans (le_of_lt ha) hx.1) subset_rfl
  have hmono : volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hsub le_rfl
  have haesm : AEStronglyMeasurable
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      ((hu.pz).continuousOn.mul (((by unfold Work.Elliptic.sinCos2; fun_prop :
        Continuous Work.Elliptic.sinCos2).comp continuous_snd).continuousOn))).mono_measure hmono
  -- the pointwise domination
  have hpt : ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)),
      ‖Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) p‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
    rw [MeasureTheory.ae_restrict_iff' (s := Set.Icc a b ×ˢ Work.Spaces.Iθ)
      (measurableSet_Icc.prod measurableSet_Icc)]
    refine Filter.Eventually.of_forall fun p hp => ?_
    have hθ : p.2 ∈ Work.Spaces.Iθ := hp.2
    have hx0 : 0 ≤ Real.sin (2 * p.2) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    have hx1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    -- `|sinθcos²θ| ≤ 1`
    have hC : |Work.Elliptic.sinCos2 p.2| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul]
      have h1 : |Real.sin p.2| ≤ 1 := Real.abs_sin_le_one p.2
      have h2 : |Real.cos p.2 ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg (Real.cos p.2))]
        nlinarith [Real.abs_cos_le_one p.2, abs_nonneg (Real.cos p.2), sq_abs (Real.cos p.2)]
      calc |Real.sin p.2| * |Real.cos p.2 ^ 2| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    show ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2
    -- AM–GM for the radial factor
    have hAF : |Work.Spaces.pz u p.1 p.2|
        ≤ (1 / 2) * (Work.Spaces.pz u p.1 p.2) ^ 2 + 1 / 2 := by
      nlinarith [sq_abs (Work.Spaces.pz u p.1 p.2),
        sq_nonneg (|Work.Spaces.pz u p.1 p.2| - 1)]
    by_cases hx : Real.sin (2 * p.2) = 0
    · -- at the degenerate angles `sinθcos²θ` vanishes and the weight kills the other term
      have hC0 : Work.Elliptic.sinCos2 p.2 = 0 := by
        have h2 : Real.sin p.2 * Real.cos p.2 = 0 := by
          have h3 := Real.sin_two_mul p.2
          rw [hx] at h3
          linarith
        rw [Work.Elliptic.sinCos2]
        rcases mul_eq_zero.mp h2 with h | h
        · rw [h, zero_mul]
        · rw [pow_two, h, mul_zero, mul_zero]
      rw [hC0, hx, Real.zero_rpow hηne]
      simp only [mul_zero, norm_zero]
      norm_num
    · have hxpos : 0 < Real.sin (2 * p.2) := lt_of_le_of_ne hx0 (Ne.symm hx)
      -- the weight `sin(2θ)^{-η}` is at least `1`
      have hxle : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
        have h1 : (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) ≤ 1 :=
          Real.rpow_le_one hx0 hx1 (by norm_num [Work.Spaces.eta])
        have h2 : 0 < (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) := Real.rpow_pos_of_pos hxpos _
        rw [Real.rpow_neg hxpos.le]
        exact (one_le_inv₀ h2).mpr h1
      have hstep : ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
          ≤ |Work.Spaces.pz u p.1 p.2| := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hC
      have hle2 : (1 / 2) * (Work.Spaces.pz u p.1 p.2) ^ 2 + 1 / 2
          ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
        have h4 := mul_le_mul_of_nonneg_left hxle (sq_nonneg (Work.Spaces.pz u p.1 p.2))
        nlinarith
      linarith
  exact Integrable.mono' hdom haesm hpt

/-! ## The target -/

/-- **The angular moment is an antiderivative of its `z`-derivative.**  For a function `u` smooth on the open quadrant whose slices and whose `z`-derivative's weighted square are integrable,

`F_*(u)(b) = F_*(u)(a) + ∫_a^b (∫_θ ∂_z u(s,θ) sin θ cos²θ dθ) ds`,

i.e. `d/dz F_*(u)(z) = ∫_θ ∂_z u(z,θ) sinθcos²θ dθ`, with `F_*(u)(z) = ∫_θ u(z,θ) sinθcos²θ dθ` (`Work.Elliptic.Fstar`).  This is the analytic input that makes the angular moment `F_*` a function of the *radial* Hardy/integration-by-parts arguments of the paper (`L₁₂(F)(z) = 3∫_z^∞ F_*(F)(r)/r dr`, Lemma `L12H`, `HardyInequality4`).

ROUTE (Fubini + FTC, as in the sibling file `Submission.Work.FTS.EllipticEst.moment_relation`): from `hbox`, Cauchy–Schwarz with `sinCos2 θ · sin(2θ)^{η/2}` (integrable on `Iθ`) gives the joint integrability of `|∂_z u · sinCos2|` on `[a,b] × Iθ`; for each `θ`, `SmoothOpen` gives `∫_a^b ∂_z u(s,θ) ds = u b θ - u a θ`; `hsl` gives the `θ`-integrability of the difference; then `MeasureTheory.integral_integral_swap` (or `intervalIntegral.integral_integral_swap`) finishes. -/
theorem moment_relation (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  -- joint integrability on the box
  have hjoint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    integrableOn_box_pz_mul_sinCos2 u hu hbox ha hab
  -- the slice identity holds for a.e. angle
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
        = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
    have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hst]
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioo 0 (Real.pi / 2))
      measurableSet_Ioo] with θ hθ
    exact integral_Icc_pz_mul_sinCos2 u hu ha hab hθ
  -- Fubini, then the `θ`-integral of the difference
  have hkey : ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := by
    rw [integral_Icc_integral_Itheta_swap hjoint]
    calc ∫ θ in Work.Spaces.Iθ,
          (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ :=
          MeasureTheory.integral_congr_ae hae
      _ = ∫ θ in Work.Spaces.Iθ,
            (u b θ * Work.Elliptic.sinCos2 θ - u a θ * Work.Elliptic.sinCos2 θ) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          ring
      _ = (∫ θ in Work.Spaces.Iθ, u b θ * Work.Elliptic.sinCos2 θ)
            - (∫ θ in Work.Spaces.Iθ, u a θ * Work.Elliptic.sinCos2 θ) :=
          MeasureTheory.integral_sub (hsl b hb) (hsl a ha)
      _ = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := rfl
  linarith [hkey]

end Work.FTS.EllipticEst.Blocks
