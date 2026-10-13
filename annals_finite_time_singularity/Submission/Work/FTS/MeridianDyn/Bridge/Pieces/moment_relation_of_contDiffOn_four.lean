/-
Copyright: work module for the Elgindi finite-time singularity project.

# The moment relation at smoothness order `4`

This module proves

  `Work.FTS.MeridianDyn.Bridge.Pieces.moment_relation_of_contDiffOn_four`,

the version of the angular-moment relation `F_*(u)(b) = F_*(u)(a) + ∫_a^b F_*(∂_z u)`
in which the datum is only assumed to be `C^4` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)`
(as it is in the `MeridianDyn` bridge, where `u` is a compactly supported local solution and
no global smoothness is available).

The delivered sibling `Work.FTS.EllipticEst.Blocks.moment_relation` proves the same identity
from `SmoothOpen u` (`C^∞` on the open quadrant).  All that its proof actually uses of the
datum is

* joint continuity of `∂_z u` on the open quadrant (for the a.e. strong measurability of the
  box integrand), and
* differentiability along every radial slice, at interior angles and positive radius
  (`HasDerivAt (fun r => u r θ) (∂_z u r θ) r`).

At order `4` both are available: `∂_z u` is `C^3` on `Q0` (`contDiffOn_pz_three` below, the
finite-order companion of `Work.FTS.LocData.contDiffOn_pz`), and `u` is differentiable at
every point of `Q0`.  The three further inputs of the proof (`hbox` for the AM–GM domination,
`hsl` for the `θ`-integrability of the two slices) are hypotheses of the statement, exactly as
in the sibling.

The proof is the same three-step route as the sibling:

* `integrableOn_box_pz_mul_sinCos2_of_four` — joint integrability of `∂_z u · sinθcos²θ` on
  `[a,b] × Iθ`, by AM–GM against `(∂_z u)² sin(2θ)^{-η}`;
* `integral_Icc_pz_mul_sinCos2_of_four` — the radial fundamental rule of calculus on a slice;
* Fubini (`Work.FTS.EllipticEst.Blocks.integral_Icc_integral_Itheta_swap`) and the
  `θ`-integral of the slice difference (`hsl`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Blocks.moment_relation
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

set_option maxHeartbeats 1000000

/-! ## The finite-order calculus of the open quadrant

The next three lemmas extract exactly the two properties of the datum that the moment
relation uses.  They are the order-`4` instances of the `C^∞`-statements
`Work.FTS.LocData.contDiffOn_pz` and `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`, and
avoid importing the `C^∞` vocabulary altogether. -/

/-- **`∂_z` costs one order.**  `pz` is the first partial of `fderiv ℝ (uncurry ·)` in the
direction `(1,0)`, and `fderiv` of a `C^4` function is `C^3` on an open set. -/
private theorem contDiffOn_pz_three {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 4 (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.pz G)) Work.FTS.EllipticEst.Q0 := by
  have hchain : ∀ p ∈ Work.FTS.EllipticEst.Q0, Function.uncurry (Work.Spaces.pz G) p
      = (fderiv ℝ (Function.uncurry G) p) (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
  have hfd : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := h.fderivWithin (m := 3) Work.FTS.EllipticEst.isOpen_Q0.uniqueDiffOn
      (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hp]
  have hcomp : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0))
      Work.FTS.EllipticEst.Q0 :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- **The radial slice is differentiable at interior points**, with derivative `∂_z u`. -/
private theorem hasDerivAt_slice_of_four {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 4 (Function.uncurry G) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' : ℝ => G z' θ) (Work.Spaces.pz G z θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
  have h1 : HasDerivAt (fun z' : ℝ => G z' θ) (deriv (fun z' : ℝ => G z' θ) z) z :=
    (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
  simpa only [Work.Spaces.pz] using h1

/-- Continuity of `r ↦ ∂_z u r θ` on `(0,∞)`, at an interior angle. -/
private theorem continuousOn_pz_slice_of_four {u : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun r : ℝ => Work.Spaces.pz u r θ) (Set.Ioi 0) := by
  have hpc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_pz_three h).continuousOn
  have hcurve : ContinuousOn (fun r : ℝ => (r, θ)) (Set.Ioi 0) :=
    (continuous_id.prodMk continuous_const).continuousOn
  exact hpc.comp hcurve (fun r hr =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hr, hθ.1, hθ.2⟩)

/-! ## The radial fundamental rule of calculus on a slice -/

/-- **The `z`-slice moment.**  For `u` of class `C^4` on the open quadrant, an interior angle
`θ ∈ (0,π/2)` and `0 < a < b`, the integral over `[a,b]` of `∂_z u(·,θ) · sinθcos²θ` is
`(u b θ - u a θ) · sinθcos²θ`. -/
private theorem integral_Icc_pz_mul_sinCos2_of_four (u : ℝ → ℝ → ℝ)
    (h : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {a b θ : ℝ} (ha : 0 < a) (hab : a < b) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ
      = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
  have hcont : ContinuousOn (fun r : ℝ => Work.Spaces.pz u r θ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact (continuousOn_pz_slice_of_four h hθ).mono
      (fun r hr => lt_of_lt_of_le ha hr.1)
  have hderiv : ∀ r ∈ Set.uIcc a b,
      HasDerivAt (fun r' : ℝ => u r' θ) (Work.Spaces.pz u r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hab.le] at hr
    exact hasDerivAt_slice_of_four h (lt_of_lt_of_le ha hr.1) hθ
  have hFTC : ∫ s in Set.Icc a b, Work.Spaces.pz u s θ = u b θ - u a θ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hFTC]
  exact MeasureTheory.integral_mul_const _ _

/-! ## Joint integrability of the moment integrand on the box -/

/-- **Joint integrability of `∂_z u · sinθcos²θ` on a radial box.**  From the weighted
`L²`-integrability of `∂_z u` (`hbox`, weight `sin(2θ)^{-η}`) and the joint continuity of
`∂_z u` on `Q0` (which order `4` gives), the product `∂_z u · sinθcos²θ` is jointly integrable
on `[a,b] × Iθ`.

The bound is AM–GM applied to `∂_z u · sinθcos²θ = (∂_z u · sin(2θ)^{-η/2}) ·
(sinθcos²θ · sin(2θ)^{η/2})`; since `|sinθcos²θ| ≤ 1` and `0 ≤ sin(2θ) ≤ 1` on `Iθ`, the
second factor is bounded by `1` and the square of the first is `(∂_z u)² sin(2θ)^{-η}`,
whence `|∂_z u · sinθcos²θ| ≤ ½ (∂_z u)² sin(2θ)^{-η} + ½`. -/
private theorem integrableOn_box_pz_mul_sinCos2_of_four (u : ℝ → ℝ → ℝ)
    (h : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hηne : -(Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_pz_three h).continuousOn).mul
      (((by unfold Work.Elliptic.sinCos2; fun_prop :
        Continuous Work.Elliptic.sinCos2).comp continuous_snd).continuousOn)
  have hvolFin : volume (Set.Icc a b ×ˢ Work.Spaces.Iθ) < ⊤ :=
    (isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)).measure_lt_top
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    isFiniteMeasure_restrict.mpr hvolFin.ne
  have hbase : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := hbox a b ha hab
  have hdom : Integrable (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2)
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (hbase.const_mul (1 / 2)).add (integrable_const (1 / 2))
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
      hcont).mono_measure hmono
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
        rcases mul_eq_zero.mp h2 with hh | hh
        · rw [hh, zero_mul]
        · rw [pow_two, hh, mul_zero, mul_zero]
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

/-- **The angular moment is an antiderivative of its `z`-derivative**, at smoothness order `4`.

For `u` of class `C^4` on the open quadrant `(0,∞) × (0,π/2)` whose `θ`-slices against
`sinθcos²θ` are integrable (`hsl`) and whose weighted square `(∂_z u)² sin(2θ)^{-η}` is
integrable on every box `[a,b] × Iθ` with `0 < a < b` (`hbox`):

`F_*(u)(b) = F_*(u)(a) + ∫_a^b (∫_θ ∂_z u(s,θ) sinθcos²θ dθ) ds`,
i.e. `d/dz F_*(u)(z) = ∫_θ ∂_z u(z,θ) sinθcos²θ dθ`, with
`F_*(u)(z) = ∫_θ u(z,θ) sinθcos²θ dθ` (`Work.Elliptic.Fstar`). -/
theorem moment_relation_of_contDiffOn_four (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  -- joint integrability of the moment integrand on the box
  have hjoint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    integrableOn_box_pz_mul_sinCos2_of_four u hu hbox ha hab
  -- the slice identity holds for a.e. angle
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
        = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
    have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hst]
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioo 0 (Real.pi / 2))
      measurableSet_Ioo] with θ hθ
    exact integral_Icc_pz_mul_sinCos2_of_four u hu ha hab hθ
  -- Fubini, then the `θ`-integral of the difference
  have hkey : ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := by
    rw [Work.FTS.EllipticEst.Blocks.integral_Icc_integral_Itheta_swap hjoint]
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

end Work.FTS.MeridianDyn.Bridge.Pieces
