import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## A continuity helper -/

/-- `(r,θ) ↦ sinθcos²θ` is continuous (it only depends on `θ`). -/
private lemma continuous_sinCos2_snd :
    Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
  have h : (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      = fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p
    simp only [Work.Elliptic.sinCos2]
  rw [h]
  exact (Real.continuous_sin.comp continuous_snd).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)

/-! ## The statement

The proof is the AM–GM domination of `∂_z f · sinθcos²θ` by the first `D_z`-slot of the
`ℋ¹`-integrand.  On the box `(s,z] × Iθ` we have `r ≥ s > 0`, so

* `pzSqSeta_le_Dz1_mul` gives `(∂_z f)² sin(2θ)^{-η} ≤ C·(D_z f · w/sin(2θ)^{η/2})²` with the
  box constant `C = z²/(1+s)⁴`, and `sin(2θ)^{-η} ≥ 1` away from the degenerate angles;
* `|sinθcos²θ| ≤ 1`, so `|∂_z f·sinθcos²θ| ≤ |∂_z f| ≤ ½(∂_z f)² + ½`;
* the `D_z`-slot is integrable on the box by `integrable_prod_sq_restrict_open` (the `i = 1`
  slot, valid at level `1` because `HkMem α 1 f`), the constant `½` is integrable because the
  box has finite measure, and a.e. strong measurability is
  `aesm_uncurry_restrict_open` (continuity on the open quadrant from `SmoothOpen.pz`). -/
theorem PzSinCos2Box {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 1 f)
    {s z : ℝ} (hs : 0 < s) (hsz : s < z) :
    MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set C : ℝ := z ^ 2 / (1 + s) ^ 4 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  -- the first `D_z`-slot of the `ℋ¹`-integrand is integrable on the box
  have hslot := Work.FTS.EllipticEst.integrable_prod_sq_restrict_open α 1 f hsm hmem 1
    (le_refl 1) (a := s) (b := z) (le_of_lt hs)
  -- a.e. strong measurability on the box
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
      ((hsm.pz).continuousOn.mul continuous_sinCos2_snd.continuousOn) (le_of_lt hs)
  -- the dominating function is integrable (the box has finite measure)
  have hdom : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (1 / 2 : ℝ) * (C * (Work.Spaces.DzIter 1 f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) + 1 / 2)
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (((hslot.const_mul C).const_mul (1 / 2))).add (integrable_const (1 / 2))
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  -- the pointwise domination, a.e. on the box
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ioc.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)) fun p hp => ?_
  obtain ⟨hr, hθ⟩ := hp
  have hθI : p.2 ∈ Work.Spaces.Iθ := hθ
  have hrIcc : p.1 ∈ Set.Icc s z := ⟨le_of_lt hr.1, hr.2⟩
  have hkey := Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul
    (f := f) hs hsz p.1 hrIcc p.2 hθI
  show ‖Work.Spaces.pz f p.1 p.2 * Work.Elliptic.sinCos2 p.2‖ ≤
    (1 / 2 : ℝ) * (C * (Work.Spaces.DzIter 1 f p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) + 1 / 2
  by_cases hx : Real.sin (2 * p.2) = 0
  · -- degenerate angles: `sinθcos²θ` vanishes
    have hC0 : Work.Elliptic.sinCos2 p.2 = 0 := by
      have h2 : Real.sin p.2 * Real.cos p.2 = 0 := by
        have h3 := Real.sin_two_mul p.2
        rw [hx] at h3
        linarith
      rw [Work.Elliptic.sinCos2]
      rcases mul_eq_zero.mp h2 with h | h
      · rw [h, zero_mul]
      · rw [pow_two, h, mul_zero, mul_zero]
    rw [hC0, mul_zero, norm_zero]
    have hnn : 0 ≤ (1 / 2 : ℝ) * (C * (Work.Spaces.DzIter 1 f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      mul_nonneg (by norm_num) (mul_nonneg hCnn (sq_nonneg _))
    linarith
  · -- non-degenerate angles
    have hsin0 : 0 ≤ Real.sin (2 * p.2) := Work.Spaces.sin_two_nonneg_of_Iθ hθI
    have hxpos : 0 < Real.sin (2 * p.2) := lt_of_le_of_ne hsin0 (Ne.symm hx)
    have hone : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
      have hle1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
      have h2 : (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) ≤ 1 :=
        Real.rpow_le_one hsin0 hle1 (by rw [Work.Spaces.eta]; norm_num)
      have h3 : 0 < (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) :=
        Real.rpow_pos_of_pos hxpos _
      rw [Real.rpow_neg hxpos.le]
      exact (one_le_inv₀ h3).mpr h2
    have hsq : (Work.Spaces.pz f p.1 p.2) ^ 2 ≤ C * (Work.Spaces.DzIter 1 f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      calc (Work.Spaces.pz f p.1 p.2) ^ 2
          = (Work.Spaces.pz f p.1 p.2) ^ 2 * 1 := by ring
        _ ≤ (Work.Spaces.pz f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left hone (sq_nonneg _)
        _ ≤ C * (Work.Spaces.DzIter 1 f p.1 p.2
              * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := hkey
    have hAM : |Work.Spaces.pz f p.1 p.2|
        ≤ (1 / 2 : ℝ) * (Work.Spaces.pz f p.1 p.2) ^ 2 + 1 / 2 := by
      nlinarith [sq_abs (Work.Spaces.pz f p.1 p.2),
        sq_nonneg (|Work.Spaces.pz f p.1 p.2| - 1)]
    have habs : |Work.Elliptic.sinCos2 p.2| ≤ 1 :=
      Work.FTS.EllipticEst.abs_sinCos2_le_one hθI
    calc ‖Work.Spaces.pz f p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        = |Work.Spaces.pz f p.1 p.2| * |Work.Elliptic.sinCos2 p.2| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |Work.Spaces.pz f p.1 p.2| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = |Work.Spaces.pz f p.1 p.2| := mul_one _
      _ ≤ (1 / 2 : ℝ) * (Work.Spaces.pz f p.1 p.2) ^ 2 + 1 / 2 := hAM
      _ ≤ (1 / 2 : ℝ) * (C * (Work.Spaces.DzIter 1 f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) + 1 / 2 := by
          have h := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
          linarith

end Work.FTS.ClassC
