/-
# `Work.FTS.EllSol.EllPkgAux.ThMollAux0` — generic helpers for the `θ`-mollification transfer

Self-contained lemmas used by `thMollTransfer2` and by the auxiliary lemmas about it:

* `abs_sKer_le_inv` : the bump `sKer ε` is bounded by its normalising constant;
* `integral_comp_neg_eq` : change of variables `x ↦ -x` on the line;
* `integral_mul_Qcut` : multiplying by the indicator `Qcut g = 1_{Iθ}·g` turns a line integral
  into the set integral over `Iθ`;
* `setIntegral_Iθ_eq_interval`, `interval_eq_setIntegral_Iθ` : `∫_{Iθ}` against `∫_0^{π/2}`;
* `integrable_sKer_mul_of_integrable` : a bump times an integrable function is integrable;
* `ibp_first_pi` : integration by parts on `[0, π/2]` with interior differentiability.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ

/-- The bump is bounded by its normalising constant. -/
theorem abs_sKer_le_inv {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |sKer ε t| ≤ (ε * sMass)⁻¹ := by
  have hD : 0 ≤ (ε * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)
  rw [sKer, abs_mul, abs_of_nonneg hD]
  refine mul_le_of_le_one_right hD ?_
  rw [abs_le]
  exact ⟨by linarith [sBump_nonneg (t / ε)], sBump_le_one (t / ε)⟩

/-- Change of variables `x ↦ -x` for the Lebesgue integral on the line. -/
theorem integral_comp_neg_eq (f : ℝ → ℝ) : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
  have h := MeasureTheory.Measure.integral_comp_mul_left f (-1 : ℝ)
  simpa using h

/-- Multiplying by an indicator of `Iθ` turns a line integral into the set integral over `Iθ`. -/
theorem integral_mul_Qcut (f g : ℝ → ℝ) :
    (∫ s : ℝ, f s * Qcut g s) = ∫ s in Iθ, f s * g s := by
  have h : (fun s : ℝ => f s * Qcut g s)
      = (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator (fun s : ℝ => f s * g s) := by
    funext s
    rw [Qcut]
    exact (Set.indicator_mul_right _ f g).symm
  rw [h, MeasureTheory.integral_indicator measurableSet_Icc]
  rfl

/-- The set integral over `Iθ` is the interval integral from `0` to `π/2`. -/
theorem setIntegral_Iθ_eq_interval (f : ℝ → ℝ) :
    (∫ s in Iθ, f s) = ∫ s in (0 : ℝ)..(Real.pi / 2), f s := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]

theorem interval_eq_setIntegral_Iθ (f : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..(Real.pi / 2), f s) = ∫ s in Iθ, f s :=
  (setIntegral_Iθ_eq_interval f).symm

/-! ## Integrability of a bump times an integrable function -/

/-- A bump of radius `ε` times an integrable function is integrable. -/
theorem integrable_sKer_mul_of_integrable {ε θ' : ℝ} (hε : 0 < ε) {F : ℝ → ℝ}
    (hF : Integrable F) : Integrable (fun s : ℝ => sKer ε (θ' - s) * F s) := by
  have hD : 0 ≤ (ε * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)
  have hcont : Continuous (fun s : ℝ => sKer ε (θ' - s)) :=
    ((contDiff_sKer ε (n := 3)).continuous).comp (continuous_const.sub continuous_id)
  have hm : AEStronglyMeasurable (fun s : ℝ => sKer ε (θ' - s) * F s) volume :=
    hcont.aestronglyMeasurable.mul hF.1
  refine MeasureTheory.Integrable.mono' (g := fun s : ℝ => (ε * sMass)⁻¹ * ‖F s‖) ?_ hm ?_
  · simpa only [Real.norm_eq_abs] using hF.norm.const_mul ((ε * sMass)⁻¹)
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_sKer_le_inv hε (θ' - s)) (abs_nonneg (F s))

/-! ## The angle interval bookkeeping -/

theorem measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

theorem pi_half_pos : (0 : ℝ) < Real.pi / 2 := by positivity

/-- Weighted integration by parts on `[0, π/2]` with interior differentiability. -/
theorem ibp_first_pi {u u' g h : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) (Real.pi / 2)))
    (hu' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (u' x) x)
    (hg' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (h x) x)
    (hu'int : IntervalIntegrable u' volume 0 (Real.pi / 2))
    (hhint : IntervalIntegrable h volume 0 (Real.pi / 2)) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), u x * h x)
      = u (Real.pi / 2) * g (Real.pi / 2) - u 0 * g 0
        - ∫ x in (0 : ℝ)..(Real.pi / 2), u' x * g x := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := pi_half_pos.le
  have hmin : min (0 : ℝ) (Real.pi / 2) = 0 := min_eq_left hle
  have hmax : max (0 : ℝ) (Real.pi / 2) = Real.pi / 2 := max_eq_right hle
  refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := Real.pi / 2) ?_ ?_ ?_ ?_ hu'int hhint
  · simpa only [Set.uIcc_of_le hle] using hu
  · simpa only [Set.uIcc_of_le hle] using hg
  · intro x hx
    rw [hmin, hmax] at hx
    exact hu' x hx
  · intro x hx
    rw [hmin, hmax] at hx
    exact hg' x hx

end Work.FTS.EllSol.EllPkgAux
