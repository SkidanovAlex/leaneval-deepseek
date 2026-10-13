import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The near-`0` slice mass is `L¹(z^{-4}dz)` under `HkMem α 0`

For `F : ℝ → ℝ → ℝ` with `F ∈ H⁰(α)` in the sense of `Work.Spaces.HkMem α 0 F`, the
`z`-function

  `z ↦ (∫_θ F z θ² · sin(2θ)^{-η}) / z⁴`

is integrable on `(0,1)`.

The point is only the *weight* bookkeeping.  At level `k = 0` the `H^k`-integrand collapses to
the single pure radial term

  `HkIntegrand α 0 F z θ = (F z θ · w z / sin(2θ)^{η/2})² = w z² · F z θ² · sin(2θ)^{-η}`,

so the slice integral occurring in `HkMem` is exactly `w z² = (1+z)⁴/z⁴` times the slice mass
above:

  `∫_θ HkIntegrand α 0 F z θ = w z² · ∫_θ F z θ² · sin(2θ)^{-η}`.

Since `HkMem α 0 F` gives the integrability on `[0,∞)` of that slice integral, and since

  `(∫_θ F z θ² sin(2θ)^{-η}) / z⁴ = (∫_θ HkIntegrand α 0 F z θ) / (1+z)⁴`   (`z ≠ 0`),

while `(1+z)⁴ ≥ 1` for `z > 0`, the target function is dominated on `(0,1)` by the (integrable)
`z ↦ ∫_θ HkIntegrand α 0 F z θ`.  The `z = 0` value is irrelevant: the interval is `(0,1)`.

This is the near-`0` engine of the `PhiStar/Honesty` layer (paired with the far-`∞` statement
`integrableOn_sliceMass_Ioi_one_of_HkMem`).
-/

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem integrableOn_sliceMass_div_z4_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / z ^ 4)
      (Set.Ioo 0 1) := by
  -- The `H⁰`-integrand of `HkMem` is `w z²` times the slice mass appearing in the target.
  have hBG : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro z
    rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        = ∫ θ in Work.Spaces.Iθ, F z θ * F z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
        from setIntegral_congr_fun measurableSet_Icc
          (fun θ hθ => by
            rw [HkIntegrand_zero_eq α F z θ,
              Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ])]
    rw [show (∫ θ in Work.Spaces.Iθ,
          F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.w2 z
            * (F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        from setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  -- On `(0,1)` the two quotients agree, because `w z² · z⁴ = (1+z)⁴`.
  have hkey : ∀ z ∈ Set.Ioo (0:ℝ) 1,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ) / (1 + z) ^ 4
        = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
            / z ^ 4 := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz.1
    have hw : Work.FTS.EllipticEst.AngSecond.w2 z * z ^ 4 = (1 + z) ^ 4 := by
      rw [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
      field_simp [hz0]
    have hw0 : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
      have hwz : Work.Spaces.w z ≠ 0 :=
        div_ne_zero (pow_ne_zero 2 (by linarith [hz.1] : (1:ℝ) + z ≠ 0)) (pow_ne_zero 2 hz0)
      simpa [Work.FTS.EllipticEst.AngSecond.w2] using pow_ne_zero 2 hwz
    rw [hBG z, ← hw]
    field_simp
  -- `HkMem α 0 F` gives the integrability of the slice integral on `[0,∞)`, hence on `(0,1)`.
  have hBint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ) (Set.Ioo 0 1) :=
    hF.2.mono_set (fun z hz => le_of_lt hz.1)
  -- Dividing by `(1+z)⁴ ≥ 1` keeps integrability, since it does not increase the modulus.
  have hSint : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ) / (1 + z) ^ 4)
      (Set.Ioo 0 1) := by
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
          / (1 + z) ^ 4)
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
      hBint.aestronglyMeasurable.mul
        ((measurable_inv.comp
          ((measurable_const.add measurable_id).pow_const 4)).aestronglyMeasurable)
    refine (hBint.norm).mono' haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have h1 : (1:ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith [hz.1])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < (1 + z) ^ 4)]
    exact div_le_self (abs_nonneg _) h1
  exact hSint.congr_fun (fun z hz => hkey z hz) measurableSet_Ioo

end Work.FTS.PhiStar.Honesty
