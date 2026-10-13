/-
Copyright: work module for the Elgindi finite-time singularity project.

# Per-slice mass bound for the mode coefficients (`cmode`)

The honesty layer bounds the mode coefficients `cmode m F z` of a slice by the angular
`L²`-norm of the slice with the paper's weight `σ θ = sin(2θ)^{-η}` (see
`cmode_sq_le_slice`, whose hypothesis is the integrability of that weighted square).  This
module supplies the two integral facts that go with it, for a datum which is `C^∞` on the
open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and honestly in `ℋ¹`
(`Work.Spaces.HkMem α 1 F`):

* the slice mass `θ ↦ (F z θ)² · sin(2θ)^{-η}` is integrable on `Iθ`, and
  `w z ^ 2 · ∫_θ (F z θ)² σ θ ≤ ∫_θ HkIntegrand α 1 F z θ`;
* the same for the `z`-derivative, with the extra factor `(z · w z)^2`:
  `θ ↦ (∂_z F z θ)² · sin(2θ)^{-η}` is integrable on `Iθ`, and
  `z ^ 2 · w z ^ 2 · ∫_θ (∂_zF z θ)² σ θ ≤ ∫_θ HkIntegrand α 1 F z θ`.

**Route.**  Everything is the `k = 1` instance of the elementary fact that `HkIntegrand` is a
sum of squares.  The pointwise identity `SmoothOpen`'s companion
`AngSecond.sq_mul_W`,

  `(g z θ · w z / sin(2θ)^{η/2})² = g z θ · g z θ · w z² · σ θ`  on `Iθ`

(whose endpoint case `sin 2θ = 0` is handled by `Real.zero_rpow`), turns the `i`-th pure
`D_z`-summand of `HkIntegrand α 1 F` into exactly the weighted square appearing in the
statement: for `g = F` (`i = 0`, `DzIter 0 F = F`) and for `g = ∂_zF` (`i = 1`,
`DzIter 1 F z θ = z · ∂_zF z θ`), the extra factor being `w z²` resp. `z² · w z²`.  Both
integrability statements are then the corresponding instance of
`EllipticEst.integrableOn_zSummand` (dividing by the non-zero constant `w z²` resp.
`z² w z²`, legitimate since `z > 0`), and both inequalities are
`MeasureTheory.integral_mono_of_nonneg` against `Spaces.sq_le_HkIntegrand_z` (a single
summand of a sum of squares is dominated by the sum), after pulling the constant out of the
integral with `integral_mul_const`.

No hypothesis on `F` beyond the two named ones is used, and the bound is sharp in the sense
that both sides are the same integral when one discards the other summands of
`HkIntegrand`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **The pointwise identity.**  On `Iθ`, the weighted square of `g` is the product of the
`σ`-weighted square, the radial weight `w z²` and the angular weight `σ θ`; this is
`AngSecond.sq_mul_W` with the abbreviations `w2`, `sig` unfolded. -/
private lemma sq_mul_W_explicit {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 := by
  rw [Work.FTS.EllipticEst.AngSecond.sq_mul_W g hθ]
  rw [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- **The pointwise identity for `D_z`.**  On `Iθ` the second (`i = 1`) pure `D_z`-summand of
`HkIntegrand`, `(D_z F · w / sin(2θ)^{η/2})²`, is the `∂_zF`-mass times `z² · w z²`. -/
private lemma sq_mul_W_explicit_Dz {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter 1 F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (z ^ 2 * (Work.Spaces.w z) ^ 2) := by
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  rw [show (z * Work.Spaces.pz F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.pz F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 * z ^ 2
      from by ring]
  rw [Work.FTS.EllipticEst.AngSecond.sq_mul_W (Work.Spaces.pz F) hθ]
  rw [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- **The slice-mass bound.**  For `F` smooth on the open quadrant and honestly in `ℋ¹`, and
every `z > 0`, the slice masses of `F` and of `∂_zF` (with the weight `sin(2θ)^{-η}`) are
integrable on `Iθ` and are bounded by the slice integral of `HkIntegrand α 1 F`, after
multiplying by the appropriate powers of the radial weight (`w z²` resp. `z² w z²`). -/
theorem cmode_slice_mass_le {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  -- the two radial weights are non-zero (`z > 0`)
  have hw2pos : 0 < (Work.Spaces.w z) ^ 2 :=
    pow_pos (Work.FTS.EllipticEst.AngSecond.w_pos hz) 2
  have hzw2pos : 0 < z ^ 2 * (Work.Spaces.w z) ^ 2 := mul_pos (pow_pos hz 2) hw2pos
  -- the slice integrability of the `ℋ¹`-integrand
  have hHz := hF.1 z hzI
  -- the two single summands of `HkIntegrand α 1 F` that we compare with
  have hs0 := Work.FTS.EllipticEst.integrableOn_zSummand α 1 hsm hF 0 (by norm_num) hzI
  have hs1 := Work.FTS.EllipticEst.integrableOn_zSummand α 1 hsm hF 1 (by norm_num) hzI
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- integrability of the `F`-mass: it is the `i = 0` summand divided by `w z²`
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.mul_const hs0 ((Work.Spaces.w z) ^ 2)⁻¹) ?_ measurableSet_Icc
    intro θ hθ
    change (Work.Spaces.DzIter 0 F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹
      = (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [Work.Spaces.DzIter_zero, sq_mul_W_explicit (g := F) hθ, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hw2pos), mul_one]
  · -- the mass bound: pull out `w z²` and compare with the `i = 0` summand
    calc (∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (Work.Spaces.w z) ^ 2
        = ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.w z) ^ 2 := (MeasureTheory.integral_mul_const _ _).symm
      _ = ∫ θ in Work.Spaces.Iθ,
            (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
          exact (sq_mul_W_explicit (g := F) hθ).symm
      _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => sq_nonneg _) hHz
            (Filter.Eventually.of_forall fun θ => ?_)
          exact Work.Spaces.sq_le_HkIntegrand_z α 1 F z θ 0 (by norm_num)
  · -- integrability of the `∂_zF`-mass: it is the `i = 1` summand divided by `z² w z²`
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.mul_const hs1 ((z ^ 2 * (Work.Spaces.w z) ^ 2))⁻¹) ?_
      measurableSet_Icc
    intro θ hθ
    change (Work.Spaces.DzIter 1 F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        * ((z ^ 2 * (Work.Spaces.w z) ^ 2))⁻¹
      = (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [sq_mul_W_explicit_Dz (F := F) hθ, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hzw2pos), mul_one]
  · -- the `∂_zF`-mass bound: pull out `z² w z²` and compare with the `i = 1` summand
    calc (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (z ^ 2 * (Work.Spaces.w z) ^ 2) := (MeasureTheory.integral_mul_const _ _).symm
      _ = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
          exact (sq_mul_W_explicit_Dz (F := F) hθ).symm
      _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => sq_nonneg _) hHz
            (Filter.Eventually.of_forall fun θ => ?_)
          exact Work.Spaces.sq_le_HkIntegrand_z α 1 F z θ 1 (by norm_num)

end Work.FTS.PhiStar.Honesty
