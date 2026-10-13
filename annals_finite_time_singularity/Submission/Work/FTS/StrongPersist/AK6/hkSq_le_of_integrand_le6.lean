import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.WtoH_Angular
import Submission.Work.Elliptic.WtoH_IntZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkSq` from a pointwise bound on the `ℋ⁶`-integrand

If the `ℋ⁶`-integrand of `f` is dominated on the closed quadrant by the product of the radial
factor `1/(1+z)²` with the two angular profiles `A·sin(2θ)^{-η}` and
`B·(α+sin 2θ)²·sin(2θ)^{2α/5-γ(α)}`, then `|f|²_{ℋ⁶} ≤ 2(A·10⁴ + B·700)`.

This is the pointwise-to-`HkSq` bookkeeping: the two angular profiles have `θ`-integrals bounded
by `10⁴` resp. `700` uniformly in `α ∈ (0,1]` (`Work.Elliptic.WtoH_Angular`), while the radial
factor has `z`-integral `1 ≤ 2` over `Iz = [0,∞)` (`Work.Elliptic.WtoH_IntZ`).  The factors
multiply to `2(A·10⁴ + B·700)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.AK6

set_option autoImplicit false

theorem hkSq_le_of_integrand_le6 {α A B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) {f : ℝ → ℝ → ℝ} (hpt : ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), θ ∈ Work.Spaces.Iθ → Work.Spaces.HkIntegrand α 6 f z θ ≤ (1 / (1 + z) ^ 2) * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + B * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) : Work.Spaces.HkSq α 6 f ≤ 2 * (A * 10 ^ 4 + B * 700) := by
  -- Integrability of the two angular profiles on `Iθ`.
  have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).1
  have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.Spaces.integrableOn_angular_weight' hα hα1
  -- The uniform angular integral bound.
  have hAng : (∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + B * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))))
      ≤ A * 10 ^ 4 + B * 700 :=
    Work.Elliptic.WtoH_Angular (α := α) hα hα1 hA hB
  -- The `θ`-slices of the `ℋ⁶`-integrand.
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ (1 / (1 + z) ^ 2) * (A * 10 ^ 4 + B * 700) := by
    intro z hz
    have hmaj : Integrable (fun θ : ℝ => (1 / (1 + z) ^ 2)
        * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + B * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hS1.const_mul A).add (hS2.const_mul B)).const_mul (1 / (1 + z) ^ 2)
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 6 f z θ ≤ (1 / (1 + z) ^ 2)
          * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + B * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
      ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (1 / (1 + z) ^ 2)
            * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + B * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ) hmaj hae
      _ = (1 / (1 + z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + B * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (1 / (1 + z) ^ 2) * (A * 10 ^ 4 + B * 700) :=
          mul_le_mul_of_nonneg_left hAng (by positivity)
  -- The radial integral.
  set K : ℝ := A * 10 ^ 4 + B * 700 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; nlinarith [hA, hB]
  have hI : IntegrableOn (fun z : ℝ => (1 / (1 + z) ^ 2) * K) Work.Spaces.Iz :=
    Work.Elliptic.WtoH_IntZ.1.mul_const K
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f z θ) ≤ 2 * K := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) * K :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
            hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
              simpa only [hKdef] using hinner z hz))
      _ = (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) * K := by
          rw [MeasureTheory.integral_mul_const]
      _ ≤ 2 * K := mul_le_mul_of_nonneg_right Work.Elliptic.WtoH_IntZ.2 hKnn
  change (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ) ≤ 2 * (A * 10 ^ 4 + B * 700)
  rw [← hKdef]
  exact houter

end Work.FTS.StrongPersist.AK6
