import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two Cauchy–Schwarz steps

The proof is Cauchy–Schwarz twice: on each angular slice `θ ↦ ·` (where the weight `w2 z * sig θ`
is only known to make the *products* `g²`, `h²`, `g h` integrable — nothing is known about the
measurability of the slices themselves), and then in the radial variable `z`.

The slice step is `Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le`: the weighted
Cauchy–Schwarz for the *products*, i.e. the discriminant argument for
`t ↦ ∫_θ (g z θ - t h z θ)² w2 z σ θ ≥ 0`, which needs only the integrability of the three
weighted products.  The radial step is
`Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt`, the ordinary Cauchy–Schwarz
in `z` applied to `z ↦ √(∫_θ g² w²σ)` and `z ↦ √(∫_θ h² w²σ)`. -/

/-- **Cauchy–Schwarz for the angular-weight pairing** (namespace `Work.FTS.EllipticEst.AngSecond`).

For `g h : ℝ → ℝ → ℝ` whose pairings `IP g g`, `IP h h`, `IP g h` are honest (integrand
integrable, slicewise in `θ` and then in `z`),

  `|IP g h| ≤ √(IP g g) · √(IP h h)`,

where `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ`, `w z = (1+z)²/z²`, `σ θ = sin(2θ)^{-η}`.
Since `IP u u = L2Sq (u · W)` with `W = w/sin(2θ)^{η/2}` (`L2Sq_mul_W`), this is Cauchy–Schwarz in
the weighted `L²` space, in iterated form.

Route: write `A z = ∫_θ g² w²σ`, `B z = ∫_θ h² w²σ`, `C z = ∫_θ g h w²σ`, so that `IP g g`,
`IP h h`, `IP g h` are the `z`-integrals of `A`, `B`, `C`.  The slicewise inequality
`C z² ≤ A z · B z` is `slice_sq_integral_mul_le` with `F = g z`, `G = h z`, `κ = w²σ` (the weight
enters only through the three integrability hypotheses, which `IPMem` supplies); it gives
`|C z| = √(C z²) ≤ √(A z)·√(B z)` because `A z ≥ 0`.  The `z`-integral is then handled by
`abs_setIntegral_le_sqrt_mul_sqrt`. -/
theorem IP_cauchy_schwarz {g h : ℝ → ℝ → ℝ} (hgg : IPMem g g) (hhh : IPMem h h)
    (hgh : IPMem g h) :
    |IP g h| ≤ Real.sqrt (IP g g) * Real.sqrt (IP h h) := by
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ with hAdef
  set B : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, h z θ * h z θ * w2 z * sig θ with hBdef
  set C : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ with hCdef
  have hAgg : IntegrableOn A Work.Spaces.Iz := by rw [hAdef]; exact hgg.2
  have hBgg : IntegrableOn B Work.Spaces.Iz := by rw [hBdef]; exact hhh.2
  have hCgg : IntegrableOn C Work.Spaces.Iz := by rw [hCdef]; exact hgh.2
  have hAz_nonneg : ∀ z ∈ Work.Spaces.Iz, 0 ≤ A z := by
    intro z _
    rw [hAdef]
    refine setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (mul_self_nonneg (g z θ)) (w2_nonneg z)) (sig_nonneg hθ)
  have hBz_nonneg : ∀ z ∈ Work.Spaces.Iz, 0 ≤ B z := by
    intro z _
    rw [hBdef]
    refine setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (mul_self_nonneg (h z θ)) (w2_nonneg z)) (sig_nonneg hθ)
  have hslice : ∀ z ∈ Work.Spaces.Iz, |C z| ≤ Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z hz
    have hκ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (fun θ => w2 z * sig θ) θ :=
      fun θ hθ => mul_nonneg (w2_nonneg z) (sig_nonneg hθ)
    have hF : IntegrableOn (fun θ => g z θ * g z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hgg.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    have hG : IntegrableOn (fun θ => h z θ * h z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hhh.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    have hFG : IntegrableOn (fun θ => g z θ * h z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hgh.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    have hcs := slice_sq_integral_mul_le (s := Work.Spaces.Iθ)
      (F := fun θ => g z θ) (G := fun θ => h z θ) (κ := fun θ => w2 z * sig θ) hκ hF hG hFG
    have hCeq : C z = ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * (w2 z * sig θ) := by
      rw [hCdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hAeq : A z = ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * (w2 z * sig θ) := by
      rw [hAdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hBeq : B z = ∫ θ in Work.Spaces.Iθ, h z θ * h z θ * (w2 z * sig θ) := by
      rw [hBdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hC2 : C z ^ 2 ≤ A z * B z := by
      rw [hCeq, hAeq, hBeq]
      exact hcs
    calc |C z| = Real.sqrt ((C z) ^ 2) := (Real.sqrt_sq_eq_abs (C z)).symm
      _ ≤ Real.sqrt (A z * B z) := Real.sqrt_le_sqrt hC2
      _ = Real.sqrt (A z) * Real.sqrt (B z) := Real.sqrt_mul (hAz_nonneg z hz) (B z)
  change |∫ z in Work.Spaces.Iz, C z|
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, A z) * Real.sqrt (∫ z in Work.Spaces.Iz, B z)
  exact abs_setIntegral_le_sqrt_mul_sqrt hAgg hBgg hCgg hAz_nonneg hBz_nonneg hslice

end Work.FTS.EllipticEst.AngSecond
