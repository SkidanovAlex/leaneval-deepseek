import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseBoxFock.fourierSample_scaling
import Submission.Work.BoseBoxFock.poissonEuclid3Summable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

/-!
# `Work.BoseBoxFock.LatSym.poisson_scaled_general`

Poisson summation on `ℝ³` for the momentum lattice `(2π/ℓ)ℤ³` (`kmomInt ℓ n = (2π/ℓ) • latVec n`),
in the form

  `∑'_n f (kmomInt ℓ n) = (ℓ/(2π))³ * ∑'_m ∫ p, f p * exp (-(I ⟪ℓ • latVec m, p⟫))`.

## Route

Apply `Work.BoseBoxFock.poissonEuclid3Summable` (already proved: for `F` continuous with `(1+‖x‖)⁴`
decay and summable Fourier samples it gives
`∑'_m F (latVec m) = ∑'_m ∫ x, F x * exp (-(2π I ⟪x, latVec m⟫))`) to
`F := fun y => f ((2π/ℓ) • y)`.

* Left side: `F (latVec n) = f ((2π/ℓ) • latVec n) = f (kmomInt ℓ n)`
  (`Submission.Work.BoseBoxFock.KinRowQuant`'s `kmomInt`; `(2π/ℓ) • latVec n = kmomInt ℓ n` is
  `Work.BoseBoxFock.kmomInt_eq_smul_latVec` in `BoseBoxFock/kinFT_fold_const.lean`, also in
  `BoseBoxFock/kernelAliasing_smooth.lean`, or `latMinus_smul_latVec_eq_kmomInt` in
  `BoseBoxFock/latMinusCont_image.lean`).
* Right side: `∫ x, F x * exp (-(2π I ⟪x, latVec m⟫)) = (ℓ/(2π))³ ∫ p, f p * exp (-(I ⟪ℓ • latVec m, p⟫))`
  which is exactly `Work.BoseBoxFock.fourierSample_scaling hℓ f (latVec m)`.
* The decay hypothesis `(1+‖y‖)⁴ * ‖F y‖ ≤ C` follows from `hfdec` (absorb `(1+ℓ/2π)⁴`), and the
  summability hypothesis transfers termwise by the same `fourierSample_scaling` identity (up to the
  constant `(ℓ/(2π))³`, using `hsum.mul_left`/`Summable.congr`).
-/

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The scaled integer lattice vector `(2π/ℓ) • latVec n` is the lattice momentum `kmomInt ℓ n`
(this is `Work.BoseBoxFock.kmomInt_eq_smul_latVec` written in the opposite direction, reproved here
from the definitions so that the module needs no extra import). -/
lemma smul_latVec_eq_kmomInt (ℓ : ℝ) (n : Fin 3 → ℤ) :
    (2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec n = Work.BoseBoxFock.kmomInt ℓ n := by
  rw [Work.BoseBoxFock.kmomInt, Work.BoseB4.vec, Work.BoseBoxFock.latVec]
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply]
  ring

/-- **Decay transfer under dilation.**  If `(1 + ‖p‖)⁴ ‖f p‖ ≤ C` for all `p`, then
`(1 + ‖y‖)⁴ ‖f (a • y)‖ ≤ (max 1 a⁻¹)⁴ C` for all `y` (and `a > 0`).

Indeed `1 + ‖y‖ ≤ max 1 a⁻¹ · (1 + ‖a • y‖)` because `‖a • y‖ = a ‖y‖`, `max 1 a⁻¹ ≥ 1` and
`max 1 a⁻¹ · a ≥ 1`. -/
lemma decay_comp_smul {f : E3 → ℂ} {a : ℝ} (ha : 0 < a) {C : ℝ}
    (hC : ∀ p : E3, (1 + ‖p‖) ^ 4 * ‖f p‖ ≤ C) (y : E3) :
    (1 + ‖y‖) ^ 4 * ‖f (a • y)‖ ≤ (max 1 a⁻¹) ^ 4 * C := by
  have hnorm : ∀ y : E3, ‖a • y‖ = a * ‖y‖ := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg ha.le]
  have hK1 : (1 : ℝ) ≤ max 1 a⁻¹ := le_max_left _ _
  have hKa : 1 ≤ max 1 a⁻¹ * a := by
    have h := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) a⁻¹) ha.le
    rwa [inv_mul_cancel₀ (ne_of_gt ha)] at h
  have hle : ∀ y : E3, 1 + ‖y‖ ≤ max 1 a⁻¹ * (1 + ‖a • y‖) := by
    intro y
    rw [hnorm y]
    have hmul : ‖y‖ ≤ max 1 a⁻¹ * a * ‖y‖ := by
      calc ‖y‖ = 1 * ‖y‖ := by ring
        _ ≤ (max 1 a⁻¹ * a) * ‖y‖ := mul_le_mul_of_nonneg_right hKa (norm_nonneg y)
    calc 1 + ‖y‖ ≤ max 1 a⁻¹ + max 1 a⁻¹ * a * ‖y‖ := add_le_add hK1 hmul
      _ = max 1 a⁻¹ * (1 + a * ‖y‖) := by ring
  have h4 : (1 + ‖y‖) ^ 4 ≤ (max 1 a⁻¹) ^ 4 * (1 + ‖a • y‖) ^ 4 := by
    have h2 : (1 + ‖y‖) ^ 4 ≤ (max 1 a⁻¹ * (1 + ‖a • y‖)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (hle y) 4
    rwa [mul_pow] at h2
  calc (1 + ‖y‖) ^ 4 * ‖f (a • y)‖
      ≤ ((max 1 a⁻¹) ^ 4 * (1 + ‖a • y‖) ^ 4) * ‖f (a • y)‖ :=
        mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
    _ = (max 1 a⁻¹) ^ 4 * ((1 + ‖a • y‖) ^ 4 * ‖f (a • y)‖) := by ring
    _ ≤ (max 1 a⁻¹) ^ 4 * C := mul_le_mul_of_nonneg_left (hC (a • y)) (by positivity)

theorem poisson_scaled_general {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : Continuous f) (hfdec : ∃ C : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3),
      (1 + ‖p‖) ^ 4 * ‖f p‖ ≤ C)
    (hsum : Summable (fun m : Fin 3 → ℤ => ∫ p : EuclideanSpace ℝ (Fin 3),
      f p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p : ℂ))))) :
    (∑' n : Fin 3 → ℤ, f (Work.BoseBoxFock.kmomInt ℓ n))
      = ((ℓ / (2 * Real.pi)) ^ 3) * ∑' m : Fin 3 → ℤ, ∫ p : EuclideanSpace ℝ (Fin 3),
          f p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p : ℂ))) := by
  have ha : 0 < 2 * Real.pi / ℓ := by positivity
  obtain ⟨C, hC⟩ := hfdec
  -- the decay hypothesis of `f` transfers to `y ↦ f ((2π/ℓ) • y)`
  have hdec : ∀ y : E3, (1 + ‖y‖) ^ 4 * ‖f ((2 * Real.pi / ℓ) • y)‖
      ≤ (max 1 (2 * Real.pi / ℓ)⁻¹) ^ 4 * C := fun y => decay_comp_smul ha hC y
  -- the (complex) scalar `(ℓ/2π)³`, written in the two forms that occur below
  have hcast : (((ℓ / (2 * Real.pi)) ^ 3 : ℝ) : ℂ) = (↑ℓ / (2 * ↑Real.pi)) ^ 3 := by
    push_cast
    ring
  -- the Fourier samples of the dilated function are summable, termwise by `fourierSample_scaling`
  have hsumF : Summable (fun m : Fin 3 → ℤ => ∫ x : E3,
      f ((2 * Real.pi / ℓ) • x) *
        Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m))))) := by
    refine (hsum.mul_left (((ℓ / (2 * Real.pi)) ^ 3 : ℝ) : ℂ)).congr (fun m => ?_)
    rw [fourierSample_scaling hℓ f (Work.BoseBoxFock.latVec m), hcast]
  have key := poissonEuclid3Summable (fun y : E3 => f ((2 * Real.pi / ℓ) • y))
    (hf.comp (continuous_const_smul _)) ⟨_, hdec⟩ hsumF
  calc (∑' n : Fin 3 → ℤ, f (Work.BoseBoxFock.kmomInt ℓ n))
      = ∑' n : Fin 3 → ℤ, f ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec n) := by
        refine tsum_congr fun n => ?_
        rw [smul_latVec_eq_kmomInt]
    _ = ∑' m : Fin 3 → ℤ, ∫ x : E3, f ((2 * Real.pi / ℓ) • x) *
          Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m)))) := key
    _ = ∑' m : Fin 3 → ℤ, ((ℓ / (2 * Real.pi)) ^ 3) * ∫ p : E3,
          f p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p : ℂ))) := by
        refine tsum_congr fun m => ?_
        exact fourierSample_scaling hℓ f (Work.BoseBoxFock.latVec m)
    _ = ((ℓ / (2 * Real.pi)) ^ 3) * ∑' m : Fin 3 → ℤ, ∫ p : E3,
          f p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p : ℂ))) :=
        tsum_mul_left

end Work.BoseBoxFock.LatSym
