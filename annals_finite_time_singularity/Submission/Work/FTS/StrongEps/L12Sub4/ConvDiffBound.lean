import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.L12Sub4.KernelWeightSub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

open MeasureTheory

/-- **Pointwise-in-`ζ` size of the mollifier error.**  Same hypotheses as `KernelWeightSub`, but the
conclusion is stated directly for the integral of the *difference* integrand
`p ↦ k p * (G (ζ + p.2) - G ζ)`: no rewrite of that integral as a difference of integrals (which
would need the integrability of `p ↦ k p * G (ζ + p.2)`) is required. -/
private lemma conv_diff_inner {k : ℝ × ℝ → ℝ} {G : ℝ → ℝ} {ε B : ℝ}
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ ε)
    (hB : 0 ≤ B)
    (hGdiff : ∀ ζ q : ℝ, |q| ≤ 1 → |G (ζ + q) - G ζ| ≤ B * |q| * G ζ)
    (hε1 : ε ≤ 1) :
    ∀ ζ : ℝ, |∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)| ≤ B * ε * G ζ := by
  intro ζ
  by_cases hB0 : B = 0
  · -- `B = 0`: `G` is constant on `[ζ-1, ζ+1]`, hence the integrand vanishes identically.
    have hzero : ∀ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ) = 0 := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul]
      · have hp2 : |p.2| ≤ 1 := le_trans (hksupp p hp) hε1
        have h2 : |G (ζ + p.2) - G ζ| ≤ 0 := by simpa [hB0] using hGdiff ζ p.2 hp2
        have h3 : G (ζ + p.2) - G ζ = 0 :=
          abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _))
        rw [h3, mul_zero]
    have hI : (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) = 0 := by
      rw [show (fun p : ℝ × ℝ => k p * (G (ζ + p.2) - G ζ)) = (fun _ => (0 : ℝ)) from
        funext hzero, integral_zero]
    rw [hI]
    simp [hB0]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    -- The oscillation hypothesis forces `G ζ ≥ 0` (evaluate at `q = 1/2`).
    have hGζ : 0 ≤ G ζ := by
      have h := hGdiff ζ (1 / 2) (by norm_num)
      have h1 : |(1 : ℝ) / 2| = (1 : ℝ) / 2 := by norm_num
      rw [h1] at h
      exact nonneg_of_mul_nonneg_right (le_trans (abs_nonneg _) h)
        (mul_pos hBpos (by norm_num))
    -- Pointwise domination of the difference integrand on the support of `k`.
    have hpt : ∀ p : ℝ × ℝ, k p * |G (ζ + p.2) - G ζ| ≤ (B * ε * G ζ) * k p := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul, mul_zero]
      · have hp2 : |p.2| ≤ ε := hksupp p hp
        have hp2' : |p.2| ≤ 1 := le_trans hp2 hε1
        have h1 : |G (ζ + p.2) - G ζ| ≤ B * |p.2| * G ζ := hGdiff ζ p.2 hp2'
        have h2 : B * |p.2| * G ζ ≤ B * ε * G ζ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hB) hGζ
        have h3 : |G (ζ + p.2) - G ζ| ≤ B * ε * G ζ := le_trans h1 h2
        calc k p * |G (ζ + p.2) - G ζ| ≤ k p * (B * ε * G ζ) :=
              mul_le_mul_of_nonneg_left h3 (hknn p)
          _ = (B * ε * G ζ) * k p := by ring
    have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => (B * ε * G ζ) * k p) :=
      hki.const_mul _
    calc |∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)|
        ≤ ∫ p : ℝ × ℝ, |k p * (G (ζ + p.2) - G ζ)| := abs_integral_le_integral_abs
      _ = ∫ p : ℝ × ℝ, k p * |G (ζ + p.2) - G ζ| := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            change |k p * (G (ζ + p.2) - G ζ)| = k p * |G (ζ + p.2) - G ζ|
            rw [abs_mul, abs_of_nonneg (hknn p)]
      _ ≤ ∫ p : ℝ × ℝ, (B * ε * G ζ) * k p := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun p => mul_nonneg (hknn p) (abs_nonneg _)) hInt
              (Filter.Eventually.of_forall hpt)
      _ = B * ε * G ζ := by rw [MeasureTheory.integral_const_mul, hk1, mul_one]

/-- **The outer integral step.**  If a plane function `A` is pointwise dominated by `B ε G(·.2)` and
`x ↦ G x.2 * |F x.1 x.2|` is integrable, then
`|∫_x A x · F x.1 x.2| ≤ B ε ∫_x G x.2 · |F x.1 x.2|`. -/
private lemma plane_le_of_pointwise {A : ℝ × ℝ → ℝ} {G : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {ε B : ℝ}
    (hA : ∀ x : ℝ × ℝ, |A x| ≤ B * ε * G x.2)
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    |∫ x : ℝ × ℝ, A x * F x.1 x.2| ≤ B * ε * (∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|) := by
  have h1 : |∫ x : ℝ × ℝ, A x * F x.1 x.2| ≤ ∫ x : ℝ × ℝ, |A x * F x.1 x.2| :=
    abs_integral_le_integral_abs
  have h2 : ∫ x : ℝ × ℝ, |A x * F x.1 x.2|
      ≤ ∫ x : ℝ × ℝ, (B * ε) * (G x.2 * |F x.1 x.2|) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => abs_nonneg _) (hFint.const_mul (B * ε))
      (Filter.Eventually.of_forall fun x => ?_)
    change |A x * F x.1 x.2| ≤ (B * ε) * (G x.2 * |F x.1 x.2|)
    rw [abs_mul]
    calc |A x| * |F x.1 x.2| ≤ (B * ε * G x.2) * |F x.1 x.2| :=
          mul_le_mul_of_nonneg_right (hA x) (abs_nonneg _)
      _ = (B * ε) * (G x.2 * |F x.1 x.2|) := by ring
  have h3 : ∫ x : ℝ × ℝ, (B * ε) * (G x.2 * |F x.1 x.2|)
      = B * ε * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2| := by
    rw [MeasureTheory.integral_const_mul]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-- **The `ε`-size of the mollifier error in the weight-adjoint form** (generic).  Under the
hypotheses of `KernelWeightSub` (nonnegative integrable kernel `k` of mass `1` supported in the strip
`|p₂| ≤ ε ≤ 1`, continuous weight `G` with `|G (ζ+q) - G ζ| ≤ B|q| G ζ` for `|q| ≤ 1`) and with
`x ↦ G x.2 · |F x.1 x.2|` integrable,

  `|∫_x (∫_p k p · (G (x.2+p.2) - G x.2)) · F x.1 x.2| ≤ B ε ∫_x G x.2 · |F x.1 x.2|`

(integrals over the plane).

Hints: the pointwise-in-`ζ` bound `|∫ p, k p * (G (ζ+p.2) - G ζ)| ≤ B ε G ζ` is
`KernelWeightSub` (`FTS/StrongEps/L12Sub4/KernelWeightSub`, already proved, importable) after the
rewrite `∫ p, k p (G(ζ+p.2) - Gζ) = (∫ p, k p G(ζ+p.2)) - Gζ` (`MeasureTheory.integral_sub` +
`MeasureTheory.integral_mul_const` + `hk1`); alternatively prove it directly with
`MeasureTheory.norm_integral_le_integral_norm`, `MeasureTheory.integral_mono_of_nonneg` and
`∫ p, k p * |p.2| ≤ ε`.  Then specialise at `ζ = x.2`, use
`MeasureTheory.norm_integral_le_integral_norm` for the outer integral, and
`MeasureTheory.integral_mono_of_nonneg` against the integrable majorant
`B ε (G x.2 * |F x.1 x.2|)` (`hFint.const_mul`), finishing with
`MeasureTheory.integral_const_mul`.  No measurability of the parametric integral
`x ↦ ∫ p, k p (G (x.2+p.2) - G x.2)` is needed for these steps. -/
theorem ConvDiffBound (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ) {ε B : ℝ}
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ ε)
    (hGcont : Continuous G) (hB : 0 ≤ B)
    (hGdiff : ∀ ζ q : ℝ, |q| ≤ 1 → |G (ζ + q) - G ζ| ≤ B * |q| * G ζ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    |∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2|
      ≤ B * ε * (∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|) := by
  have hA : ∀ x : ℝ × ℝ, |(∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2))| ≤ B * ε * G x.2 :=
    fun x => conv_diff_inner hknn hki hk1 hksupp hB hGdiff hε1 x.2
  exact plane_le_of_pointwise
    (A := fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) hA hFint

end Work.FTS.StrongEps.L12Sub4
