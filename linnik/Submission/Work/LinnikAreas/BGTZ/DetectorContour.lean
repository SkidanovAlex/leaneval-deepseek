/-
# `Work.LinnikAreas.BGTZ.DetectorContour`

The decomposition `‖detector‖ ≤ detResBound + ‖detJ‖` of the BGTZ zero detector
(`Paper/bgtz.txt`, proof of Proposition 5.1): the smoothed sum `detector` equals the contour
integral `detJ` on the critical line plus the residue of the shifted integrand at `s = 1 - ρ`,
and that residue is bounded by `detResBound`.

The pieces are proved in the companion modules: `DetectorContourCore` (algebraic/analytic core,
including the summability of the detector's Dirichlet series), `DetPerronFormula` (smoothed Perron
formula), `DetSeriesIdentity` (Euler product), `DetIntBound`, `DetContourShift` (vertical contour
shift across the pole), `DetResNormLe`, `DetTrivCharValue`, `DetSieveLocalTriv`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs
import Submission.Work.LinnikAreas.BGTZ.RatioLone
import Submission.Work.Sieve.LFunction_critical_line_bound
import Submission.Work.LinnikAreas.BGTZ.DetContourDefs
import Submission.Work.LinnikAreas.BGTZ.DetectorContourCore
import Submission.Work.LinnikAreas.BGTZ.DetPerronFormulaCore
import Submission.Work.LinnikAreas.BGTZ.DetSeriesIdentity
import Submission.Work.LinnikAreas.BGTZ.DetIntBound
import Submission.Work.LinnikAreas.BGTZ.DetResNormLe
import Submission.Work.LinnikAreas.BGTZ.DetTrivCharValue
import Submission.Work.LinnikAreas.BGTZ.DetSieveLocalTriv

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- **The Perron representation of the detector sum**: with the Perron line `Re s = 2`,
`detector` is the integral of `detInt` against `dt/(2π)`. -/
lemma detector_eq_integral {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {R : ℕ} {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {ρ : ℂ} (hre : 1 / 2 < ρ.re)
    {N : ℕ} (hN : 1 ≤ N) :
    detector χ₁ χ N θw ρ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ,
          detInt χ₁ χ R θw N ρ ((2 : ℝ) + (t : ℂ) * Complex.I) := by
  have hconv : Summable (fun n : ℕ => ‖detCoeff χ₁ χ θw n‖ / (n : ℝ) ^ (2 + ρ.re)) :=
    detCoeff_summable χ₁ χ hχ₁ hθ hre
  have hperron := detPerronFormula (f := detCoeff χ₁ χ θw) (c := 2) (by norm_num) hN ρ hconv
  have hseries : ∀ t : ℝ,
      (∑' n : ℕ, detCoeff χ₁ χ θw n / (n : ℂ) ^ (ρ + ((2 : ℝ) + (t : ℂ) * Complex.I)))
        = DirichletCharacter.LFunction χ (ρ + ((2 : ℝ) + (t : ℂ) * Complex.I))
          * DirichletCharacter.LFunction (χ * χ₁) (ρ + ((2 : ℝ) + (t : ℂ) * Complex.I))
          * sieveG χ₁ R θw (ρ + ((2 : ℝ) + (t : ℂ) * Complex.I)) χ := by
    intro t
    refine DetSeriesIdentity χ₁ χ hχ₁ hθ ?_
    have hre' : (ρ + ((2 : ℝ) + (t : ℂ) * Complex.I)).re = 2 + ρ.re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      ring
    rw [hre']
    linarith
  have hint_eq : (1 / (2 * Real.pi)) * ∫ t : ℝ,
        (∑' n : ℕ, detCoeff χ₁ χ θw n / (n : ℂ) ^ (ρ + ((2 : ℝ) + (t : ℂ) * Complex.I)))
          * (N : ℂ) ^ ((2 : ℝ) + (t : ℂ) * Complex.I)
          / (((2 : ℝ) + (t : ℂ) * Complex.I) * ((2 : ℝ) + 1 + (t : ℂ) * Complex.I))
      = (1 / (2 * Real.pi)) * ∫ t : ℝ,
          detInt χ₁ χ R θw N ρ ((2 : ℝ) + (t : ℂ) * Complex.I) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (.of_forall fun t => ?_)
    simp only [hseries t, detInt, detNum]
    ring
  have hdet : detector χ₁ χ N θw ρ
      = ∑ n ∈ Finset.Icc 1 N,
          detCoeff χ₁ χ θw n * (n : ℂ) ^ (-ρ) * (1 - (n : ℂ) / (N : ℂ)) := by
    unfold detector detCoeff
    refine Finset.sum_congr rfl fun n hn => ?_
    ring
  rw [hdet, ← hperron, hint_eq]

/-- **The contour shift of the detector**: `detector = detJ + detRes`. -/
lemma detector_eq_detJ_add_detRes {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ₁ χ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₁ne : χ₁ ≠ 1) {R : ℕ} {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0
      ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hre : 1 / 2 < ρ.re) (hρre : ρ.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    detector χ₁ χ N θw ρ = detJ χ₁ χ R θw N ρ + detRes χ₁ χ R θw N ρ := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρre
    norm_num at hρre
  have hρ2 : ρ.re < 2 := by linarith
  have hρ0 : 0 < ρ.re := by linarith
  have hc0 : (1 / 2 : ℝ) - ρ.re ≠ 0 := by
    intro h
    linarith [hre]
  have hcm : (1 / 2 : ℝ) - ρ.re ≠ -1 := by
    intro h
    linarith [hre]
  have hc1 : (1 / 2 : ℝ) - ρ.re + ρ.re ≠ 1 := by norm_num
  have hc2 : (2 : ℝ) + ρ.re ≠ 1 := by linarith
  have hc1u : (1 / 2 : ℝ) - ρ.re ≠ 1 - ρ.re := by
    intro h
    linarith
  have hc2u : (2 : ℝ) ≠ 1 - ρ.re := by
    intro h
    linarith
  have hp1 : (-1 : ℝ) < 1 / 2 - ρ.re := by linarith
  have hNc : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
  obtain ⟨C, A, hCpos, hAneg, hbd1, hbd2, hbd3⟩ :=
    DetIntBound (q := q) hq χ₁ χ R θw N hN ρ hre hρre
  have hint1 : MeasureTheory.Integrable
      (fun t : ℝ => detInt χ₁ χ R θw N ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)) :=
    integrable_detInt_of_bound χ₁ χ R θw N ρ hNc hc0 hcm hc1 hAneg hCpos hbd1
  have hint2 : MeasureTheory.Integrable
      (fun t : ℝ => detInt χ₁ χ R θw N ρ ((2 : ℝ) + (t : ℂ) * Complex.I)) :=
    integrable_detInt_of_bound χ₁ χ R θw N ρ hNc (by norm_num) (by norm_num) hc2
      hAneg hCpos hbd2
  obtain ⟨htop, hbot⟩ := tendsto_detH_horizontal χ₁ χ R θw N ρ hzero hρ1 hρ0
    (by linarith : A < 0) hCpos hbd3
  have hshift := detContourShift (fun s => detInt χ₁ χ R θw N ρ s) (fun s => detH χ₁ χ R θw N ρ s)
    (1 / 2 - ρ.re) 2 (by linarith) (1 - ρ) (detRes χ₁ χ R θw N ρ)
    ⟨by simp only [Complex.sub_re, Complex.one_re]; linarith,
      by simp only [Complex.sub_re, Complex.one_re]; linarith⟩
    (fun R' => differentiableOn_detH χ₁ χ R θw N ρ hχ₁ hχ₁ne hNc hρ2 hp1 (by norm_num))
    (Filter.Eventually.of_forall fun t => detH_eq_line χ₁ χ R θw N ρ hzero hρ1 hc0 hcm hc1u)
    (Filter.Eventually.of_forall fun t => detH_eq_line χ₁ χ R θw N ρ hzero hρ1
      (by norm_num) (by norm_num) hc2u)
    htop hbot hint1 hint2
  have hper := detector_eq_integral (q := q) χ₁ χ hχ₁ (θw := θw) (R := R) hθ hre hN
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hkey : (1 / (2 * Real.pi)) * (2 * Real.pi * detRes χ₁ χ R θw N ρ)
      = detRes χ₁ χ R θw N ρ := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hpi, one_mul]
  rw [hper, detJ_eq_integral, hshift, mul_add, hkey]
  simp only [detLine]

theorem DetectorContour {q : ℕ} [NeZero q] (hq : 400000 < q) (χ₁ χ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₁ne : χ₁ ≠ 1) {β₁ : ℝ} (hβ₁ : β₁ < 1)
    (hzm : Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0)
    (hβ₁' : 1 - 1 / (10 * Real.log q) < β₁)
    {A θ Cz : ℝ} (hA : HypA A θ) (hZ : HypZeta Cz) {R : ℕ} (hR : 200 ≤ R)
    {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw)
    (T : ℝ) (hT : 4 ≤ T) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0 ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0)
    (hre : 1 / 2 < ρ.re) (him : |ρ.im| ≤ T) {N : ℕ} (hN : 1 ≤ N) :
    ‖detector χ₁ χ N θw ρ‖ ≤ detResBound χ₁ χ R θw N ρ + ‖detJ χ₁ χ R θw N ρ‖ := by
  have hq2 : 2 ≤ q := by omega
  have hρre : ρ.re < 1 := det_rho_re_lt_one hq χ₁ χ hχ₁ne hzero hre
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρre
    norm_num at hρre
  have hmain := detector_eq_detJ_add_detRes hq2 χ₁ χ hχ₁ hχ₁ne (θw := θw) hθ hzero hre hρre hN
  have hres := DetResNormLe (R := R) χ₁ χ hχ₁ hχ₁ne θw hN hzero hρ1 hρre
  calc ‖detector χ₁ χ N θw ρ‖
      = ‖detJ χ₁ χ R θw N ρ + detRes χ₁ χ R θw N ρ‖ := by rw [hmain]
    _ ≤ ‖detJ χ₁ χ R θw N ρ‖ + ‖detRes χ₁ χ R θw N ρ‖ := norm_add_le _ _
    _ ≤ ‖detJ χ₁ χ R θw N ρ‖ + detResBound χ₁ χ R θw N ρ := by linarith
    _ = detResBound χ₁ χ R θw N ρ + ‖detJ χ₁ χ R θw N ρ‖ := by ring

end Work.LinnikAreas.BGTZ
