import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped Real Topology

namespace Commons.NumberTheory.DirichletCharacter

/-- For `z = (x : ℂ) + Complex.I * (T : ℂ) - u` the square of the norm splits as the
sum of the squares of the real and imaginary parts. -/
private lemma normSq_diff_eq {x T : ℝ} {u : ℂ} :
    ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ ^ 2 = (x - u.re) ^ 2 + (T - u.im) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply]
  simp
  ring

/-- Under `T ≠ u.im` the point `(x : ℂ) + Complex.I * (T : ℂ)` never meets `u`, so
the distance to `u` is strictly positive. -/
private lemma normSq_diff_pos {x T : ℝ} {u : ℂ} (hT : T ≠ u.im) :
    0 < ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ := by
  have hd0 : T - u.im ≠ 0 := sub_ne_zero.mpr hT
  have hz_ne : ((x : ℂ) + Complex.I * (T : ℂ)) - u ≠ 0 := by
    intro hz
    have him : (((x : ℂ) + Complex.I * (T : ℂ)) - u).im = T - u.im := by simp
    have h0 : (((x : ℂ) + Complex.I * (T : ℂ)) - u).im = 0 := by simp [hz]
    exact hd0 (by simpa [him] using h0)
  have hnz : ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
  exact lt_of_le_of_ne' (norm_nonneg _) hnz

/-- **Pointwise bound for the pole term.**  For every real `x` (a fortiori every
`x ∈ [0, 2]`)

`(2 - x) / (|x + iT - u| · |2 + iT - u|) ≤ 1 / |T - u.im|`

whenever `T ≠ u.im`.  Indeed the difference of the squares is a perfect square:

`|x + iT - u|² · |2 + iT - u|² − (2 − x)² (T − u.im)² = ((2 − u.re)(x − u.re) + (T − u.im)²)² ≥ 0`. -/
private lemma polePointwise_le {T : ℝ} {u : ℂ} (hT : T ≠ u.im) (x : ℝ) :
    (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖) ≤
      1 / |T - u.im| := by
  let A := ‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖
  let B := ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖
  have hA2 : A ^ 2 = (x - u.re) ^ 2 + (T - u.im) ^ 2 := by
    dsimp [A]
    exact normSq_diff_eq (x := x) (T := T) (u := u)
  have hB2 : B ^ 2 = (2 - u.re) ^ 2 + (T - u.im) ^ 2 := by
    dsimp [B]
    exact normSq_diff_eq (x := 2) (T := T) (u := u)
  have hsq2 : (2 - x) ^ 2 * (T - u.im) ^ 2 ≤ A ^ 2 * B ^ 2 := by
    rw [hA2, hB2]
    have hdiff : (((x - u.re) ^ 2 + (T - u.im) ^ 2) * ((2 - u.re) ^ 2 + (T - u.im) ^ 2)) -
        (2 - x) ^ 2 * (T - u.im) ^ 2 =
        ((2 - u.re) * (x - u.re) + (T - u.im) ^ 2) ^ 2 := by ring
    have hsq_nonneg : 0 ≤ ((2 - u.re) * (x - u.re) + (T - u.im) ^ 2) ^ 2 := sq_nonneg _
    nlinarith
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hprod : (2 - x) * |T - u.im| ≤ A * B := by
    apply le_of_sq_le_sq _ (mul_nonneg hA0 hB0)
    calc ((2 - x) * |T - u.im|) ^ 2 = (2 - x) ^ 2 * |T - u.im| ^ 2 := by ring
      _ = (2 - x) ^ 2 * (T - u.im) ^ 2 := by rw [sq_abs]
      _ ≤ (A * B) ^ 2 := by
        calc (2 - x) ^ 2 * (T - u.im) ^ 2 ≤ A ^ 2 * B ^ 2 := hsq2
          _ = (A * B) ^ 2 := by ring
  have hApos : 0 < A := by
    dsimp [A]
    exact normSq_diff_pos (x := x) (T := T) (u := u) hT
  have hBpos : 0 < B := by
    dsimp [B]
    exact normSq_diff_pos (x := 2) (T := T) (u := u) hT
  have hdabs : 0 < |T - u.im| := abs_pos.mpr (sub_ne_zero.mpr hT)
  exact (div_le_div_iff₀ (mul_pos hApos hBpos) hdabs).2 (by simpa using hprod)

/-- The pole-term integrand is continuous everywhere: the denominator vanishes only at
`u`, which is never met since `T ≠ u.im`. -/
private lemma integrand_cont {T : ℝ} {u : ℂ} (hT : T ≠ u.im) :
    Continuous (fun x : ℝ =>
      (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)) := by
  refine Continuous.div₀ ?hf ?hg ?h0
  · fun_prop
  · fun_prop
  · intro x
    apply mul_ne_zero
    · have hz : ((x : ℂ) + Complex.I * (T : ℂ)) - u ≠ 0 := by
        intro hz
        have him : (((x : ℂ) + Complex.I * (T : ℂ)) - u).im = T - u.im := by simp
        have h0 : (((x : ℂ) + Complex.I * (T : ℂ)) - u).im = 0 := by simp [hz]
        exact (sub_ne_zero.mpr hT) (by simpa [him] using h0)
      exact norm_ne_zero_iff.mpr hz
    · have hz2 : ((2 : ℂ) + Complex.I * (T : ℂ)) - u ≠ 0 := by
        intro hz
        have him : (((2 : ℂ) + Complex.I * (T : ℂ)) - u).im = T - u.im := by simp
        have h0 : (((2 : ℂ) + Complex.I * (T : ℂ)) - u).im = 0 := by simp [hz]
        exact (sub_ne_zero.mpr hT) (by simpa [him] using h0)
      exact norm_ne_zero_iff.mpr hz2

/-- **Integral bound for the pole contribution on `[0, 2]`.**

The pointwise inequality `polePointwise_le` (integrand `≤ 1/|T - u.im|` on `[0,2]`)
integrates over the interval of length two to give

`∫ x in 0..2, (2 - x) / (|x + iT - u| · |2 + iT - u|) dx ≤ 2 / |T - u.im|`.

The hypothesis `u.re < 1` (a pole lying to the left of the segment's midpoint) is
part of the statement but is not needed for the estimate. -/
theorem poleXIntegral_le {T : ℝ} {u : ℂ} (hu1 : u.re < 1) (hT : T ≠ u.im) :
    (∫ x : ℝ in 0..2,
        (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)) ≤
      2 / |T - u.im| := by
  have _ : u.re < 1 := hu1
  let c : ℝ := 1 / |T - u.im|
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) (2 : ℝ),
      (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖) ≤ c := by
    intro x hx
    exact polePointwise_le hT x
  have hcont : Continuous (fun x : ℝ =>
      (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)) :=
    integrand_cont hT
  have hF_int : IntervalIntegrable (fun x : ℝ =>
      (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)) volume 0 2 :=
    hcont.intervalIntegrable 0 2
  have hc_int : IntervalIntegrable (fun _ : ℝ => c) volume 0 2 :=
    (continuous_const.intervalIntegrable 0 2)
  have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := (2 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 2) hF_int hc_int hpt
  calc
    (∫ x : ℝ in 0..2,
        (2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖)) ≤
        ∫ x : ℝ in 0..2, c := hmono
    _ = 2 * c := by
      rw [intervalIntegral.integral_const]
      norm_num
    _ = 2 / |T - u.im| := by
      dsimp [c]
      ring

end Commons.NumberTheory.DirichletCharacter