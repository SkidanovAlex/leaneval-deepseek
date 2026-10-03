import Mathlib
import Submission.Work.Repel.gronwall_lower
import Submission.Work.Repel.logGronwall_factor

/-!
# Lower bound for `‖deriv g z‖` from a bound on the second derivative

If `g` is holomorphic on the unit disc and its second derivative is controlled by its first
derivative through

`‖deriv (deriv g) w‖ ≤ ((4 + 2‖w‖) / (1 - ‖w‖^2)) * ‖deriv g w‖`

then `deriv g` cannot drop by more than a factor `12` on the half-disc:

`(1/12) * ‖deriv g 0‖ ≤ ‖deriv g z‖` for `‖z‖ ≤ 1/2`.

The proof integrates the logarithmic derivative of `g'` along the segment from `0` to `z`
(the classical sharp form of the Koebe distortion lower bound).  Writing
`F t = deriv g (t z)` one has `‖F' t‖ ≤ r * ((4 + 2 t r)/(1 - (t r)^2)) * ‖F t‖` with `r = ‖z‖`,
so `y t = ‖F t‖^2` satisfies the reverse Grönwall inequality
`y' ≥ -(2 r ((4 + 2 t r)/(1 - (t r)^2))) * y`
with integrating factor `A t = 2 log (1 + t r) - 6 log (1 - t r)`.  The factor is
`exp (-(A 1 - A 0)) = ((1-r)^3/(1+r))^2 ≥ (1/12)^2` for `r ≤ 1/2`, and the constant is sharp at
`r = 1/2`.
-/

namespace Work.Repel

open scoped Real
open Metric

/-- Chain rule: the real derivative of a complex-differentiable function along the complex line
`t ↦ t * z`.  The value is `z * deriv P (t * z)`. -/
private lemma hasDerivAt_comp_mul_right {P : ℂ → ℂ} {z : ℂ} {t : ℝ}
    (hd : DifferentiableAt ℂ P ((t : ℂ) * z)) :
    HasDerivAt (fun s : ℝ => P ((s : ℂ) * z)) (z * deriv P ((t : ℂ) * z)) t := by
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
    have h := (Complex.ofRealCLM.hasFDerivAt (x := t)).hasDerivAt
    simpa using h.mul_const z
  have h1 : HasDerivAt P (deriv P ((t : ℂ) * z)) ((t : ℂ) * z) := hd.hasDerivAt
  have h3 := h1.scomp t h2
  simpa [Function.comp_def, smul_eq_mul] using h3

theorem deriv_lower_of_second_deriv_bound {g : ℂ → ℂ}
    (han : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g w)
    (hbound : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      ‖deriv (deriv g) w‖ ≤ (4 + 2 * ‖w‖) / (1 - ‖w‖ ^ 2) * ‖deriv g w‖)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    (1 / 12 : ℝ) * ‖deriv g 0‖ ≤ ‖deriv g z‖ := by
  set r : ℝ := ‖z‖ with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg z
  have hr1 : r ≤ 1 / 2 := by rw [hr]; exact hz
  -- the segment `[0, 1] ∋ t ↦ t * z` stays in the open unit disc
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    calc ‖(t : ℂ) * z‖ = t * r := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, ← hr]
      _ ≤ 1 * (1 / 2) := mul_le_mul ht1 hr1 hr0 (by norm_num)
      _ < 1 := by norm_num
  have hdan : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ (deriv g) w :=
    fun w hw => (han w hw).deriv
  obtain ⟨hAc0, hAd0, hAexp0⟩ := logGronwall_factor r hr0 hr1
  set A : ℝ → ℝ := fun t => 2 * Real.log (1 + t * r) - 6 * Real.log (1 - t * r) with hAdef
  set K : ℝ → ℝ := fun t => 2 * r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2)) with hKdef
  have hAc : ContinuousOn A (Set.Icc 0 1) := by rw [hAdef]; exact hAc0
  have hAd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt A (K t) t := by
    intro t ht; rw [hAdef, hKdef]; exact hAd0 t ht
  have hFc : ContinuousOn (fun t : ℝ => deriv g ((t : ℂ) * z)) (Set.Icc 0 1) := by
    intro t ht
    have h1 : ContinuousAt (deriv g) ((t : ℂ) * z) := (hdan _ (hmem t ht)).continuousAt
    have h2 : ContinuousAt (fun s : ℝ => (s : ℂ) * z) t := by fun_prop
    have h3 : ContinuousAt ((deriv g) ∘ fun s : ℝ => (s : ℂ) * z) t :=
      ContinuousAt.comp (f := fun s : ℝ => (s : ℂ) * z) (x := t) h1 h2
    simpa [Function.comp_def] using h3.continuousWithinAt
  have hyc : ContinuousOn (fun t : ℝ => ‖deriv g ((t : ℂ) * z)‖ ^ 2) (Set.Icc 0 1) :=
    (hFc.norm).pow 2
  have hyd : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => ‖deriv g ((s : ℂ) * z)‖ ^ 2)
        (2 * inner ℝ (deriv g ((t : ℂ) * z)) (z * deriv (deriv g) ((t : ℂ) * z))) t := by
    intro t ht
    have hw : ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := hmem t (Set.Ioo_subset_Icc_self ht)
    have hd : DifferentiableAt ℂ (deriv g) ((t : ℂ) * z) := (hdan _ hw).differentiableAt
    exact (hasDerivAt_comp_mul_right hd).norm_sq
  -- the reverse Grönwall inequality for `y t = ‖F t‖^2`
  have hineq : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      -(K t) * ‖deriv g ((t : ℂ) * z)‖ ^ 2
        ≤ 2 * inner ℝ (deriv g ((t : ℂ) * z)) (z * deriv (deriv g) ((t : ℂ) * z)) := by
    intro t ht
    rw [hKdef]
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hw : ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := hmem t (Set.Ioo_subset_Icc_self ht)
    have hwn : ‖((t : ℂ) * z)‖ = t * r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, ← hr]
    have hb := hbound ((t : ℂ) * z) hw
    rw [hwn] at hb
    have hkey : ‖z * deriv (deriv g) ((t : ℂ) * z)‖
        ≤ (r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2))) * ‖deriv g ((t : ℂ) * z)‖ := by
      rw [norm_mul, ← hr]
      calc r * ‖deriv (deriv g) ((t : ℂ) * z)‖
          ≤ r * (((4 + 2 * (t * r)) / (1 - (t * r) ^ 2)) * ‖deriv g ((t : ℂ) * z)‖) :=
            mul_le_mul_of_nonneg_left hb hr0
        _ = (r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2))) * ‖deriv g ((t : ℂ) * z)‖ := by ring
    have hcs := abs_real_inner_le_norm (deriv g ((t : ℂ) * z))
      (z * deriv (deriv g) ((t : ℂ) * z))
    have hle : |inner ℝ (deriv g ((t : ℂ) * z)) (z * deriv (deriv g) ((t : ℂ) * z))|
        ≤ ‖deriv g ((t : ℂ) * z)‖ * ((r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2)))
            * ‖deriv g ((t : ℂ) * z)‖) :=
      hcs.trans (mul_le_mul_of_nonneg_left hkey (norm_nonneg _))
    have hna := neg_abs_le (inner ℝ (deriv g ((t : ℂ) * z))
      (z * deriv (deriv g) ((t : ℂ) * z)))
    nlinarith [hle, hna, norm_nonneg (deriv g ((t : ℂ) * z))]
  have hmain := gronwall_lower (y := fun t : ℝ => ‖deriv g ((t : ℂ) * z)‖ ^ 2)
      (y' := fun t : ℝ => 2 * inner ℝ (deriv g ((t : ℂ) * z))
        (z * deriv (deriv g) ((t : ℂ) * z)))
      (A := A) (K := K) (by norm_num) hyc hyd hAc hAd hineq
  have hA0 : A 0 = 0 := by rw [hAdef]; simp [Real.log_one]
  have hAexp : Real.exp (-(A 1 - A 0)) = ((1 - r) ^ 3 / (1 + r)) ^ 2 := by
    rw [hA0, sub_zero, hAdef]
    exact hAexp0
  have hkey2 : ‖deriv g 0‖ ^ 2 * ((1 - r) ^ 3 / (1 + r)) ^ 2 ≤ ‖deriv g z‖ ^ 2 := by
    rw [hAexp] at hmain
    simpa using hmain
  have hq_pos : 0 < (1 - r) ^ 3 / (1 + r) :=
    div_pos (pow_pos (by linarith : 0 < 1 - r) 3) (by linarith : 0 < 1 + r)
  have hb2 : (‖deriv g 0‖ * ((1 - r) ^ 3 / (1 + r))) ^ 2 ≤ ‖deriv g z‖ ^ 2 := by
    rw [mul_pow]; exact hkey2
  have hb : ‖deriv g 0‖ * ((1 - r) ^ 3 / (1 + r)) ≤ ‖deriv g z‖ := by
    have h := sq_le_sq.mp hb2
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt hq_pos)),
        abs_of_nonneg (norm_nonneg (deriv g z))] at h
    exact h
  have hq12 : (1 / 12 : ℝ) ≤ (1 - r) ^ 3 / (1 + r) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 + r)]
    have h1 : ((1:ℝ)/2)^3 ≤ (1 - r)^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    nlinarith [h1, hr1]
  calc (1 / 12 : ℝ) * ‖deriv g 0‖
      = ‖deriv g 0‖ * (1/12) := by ring
    _ ≤ ‖deriv g 0‖ * ((1 - r)^3/(1+r)) := mul_le_mul_of_nonneg_left hq12 (norm_nonneg _)
    _ ≤ ‖deriv g z‖ := hb

end Work.Repel
