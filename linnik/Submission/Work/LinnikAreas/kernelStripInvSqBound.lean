import Mathlib
import Submission.Work.LinnikAreas.Kernel
import Submission.Work.LinnikContract.Defs

/-!
# The `‖u‖⁻²` kernel bound on the critical strip, for arbitrary `K`

This file proves `Work.LinnikAreas.kernelStripInvSqBound`:

for `𝓛 > 0` and *arbitrary* real `L`, `K` there is `A > 0` with

`‖Hk L K ((1 - u)𝓛)‖ ≤ A / ‖u‖²`

for every `u : ℂ` with `0 ≤ Re u ≤ 1` and `‖u‖ ≥ 2`.

Here `Hk L K z = e^{-(L-2K)z}·F₂(K,z)` with `F₂(K,z) = ((1-e^{-Kz})/z)²`
(`Submission.Work.LinnikContract.Defs`).  The sibling file `Kernel.lean` proves the
sharper pointwise bounds `‖Hk L K z‖ ≤ e^{-(L-2K)Re z}·4/‖z‖²` under the
additional hypotheses `0 < K` and (in `norm_Hk_le`) `L - 2K > 0`, which force the
constant to be *exactly* `16/𝓛²`.  That route does not apply to arbitrary `K`,
because for `K < 0` the factor `1 - e^{-Kz}` grows like `e^{|K|Re z}`.

The observation here is that on the strip the growth is *uniform*: since
`Re z = (1 - Re u)·𝓛 ∈ [0, 𝓛]`, both

* `‖1 - e^{-Kz}‖ ≤ 1 + e^{|K|𝓛}`, and
* `‖e^{-(L-2K)z}‖ ≤ e^{|L-2K|𝓛}`

hold with constants depending only on `L, K, 𝓛`, and hence so does

`‖Hk L K z‖ ≤ e^{|L-2K|𝓛}·(1 + e^{|K|𝓛})² / ‖z‖²`.

Finally `‖z‖ = 𝓛‖1 - u‖ ≥ 𝓛‖u‖/2` (because `‖u‖ ≥ 2`), which turns the
`1/‖z‖²` into the required `4/(𝓛²‖u‖²)`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- On the strip `0 ≤ Re z ≤ 𝓛` the numerator `1 - e^{-Kz}` of `F₂` is bounded by
`1 + e^{|K|𝓛}`, with no hypothesis on the sign of `K`. -/
lemma norm_one_sub_exp_neg_mul_le {K 𝓛 : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 𝓛) :
    ‖1 - Complex.exp (-(K : ℂ) * z)‖ ≤ 1 + Real.exp (|K| * 𝓛) := by
  have hnorm : ‖Complex.exp (-(K : ℂ) * z)‖ = Real.exp (-(K * z.re)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  calc ‖1 - Complex.exp (-(K : ℂ) * z)‖
      ≤ 1 + ‖Complex.exp (-(K : ℂ) * z)‖ := by
        simpa using norm_sub_le (1 : ℂ) (Complex.exp (-(K : ℂ) * z))
    _ ≤ 1 + Real.exp (|K| * 𝓛) := by
        gcongr
        rw [hnorm]
        apply Real.exp_le_exp.mpr
        have h1 : |z.re| ≤ 𝓛 := by rw [abs_of_nonneg hz0]; exact hz1
        have h2 : -(K * z.re) ≤ |K * z.re| := neg_le_abs _
        rw [abs_mul] at h2
        calc -(K * z.re) ≤ |K| * |z.re| := h2
          _ ≤ |K| * 𝓛 := by gcongr

/-- On the strip `0 ≤ Re z ≤ 𝓛`, `‖e^{-(L-2K)z}‖ ≤ e^{|L-2K|𝓛}`. -/
lemma norm_exp_neg_mul_le {L K 𝓛 : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 𝓛) :
    ‖Complex.exp (-((L - 2 * K : ℝ) : ℂ) * z)‖ ≤ Real.exp (|L - 2 * K| * 𝓛) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h : (-((L - 2 * K : ℝ) : ℂ) * z).re = -((L - 2 * K) * z.re) := by
    simp [Complex.mul_re]
    ring
  rw [h]
  have h1 : |z.re| ≤ 𝓛 := by rw [abs_of_nonneg hz0]; exact hz1
  have h2 : -((L - 2 * K) * z.re) ≤ |(L - 2 * K) * z.re| := neg_le_abs _
  rw [abs_mul] at h2
  calc -((L - 2 * K) * z.re) ≤ |L - 2 * K| * |z.re| := h2
    _ ≤ |L - 2 * K| * 𝓛 := by gcongr

/-- On the strip, `‖F₂(K,z)‖ ≤ (1 + e^{|K|𝓛})²/‖z‖²`. -/
lemma norm_F2_le_const {K 𝓛 : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 𝓛)
    (hzn : 0 < ‖z‖) :
    ‖F2 K z‖ ≤ (1 + Real.exp (|K| * 𝓛)) ^ 2 / ‖z‖ ^ 2 := by
  have hdiv : ‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖
      ≤ (1 + Real.exp (|K| * 𝓛)) / ‖z‖ :=
    div_le_div_of_nonneg_right (norm_one_sub_exp_neg_mul_le hz0 hz1) (le_of_lt hzn)
  calc ‖F2 K z‖ = (‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖) ^ 2 := by
        rw [F2, norm_pow, norm_div]
    _ ≤ ((1 + Real.exp (|K| * 𝓛)) / ‖z‖) ^ 2 := pow_le_pow_left₀ (by positivity) hdiv 2
    _ = (1 + Real.exp (|K| * 𝓛)) ^ 2 / ‖z‖ ^ 2 := by rw [div_pow]

/-- **General pointwise kernel bound.**  For `0 ≤ Re z ≤ 𝓛`, `z ≠ 0` and arbitrary real
`L, K`,
`‖Hk L K z‖ ≤ e^{|L-2K|𝓛}·(1 + e^{|K|𝓛})²/‖z‖²`. -/
lemma norm_Hk_le_general {L K 𝓛 : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 𝓛)
    (hzn : 0 < ‖z‖) :
    ‖Hk L K z‖ ≤ Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 / ‖z‖ ^ 2 := by
  rw [Hk, norm_mul]
  calc ‖Complex.exp (-((L - 2 * K : ℝ) : ℂ) * z)‖ * ‖F2 K z‖
      ≤ Real.exp (|L - 2 * K| * 𝓛) * ((1 + Real.exp (|K| * 𝓛)) ^ 2 / ‖z‖ ^ 2) :=
        mul_le_mul (norm_exp_neg_mul_le hz0 hz1) (norm_F2_le_const hz0 hz1 hzn)
          (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 / ‖z‖ ^ 2 := by ring

/-- **The `‖u‖⁻²` kernel bound on the critical strip** (for arbitrary real `L`, `K`).

There is a constant `A > 0` — explicitly
`A = 4·e^{|L-2K|𝓛}·(1 + e^{|K|𝓛})²/𝓛²` — such that for every `u : ℂ` with
`0 ≤ Re u ≤ 1` and `‖u‖ ≥ 2` one has `‖Hk L K ((1-u)𝓛)‖ ≤ A/‖u‖²`. -/
theorem kernelStripInvSqBound {𝓛 : ℝ} (h𝓛 : 0 < 𝓛) (L K : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 1 → 2 ≤ ‖u‖ →
      ‖Work.LinnikContract.Hk L K ((1 - u) * (𝓛 : ℂ))‖ ≤ A / ‖u‖ ^ 2 := by
  refine ⟨4 * Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 / 𝓛 ^ 2,
    by positivity, ?_⟩
  intro u hu0 hu1 hu2
  set z : ℂ := (1 - u) * (𝓛 : ℂ) with hz
  -- The real part of `z` lies in `[0, 𝓛]`.
  have hzre : z.re = (1 - u.re) * 𝓛 := by
    rw [hz, Complex.mul_re]
    simp
  have hz0 : 0 ≤ z.re := by
    rw [hzre]; exact mul_nonneg (by linarith) (le_of_lt h𝓛)
  have hz1 : z.re ≤ 𝓛 := by rw [hzre]; nlinarith [h𝓛]
  -- `‖z‖ = 𝓛‖1 - u‖` and `‖u‖ ≥ 2` gives `‖1 - u‖ ≥ 1` and `‖z‖ > 0`.
  have hzabs : ‖z‖ = 𝓛 * ‖1 - u‖ := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝓛, norm_sub_rev]
    ring
  have htri : ‖u‖ ≤ ‖1 - u‖ + 1 := by
    have h := norm_add_le (u - 1) (1 : ℂ)
    rw [sub_add_cancel] at h
    rw [norm_sub_rev] at h
    simpa using h
  have hu1n : 1 ≤ ‖1 - u‖ := by linarith
  have hupos : 0 < ‖u‖ := by linarith
  have hzn : 0 < ‖z‖ := by rw [hzabs]; exact mul_pos h𝓛 (by linarith)
  -- Pointwise bound on the strip.
  have hHk := norm_Hk_le_general (L := L) (K := K) hz0 hz1 hzn
  -- `‖z‖ ≥ 𝓛‖u‖/2`, hence `𝓛²‖u‖² ≤ 4‖z‖²`.
  have hzu : 𝓛 * ‖u‖ / 2 ≤ ‖z‖ := by
    rw [hzabs]
    have h2 : ‖u‖ / 2 ≤ ‖1 - u‖ := by linarith
    nlinarith [h𝓛]
  have hkey : 𝓛 ^ 2 * ‖u‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
    have hsq : (𝓛 * ‖u‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hzu 2
    nlinarith [hsq]
  have hDC : 0 < Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 := by
    positivity
  calc ‖Hk L K z‖
      ≤ Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 / ‖z‖ ^ 2 := hHk
    _ ≤ (4 * Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 / 𝓛 ^ 2)
          / ‖u‖ ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hzn 2) (pow_pos hupos 2)]
        have he : (4 * Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 / 𝓛 ^ 2)
              * ‖z‖ ^ 2
            = 4 * Real.exp (|L - 2 * K| * 𝓛) * (1 + Real.exp (|K| * 𝓛)) ^ 2 * ‖z‖ ^ 2
              / 𝓛 ^ 2 := by ring
        rw [he, le_div_iff₀ (pow_pos h𝓛 2)]
        have hX := mul_le_mul_of_nonneg_left hkey (le_of_lt hDC)
        nlinarith [hX]

end Work.LinnikAreas
