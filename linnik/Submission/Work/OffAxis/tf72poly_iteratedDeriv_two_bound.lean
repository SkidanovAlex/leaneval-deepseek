import Mathlib
import Submission.Work.ZeroFreeTables.tf72Fc_decay
import Submission.Work.ZeroFreeTables.XY.deriv_tf72poly_eq
import Submission.Work.ZeroFreeTables.XY.hasDerivAt_deriv_tf72poly

namespace Work.OffAxis

open Work.ZeroFreeTables (tf72poly)

/-- `tf72poly lam`, expanded as an explicit polynomial in `t`:
`(λ/30)(2-λt)³(4+6λt+λ²t²) = (λ/30)(32 - 40λ²t² + 20λ³t³ - λ⁵t⁵)`. -/
noncomputable def tf72polyExpanded (lam : ℝ) (t : ℝ) : ℝ :=
  (lam / 30) * (32 - 40 * lam ^ 2 * t ^ 2 + 20 * lam ^ 3 * t ^ 3 - lam ^ 5 * t ^ 5)

lemma tf72poly_eq_tf72polyExpanded (lam : ℝ) : tf72poly lam = tf72polyExpanded lam := by
  funext t
  unfold tf72polyExpanded tf72poly
  ring

/-- First derivative of the expanded polynomial `tf72polyExpanded lam`. -/
lemma hasDerivAt_tf72polyExpanded (lam t : ℝ) :
    HasDerivAt (tf72polyExpanded lam)
      ((lam / 30) * (-(80 * lam ^ 2) * t + 60 * lam ^ 3 * t ^ 2 - 5 * lam ^ 5 * t ^ 4)) t := by
  have h0 : HasDerivAt (fun _ : ℝ => (32 : ℝ)) 0 t := hasDerivAt_const (x := t) (32 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => 40 * lam ^ 2 * s ^ 2) (40 * lam ^ 2 * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (40 * lam ^ 2)
  have h3 : HasDerivAt (fun s : ℝ => 20 * lam ^ 3 * s ^ 3) (20 * lam ^ 3 * (3 * t ^ 2)) t := by
    simpa using (hasDerivAt_pow 3 t).const_mul (20 * lam ^ 3)
  have h5 : HasDerivAt (fun s : ℝ => lam ^ 5 * s ^ 5) (lam ^ 5 * (5 * t ^ 4)) t := by
    simpa using (hasDerivAt_pow 5 t).const_mul (lam ^ 5)
  have hc : HasDerivAt
      (fun s : ℝ => 32 - 40 * lam ^ 2 * s ^ 2 + 20 * lam ^ 3 * s ^ 3 - lam ^ 5 * s ^ 5)
      (0 - 40 * lam ^ 2 * (2 * t) + 20 * lam ^ 3 * (3 * t ^ 2) - lam ^ 5 * (5 * t ^ 4)) t :=
    ((h0.sub h2).add h3).sub h5
  have hcm := hc.const_mul (lam / 30)
  have heq : (0 - 40 * lam ^ 2 * (2 * t) + 20 * lam ^ 3 * (3 * t ^ 2) - lam ^ 5 * (5 * t ^ 4))
      = (-(80 * lam ^ 2) * t + 60 * lam ^ 3 * t ^ 2 - 5 * lam ^ 5 * t ^ 4) := by ring
  rw [heq] at hcm
  unfold tf72polyExpanded
  exact hcm

/-- Derivative of the first derivative of the expanded polynomial. -/
lemma hasDerivAt_deriv_tf72polyExpanded (lam t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        (lam / 30) * (-(80 * lam ^ 2) * s + 60 * lam ^ 3 * s ^ 2 - 5 * lam ^ 5 * s ^ 4))
      ((lam / 30) * (-(80 * lam ^ 2) + 120 * lam ^ 3 * t - 20 * lam ^ 5 * t ^ 3)) t := by
  have h0 : HasDerivAt (fun s : ℝ => (-(80 * lam ^ 2)) * s) (-(80 * lam ^ 2)) t := by
    simpa using (hasDerivAt_id' t).const_mul (-(80 * lam ^ 2))
  have h2 : HasDerivAt (fun s : ℝ => 60 * lam ^ 3 * s ^ 2) (60 * lam ^ 3 * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (60 * lam ^ 3)
  have h4 : HasDerivAt (fun s : ℝ => 5 * lam ^ 5 * s ^ 4) (5 * lam ^ 5 * (4 * t ^ 3)) t := by
    simpa using (hasDerivAt_pow 4 t).const_mul (5 * lam ^ 5)
  have hc : HasDerivAt
      (fun s : ℝ => (-(80 * lam ^ 2)) * s + 60 * lam ^ 3 * s ^ 2 - 5 * lam ^ 5 * s ^ 4)
      ((-(80 * lam ^ 2)) + 60 * lam ^ 3 * (2 * t) - 5 * lam ^ 5 * (4 * t ^ 3)) t :=
    (h0.add h2).sub h4
  have hcm := hc.const_mul (lam / 30)
  have heq : ((-(80 * lam ^ 2)) + 60 * lam ^ 3 * (2 * t) - 5 * lam ^ 5 * (4 * t ^ 3))
      = (-(80 * lam ^ 2) + 120 * lam ^ 3 * t - 20 * lam ^ 5 * t ^ 3) := by ring
  rw [heq] at hcm
  exact hcm

/-- Explicit value of the second derivative of `tf72poly lam`:
`(tf72poly lam)''(t) = (λ/30)(-80λ² + 120λ³t - 20λ⁵t³)`. -/
lemma tf72poly_iteratedDeriv_two_eq (lam t : ℝ) :
    iteratedDeriv 2 (tf72poly lam) t
      = (lam / 30) * (-(80 * lam ^ 2) + 120 * lam ^ 3 * t - 20 * lam ^ 5 * t ^ 3) := by
  have h2 : iteratedDeriv 2 (tf72poly lam) = deriv (deriv (tf72poly lam)) := by
    show iteratedDeriv ((1 : ℕ) + 1) (tf72poly lam) = deriv (deriv (tf72poly lam))
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd1 : deriv (tf72poly lam) = fun s : ℝ =>
      (lam / 30) * (-(80 * lam ^ 2) * s + 60 * lam ^ 3 * s ^ 2 - 5 * lam ^ 5 * s ^ 4) := by
    rw [tf72poly_eq_tf72polyExpanded]
    funext s
    exact (hasDerivAt_tf72polyExpanded lam s).deriv
  rw [h2, hd1]
  exact (hasDerivAt_deriv_tf72polyExpanded lam t).deriv

theorem tf72poly_iteratedDeriv_two_bound (lam t : ℝ) (hlam : 0 < lam) (ht0 : 0 ≤ t)
    (ht : t ≤ 2 / lam) :
    ‖((iteratedDeriv 2 (Work.ZeroFreeTables.tf72poly lam) t : ℝ) : ℂ)‖ ≤ 16 * lam ^ 3 := by
  have heq : iteratedDeriv 2 (Work.ZeroFreeTables.tf72poly lam) t
      = (lam / 30) * (-(80 * lam ^ 2) + 120 * lam ^ 3 * t - 20 * lam ^ 5 * t ^ 3) :=
    tf72poly_iteratedDeriv_two_eq lam t
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hlam30 : (0 : ℝ) ≤ lam / 30 := by positivity
  have ht3nn : (0 : ℝ) ≤ lam ^ 3 * t := mul_nonneg (pow_nonneg hlam.le 3) ht0
  have ht5nn : (0 : ℝ) ≤ lam ^ 5 * t ^ 3 := mul_nonneg (pow_nonneg hlam.le 5) (pow_nonneg ht0 3)
  -- triangle inequality
  have htri : |-(80 * lam ^ 2) + 120 * lam ^ 3 * t - 20 * lam ^ 5 * t ^ 3|
      ≤ 80 * lam ^ 2 + 120 * lam ^ 3 * t + 20 * lam ^ 5 * t ^ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [ht3nn, ht5nn]
  -- `λt ≤ 2` and hence the polynomial part is at most `480 λ²`
  have hu0 : (0 : ℝ) ≤ lam * t := mul_nonneg hlam.le ht0
  have hu2 : lam * t ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left ht hlam.le
    have h2 : lam * (2 / lam) = 2 := by field_simp
    linarith
  have hcube : (lam * t) ^ 3 ≤ 8 := by
    have h := pow_le_pow_left₀ hu0 hu2 3
    norm_num at h
    exact h
  have hmain : 80 * lam ^ 2 + 120 * lam ^ 3 * t + 20 * lam ^ 5 * t ^ 3 ≤ 480 * lam ^ 2 := by
    have hfac : 80 * lam ^ 2 + 120 * lam ^ 3 * t + 20 * lam ^ 5 * t ^ 3
        = lam ^ 2 * (80 + 120 * (lam * t) + 20 * (lam * t) ^ 3) := by ring
    rw [hfac]
    calc lam ^ 2 * (80 + 120 * (lam * t) + 20 * (lam * t) ^ 3)
        ≤ lam ^ 2 * (80 + 120 * 2 + 20 * 8) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg lam)
          nlinarith [hu0, hu2, hcube]
      _ = 480 * lam ^ 2 := by ring
  calc |(lam / 30) * (-(80 * lam ^ 2) + 120 * lam ^ 3 * t - 20 * lam ^ 5 * t ^ 3)|
      = (lam / 30) * |-(80 * lam ^ 2) + 120 * lam ^ 3 * t - 20 * lam ^ 5 * t ^ 3| := by
        rw [abs_mul, abs_of_nonneg hlam30]
    _ ≤ (lam / 30) * (80 * lam ^ 2 + 120 * lam ^ 3 * t + 20 * lam ^ 5 * t ^ 3) :=
        mul_le_mul_of_nonneg_left htri hlam30
    _ ≤ (lam / 30) * (480 * lam ^ 2) := mul_le_mul_of_nonneg_left hmain hlam30
    _ = 16 * lam ^ 3 := by ring

end Work.OffAxis
