/-
# Interchange of the detector sum with the Cauchy kernel

`Work.LinnikAreas.BGTZ.detJ` (see `DetectorDefs`) is a vertical-line integral of a *series*
(the Dirichlet series of the detector coefficient).  This file proves that the integral of the
series is the series of the integrals (`DetectorInterchange`), which is the Fubini step that
lets the detector proof treat the individual summands.  The estimate that makes the interchange
legitimate is that the `t`-dependence of the modulus of the `n`-th summand is exactly
`‖f n‖ / n^{Re (ρ + c)}`, times the integrable kernel `‖N^{c+it}/((c+it)(c+1+it))‖`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetectorKernelBound
import Submission.Work.LinnikAreas.BGTZ.DetectorZeroTerm

open MeasureTheory

namespace Work.LinnikAreas.BGTZ

/-- `x * y / z = x * (y / z)` (associativity of division). -/
private lemma mul_div_assoc' (x y z : ℂ) : x * y / z = x * (y / z) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

/-- Real part of `d + i t`. -/
private lemma re_add_mul_I (t d : ℝ) : ((d : ℂ) + t * Complex.I).re = d := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]

/-- Real part of the exponent `ρ + (c + i t)`. -/
private lemma re_exponent (t c : ℝ) (ρ : ℂ) :
    (ρ + (c + t * Complex.I)).re = c + ρ.re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
  ring

/-- `d + i t ≠ 0` for `d > 0`. -/
private lemma add_mul_I_ne_zero (t d : ℝ) (hd : 0 < d) : (d : ℂ) + t * Complex.I ≠ 0 := by
  intro h
  have h2 : d = 0 := by
    simpa only [re_add_mul_I t d, Complex.zero_re] using congrArg Complex.re h
  exact hd.ne' h2

/-- `c + 1 + i t ≠ 0` for `c > 0`. -/
private lemma one_add_add_mul_I_ne_zero (t c : ℝ) (hc : 0 < c) :
    (c : ℂ) + 1 + t * Complex.I ≠ 0 := by
  intro h
  have h2 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re] at h2
  linarith

/-- The kernel `t ↦ ‖N^{c+it}/((c+it)(c+1+it))‖` is integrable: it is bounded by
`N^c (1 + 1/c²)/(1+t²)`. -/
private lemma integrable_norm_kernel {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) :
    Integrable (fun t : ℝ => ‖(N : ℂ) ^ (c + t * Complex.I) /
      ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖) := by
  have hb : ∀ t : ℝ, ‖(N : ℂ) ^ (c + t * Complex.I) /
      ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖
        ≤ (N : ℝ) ^ c * (1 + 1 / c ^ 2) * (1 + t ^ 2)⁻¹ := by
    intro t
    exact DetectorKernelBound hc hN t
  have hbase : Integrable (fun t : ℝ => (N : ℝ) ^ c * (1 + 1 / c ^ 2) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul ((N : ℝ) ^ c * (1 + 1 / c ^ 2))
  refine hbase.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    change Continuous fun t : ℝ => ‖(N : ℂ) ^ (c + t * Complex.I) /
      ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖
    refine continuous_norm.comp ?_
    refine Continuous.div ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * Complex.I).const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))
    · fun_prop
    · intro t
      exact mul_ne_zero (add_mul_I_ne_zero t c hc) (one_add_add_mul_I_ne_zero t c hc)
  · filter_upwards with t
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hb t

/-- The `n`-th summand of the detector series has `t`-modulus `‖f n‖ / n^{Re (ρ+c)}` times the
kernel, for `n ≥ 1`. -/
private lemma norm_summand (f : ℕ → ℂ) {c : ℝ} (ρ : ℂ) {N : ℕ} {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(f n / (n : ℂ) ^ (ρ + (c + t * Complex.I))) *
      ((N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I)))‖
      = ‖f n‖ / (n : ℝ) ^ (c + ρ.re) *
        ‖(N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖ := by
  rw [norm_mul, norm_div, Complex.norm_natCast_cpow_of_pos hn, re_exponent t c ρ]

/-- Every summand of the detector series is integrable along the vertical line. -/
private lemma integrable_summand (f : ℕ → ℂ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) (ρ : ℂ)
    (n : ℕ) :
    Integrable (fun t : ℝ => (f n / (n : ℂ) ^ (ρ + (c + t * Complex.I))) *
      ((N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I)))) := by
  have hK : Integrable (fun t : ℝ => ‖(N : ℂ) ^ (c + t * Complex.I) /
      ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖) := integrable_norm_kernel hc hN
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simpa only [Nat.cast_zero] using DetectorZeroTerm hc ρ hN f hK
  · have hcont : Continuous (fun t : ℝ => (f n / (n : ℂ) ^ (ρ + (c + t * Complex.I))) *
        ((N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I)))) := by
      refine Continuous.mul ?_ ?_
      · refine Continuous.div continuous_const ?_ ?_
        · exact (by fun_prop : Continuous fun t : ℝ => ρ + (c + t * Complex.I)).const_cpow
            (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))
        · intro t
          exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))
      · refine Continuous.div ?_ ?_ ?_
        · exact (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * Complex.I).const_cpow
            (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))
        · fun_prop
        · intro t
          exact mul_ne_zero (add_mul_I_ne_zero t c hc) (one_add_add_mul_I_ne_zero t c hc)
    refine Integrable.mono' (hK.const_mul (‖f n‖ / (n : ℝ) ^ (c + ρ.re))) ?_ ?_
    · exact hcont.aestronglyMeasurable
    · filter_upwards with t
      exact le_of_eq (norm_summand f ρ (c := c) (N := N) hn t)

theorem DetectorInterchange (f : ℕ → ℂ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ)
    (hconv : Summable (fun n : ℕ => ‖f n‖ / (n : ℝ) ^ (c + ρ.re))) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∑' n : ℕ, f n / (n : ℂ) ^ (ρ + (c + t * Complex.I)))
        * (N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I))
      = ∑' n : ℕ, (1 / (2 * Real.pi)) * ∫ t : ℝ, (f n / (n : ℂ) ^ (ρ + (c + t * Complex.I)))
        * (N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I)) := by
  have hNpos : 0 < N := hN
  let A : ℝ → ℂ := fun t => (N : ℂ) ^ (c + t * Complex.I) /
    ((c + t * Complex.I) * (c + 1 + t * Complex.I))
  let B : ℕ → ℝ → ℂ := fun n t => f n / (n : ℂ) ^ (ρ + (c + t * Complex.I))
  let C : ℕ → ℝ := fun n => ‖f n‖ / (n : ℝ) ^ (c + ρ.re)
  let I : ℝ := ∫ t : ℝ, ‖A t‖
  have hA_apply : ∀ t : ℝ, A t = (N : ℂ) ^ (c + t * Complex.I) /
      ((c + t * Complex.I) * (c + 1 + t * Complex.I)) := fun t => rfl
  have hB_apply : ∀ (n : ℕ) (t : ℝ), B n t = f n / (n : ℂ) ^ (ρ + (c + t * Complex.I)) :=
    fun n t => rfl
  have hC_apply : ∀ n : ℕ, C n = ‖f n‖ / (n : ℝ) ^ (c + ρ.re) := fun n => rfl
  have hI_eq : I = ∫ t : ℝ, ‖A t‖ := rfl
  -- the kernel is integrable, with the measure-theoretic facts we need
  have hKint : Integrable (fun t : ℝ => ‖A t‖) := by
    simpa only [hA_apply] using integrable_norm_kernel hc hNpos
  have hAbound : ∀ t : ℝ, ‖A t‖ ≤ (N : ℝ) ^ c * (1 + 1 / c ^ 2) * (1 + t ^ 2)⁻¹ := by
    intro t
    simpa only [hA_apply t] using DetectorKernelBound hc hNpos t
  have hInonneg : 0 ≤ I := by
    rw [hI_eq]
    exact integral_nonneg fun t => norm_nonneg _
  -- summation of the dominating constants
  have hCsum : Summable (fun n : ℕ => C n * I) := by
    have h := hconv.mul_right I
    simpa only [hC_apply] using h
  -- the integrals of the summands are summable
  have hFsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖B n t * A t‖) := by
    have htail : Summable (fun n : ℕ => ∫ t : ℝ, ‖B (n + 1) t * A t‖) := by
      refine Summable.of_nonneg_of_le (f := fun n : ℕ => C (n + 1) * I)
        (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_) ?_
      · have heq : (fun t : ℝ => ‖B (n + 1) t * A t‖) = fun t : ℝ => C (n + 1) * ‖A t‖ :=
          funext fun t => by
            rw [hB_apply (n + 1) t, hA_apply t, hC_apply (n + 1),
              norm_summand f ρ (c := c) (N := N) (Nat.succ_pos n) t]
        rw [heq, hI_eq]
        exact le_of_eq (integral_const_mul (C (n + 1)) (fun t : ℝ => ‖A t‖))
      · exact (summable_nat_add_iff 1).mpr hCsum
    exact (summable_nat_add_iff 1).mp htail
  -- the summands are integrable
  have hFint : ∀ n : ℕ, Integrable (fun t : ℝ => B n t * A t) := by
    intro n
    have := integrable_summand f hc hNpos ρ n
    simpa only [hA_apply, hB_apply] using this
  -- the interchange
  have hmain : ∑' n : ℕ, ∫ t : ℝ, B n t * A t = ∫ t : ℝ, ∑' n : ℕ, B n t * A t :=
    integral_tsum_of_summable_integral_norm hFint hFsum
  have key : (1 / (2 * Real.pi)) * ∫ t : ℝ, (∑' n : ℕ, B n t) * A t
      = ∑' n : ℕ, (1 / (2 * Real.pi)) * ∫ t : ℝ, B n t * A t := by
    have hcongr : (∫ t : ℝ, (∑' n : ℕ, B n t) * A t) = ∫ t : ℝ, ∑' n : ℕ, B n t * A t := by
      apply integral_congr_ae
      filter_upwards with t
      exact tsum_mul_right.symm
    rw [hcongr, ← hmain]
    exact (tsum_mul_left (a := 1 / (2 * Real.pi))
      (f := fun n : ℕ => ∫ t : ℝ, B n t * A t)).symm
  -- rewrite the goal into the `A`/`B` form
  have hL : (∫ t : ℝ, (∑' n : ℕ, f n / (n : ℂ) ^ (ρ + (c + t * Complex.I)))
        * (N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I)))
      = ∫ t : ℝ, (∑' n : ℕ, B n t) * A t := by
    apply integral_congr_ae
    filter_upwards with t
    simp only [hA_apply t]
    rw [mul_div_assoc']
  have hR : (∑' n : ℕ, (1 / (2 * Real.pi)) * ∫ t : ℝ, (f n / (n : ℂ) ^ (ρ + (c + t * Complex.I)))
        * (N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I)))
      = ∑' n : ℕ, (1 / (2 * Real.pi)) * ∫ t : ℝ, B n t * A t := by
    apply tsum_congr
    intro n
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    simp only [hA_apply t, hB_apply n t]
    rw [mul_div_assoc']
  rw [hL, hR]
  exact key

end Work.LinnikAreas.BGTZ
