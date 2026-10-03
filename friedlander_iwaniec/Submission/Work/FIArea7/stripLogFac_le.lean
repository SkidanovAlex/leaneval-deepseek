import Mathlib
import Submission.Work.FIArea7.UniCut6

namespace Work.FIArea7

open scoped BigOperators

/-!
# `Submission.Work.FIArea7.stripLogFac_le`

The uniform two-sided bound for the (7.9)/(7.10) logarithm
`logFac6 z₁ z₂ = log(8|z₁z₂|/|Δ|)` on the *box* `gBox (radN Pa)` of `Work.FITop`:

  `|logFac6 z₁ z₂| ≤ 2 log(2 + N)`   for `exp 10 ≤ N`.

This is the `L` fed into `Work.FIArea7.stripInner_le` when bounding the small-moduli
strip `Strip6`.

The two ends are elementary.  With `R = radN Pa = ⌈√(4N)⌉` every `z ∈ gBox R` has
`|z.re|, |z.im| ≤ R`, hence `|z|² = gnorm z ≤ 2R²`; since `R ≤ 3√N` (from `√(4N) = 2√N`
and `N ≥ 1`), for `z₁, z₂ ∈ gBox R` we get `8|z₁z₂| ≤ 16R² ≤ 144N ≤ (N+2)²`.  On the
other side `|Δ(z₁,z₂)| ≤ |z₁z₂|`, so whenever `Δ ≠ 0` the argument of the logarithm is at
least `8`; and if `Δ = 0` the whole expression is `log 0 = 0` in Lean's convention.  Hence
`0 ≤ logFac6 z₁ z₂ ≤ log((N+2)²) = 2 log(N+2)`.
-/

/-! ## Self-contained Gaussian-number facts -/

private lemma slf_gnorm_eq_normSq (z : GaussianInt) :
    Complex.normSq (z : ℂ) = ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  rw [Work.FIPlan.gnorm, Nat.cast_natAbs,
    abs_of_nonneg (by exact_mod_cast GaussianInt.norm_nonneg z), GaussianInt.intCast_real_norm]

private lemma slf_gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

private lemma slf_norm_eq_sqrt (z : GaussianInt) :
    ‖(z : ℂ)‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ) : ℝ)) := by
  rw [← slf_gnorm_eq_normSq z, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

private lemma slf_delta_im (z1 z2 : GaussianInt) :
    ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) = (star (z1 : ℂ) * (z2 : ℂ)).im := by
  have h : ((star z1 * z2 : GaussianInt) : ℂ) = star (z1 : ℂ) * (z2 : ℂ) := by
    rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star]; simp
  rw [Work.FIPlan.Delta, GaussianInt.intCast_im, h]

/-- `|Δ(z₁,z₂)| = |Im(z̄₁z₂)| ≤ |z₁||z₂| = √|z₁z₂|²`. -/
private lemma slf_absDelta_le_sqrt (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
  have h1 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := h1
    _ = |(star (z1 : ℂ) * (z2 : ℂ)).im| := by rw [slf_delta_im]
    _ ≤ ‖star (z1 : ℂ) * (z2 : ℂ)‖ := Complex.abs_im_le_norm _
    _ = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by rw [norm_mul, norm_star]
    _ = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [slf_norm_eq_sqrt, slf_norm_eq_sqrt]
    _ = Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ = Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
        rw [slf_gnorm_mul, Nat.cast_mul]

/-- If `|zᵢ|² ≤ 2N` then `|z₁z₂| ≤ 2N`. -/
private lemma slf_sqrt_gnorm_mul_le (N : ℝ) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 2 * N) :
    Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ 2 * N := by
  have h2N : 0 ≤ 2 * N := le_trans (Nat.cast_nonneg _) hg1
  have h1 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * N) :=
    Real.sqrt_le_sqrt hg1
  have h2 : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ≤ Real.sqrt (2 * N) :=
    Real.sqrt_le_sqrt hg2
  calc Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
      = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [slf_gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    _ ≤ Real.sqrt (2 * N) * Real.sqrt (2 * N) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * N := by
        rw [← Real.sqrt_mul h2N, show 2 * N * (2 * N) = (2 * N) ^ 2 by ring, Real.sqrt_sq h2N]

/-- The coordinates of a member of the box `gBox R` are bounded by `R`. -/
private lemma slf_mem_gBox {R : ℤ} {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    |((z.re : ℤ) : ℝ)| ≤ (R : ℝ) ∧ |((z.im : ℤ) : ℝ)| ≤ (R : ℝ) := by
  have hmem : z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
    rw [Work.FIPlan.gBox, Finset.mem_image] at hz
    obtain ⟨p, hp, hpz⟩ := hz
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have hre : z.re = p.1 := (congrArg Zsqrtd.re hpz).symm
    have him : z.im = p.2 := (congrArg Zsqrtd.im hpz).symm
    rw [hre, him]
    exact ⟨hp1, hp2⟩
  obtain ⟨h1, h2⟩ := hmem
  rw [Finset.mem_Icc] at h1 h2
  constructor
  · rw [abs_le]
    exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
  · rw [abs_le]
    exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩

/-- `|z²| ≤ 2R²` for `z` in the box `gBox R`. -/
private lemma slf_gnorm_le_of_mem_gBox {R : ℤ} {z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox R) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
  obtain ⟨h1, h2⟩ := slf_mem_gBox hz
  have hsq : Complex.normSq (z : ℂ) = ((z.re : ℤ) : ℝ) ^ 2 + ((z.im : ℤ) : ℝ) ^ 2 := by
    rw [Complex.normSq_apply, ← GaussianInt.intCast_re z, ← GaussianInt.intCast_im z]
    ring
  rw [← slf_gnorm_eq_normSq, hsq]
  have hx : ((z.re : ℤ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg ((z.re : ℤ) : ℝ)) h1 2
    rwa [sq_abs] at h
  have hy : ((z.im : ℤ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg ((z.im : ℤ) : ℝ)) h2 2
    rwa [sq_abs] at h
  linarith

/-- **The uniform bound on the (7.10) logarithm over the box `gBox (radN Pa)`.** -/
theorem stripLogFac_le (Pa : Work.FITop.Params) (hN : Real.exp 10 ≤ (Pa.N : ℝ))
    {z1 z2 : GaussianInt} (h1 : z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa))
    (h2 : z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa)) :
    |Work.FITop4.logFac6 z1 z2| ≤ 2 * Real.log (2 + Pa.N) := by
  set n : ℕ := ⌈Real.sqrt (4 * Pa.N)⌉₊ with hn
  set Rz : ℤ := Work.FITop.radN Pa with hRzdef
  have hRz_eq : Rz = (n : ℤ) := by rw [hRzdef, Work.FITop.radN, hn]
  have hRz_cast : (Rz : ℝ) = (n : ℝ) := by rw [hRz_eq]; simp
  have h1' : z1 ∈ Work.FIPlan.gBox Rz := by rw [hRzdef]; exact h1
  have h2' : z2 ∈ Work.FIPlan.gBox Rz := by rw [hRzdef]; exact h2
  -- `N ≥ 1` and `N ≥ 144`
  have hN1 : (1 : ℝ) ≤ Pa.N := by
    have h := Real.one_le_exp_iff.mpr (show (0 : ℝ) ≤ 10 by norm_num)
    linarith
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  -- `R ≤ 3√N`, hence `R² ≤ 9N`
  have hsqrtN : 1 ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
  have hn_lt : (n : ℝ) < Real.sqrt (4 * Pa.N) + 1 := by
    have h := Nat.ceil_lt_add_one (a := Real.sqrt (4 * Pa.N)) (by positivity)
    rwa [← hn] at h
  have hsqrt4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hsqrt4] at hn_lt
  have hn_le : (n : ℝ) ≤ 3 * Real.sqrt Pa.N := by linarith
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hRz_sq : (Rz : ℝ) ^ 2 ≤ 9 * Pa.N := by
    rw [hRz_cast]
    have h := pow_le_pow_left₀ hn_nn hn_le 2
    have h9 : (3 * Real.sqrt Pa.N) ^ 2 = 9 * Pa.N := by
      rw [mul_pow, Real.sq_sqrt hN0]; norm_num
    linarith [h, h9]
  -- `144N ≤ (N+2)²`
  have h144N : (144 : ℝ) * Pa.N ≤ (2 + Pa.N) ^ 2 := by
    have hN144 : (144 : ℝ) ≤ Pa.N := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
      have h10 : Real.exp 10 = Real.exp 1 ^ 10 := by
        have h : Real.exp 10 = Real.exp ((10 : ℕ) * 1) := by norm_num
        rw [h, Real.exp_nat_mul]
      have h1024 : (1024 : ℝ) ≤ Real.exp 10 := by
        rw [h10]
        calc (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
          _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h2e 10
      linarith
    have hsqN : (144 : ℝ) * Pa.N ≤ Pa.N * Pa.N := mul_le_mul_of_nonneg_right hN144 hN0
    nlinarith [hsqN]
  -- `|z₁z₂| ≤ 2 R²`
  have hG1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * (Rz : ℝ) ^ 2 :=
    slf_gnorm_le_of_mem_gBox h1'
  have hG2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * (Rz : ℝ) ^ 2 :=
    slf_gnorm_le_of_mem_gBox h2'
  have hsqrtG : Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ 2 * (Rz : ℝ) ^ 2 :=
    slf_sqrt_gnorm_mul_le ((Rz : ℝ) ^ 2) z1 z2 hG1 hG2
  by_cases hD : Work.FIPlan.Delta z1 z2 = 0
  · -- degenerate pair: the logarithm is `log 0 = 0`
    have hA0 : Work.FIPlan.absDelta z1 z2 = 0 := by
      simp only [Work.FIPlan.absDelta, hD, Int.natAbs_zero]
    have hL0 : Work.FITop4.logFac6 z1 z2 = 0 := by
      simp [Work.FITop4.logFac6, hA0]
    rw [hL0, abs_zero]
    have h2N : (1 : ℝ) < 2 + Pa.N := by linarith
    have := Real.log_pos h2N
    linarith
  · -- non-degenerate pair: `0 ≤ logFac6 ≤ 2 log(N+2)`
    have hne : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
      simp only [Work.FIPlan.absDelta, ne_eq, Int.natAbs_eq_zero]
      exact hD
    have hApos : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hA1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hAsqrt := slf_absDelta_le_sqrt z1 z2
    have hGpos : 0 < Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) :=
      lt_of_lt_of_le hApos hAsqrt
    have hargpos : 0 < 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) :=
      div_pos (mul_pos (by norm_num) hGpos) hApos
    have harg_ge1 : (1 : ℝ) ≤ 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hApos]
      linarith [hAsqrt, hGpos.le]
    have harg_le : 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ (2 + Pa.N) ^ 2 := by
      have hnum : 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
          ≤ 16 * (Rz : ℝ) ^ 2 := by linarith [hsqrtG]
      calc 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
            / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
          ≤ 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) / 1 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hA1
        _ = 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by ring
        _ ≤ 16 * (Rz : ℝ) ^ 2 := hnum
        _ ≤ 144 * Pa.N := by linarith [hRz_sq]
        _ ≤ (2 + Pa.N) ^ 2 := h144N
    have hlog : Work.FITop4.logFac6 z1 z2
        = Real.log (8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
            / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) := rfl
    have hupper : Work.FITop4.logFac6 z1 z2 ≤ 2 * Real.log (2 + Pa.N) := by
      rw [hlog]
      calc Real.log (8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
          ≤ Real.log ((2 + Pa.N) ^ 2) := Real.log_le_log hargpos harg_le
        _ = 2 * Real.log (2 + Pa.N) := by rw [Real.log_pow]; norm_num
    have hlower : 0 ≤ Work.FITop4.logFac6 z1 z2 := by
      rw [hlog]
      exact Real.log_nonneg harg_ge1
    rw [abs_of_nonneg hlower]
    exact hupper

end Work.FIArea7
