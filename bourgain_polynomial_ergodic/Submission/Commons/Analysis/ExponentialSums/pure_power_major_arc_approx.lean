import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_major_arc_approx
import Submission.Commons.Analysis.Integral.riemann_sum_sub_integral_le
import Submission.Commons.Analysis.Polynomial.dvd_eval_sub_eval_mul

namespace Commons.Analysis.ExponentialSums

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

/-! ## Residue-class factorisation of the pure-power Weyl sum -/

/-- Pointwise factorisation of the pure-power phase along a residue class: writing
`α = a/q + β` and `n = p q + r`, the phase `e(α n^d)` splits as the product of the
`q`-periodic factor `e(a r^d / q)` and the `β`-oscillating factor `e(β n^d)`.  The reason
is that `q ∣ n^d - r^d`, so the two phases differ by an integer multiple of `2πi`. -/
lemma pow_phase_factor_term (d q : ℕ) (hq : 0 < q) (a : ℤ) (β : ℝ) (p r : ℕ) :
    expTwoPiI (((a : ℝ) / (q : ℝ) + β) * ((p * q + r : ℕ) : ℝ) ^ d)
      = expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)
        * expTwoPiI (β * ((p * q + r : ℕ) : ℝ) ^ d) := by
  set n : ℝ := ((p * q + r : ℕ) : ℝ) with hn
  have hdvd : (q : ℤ) ∣ ((p * q + r : ℕ) : ℤ) ^ d - (r : ℤ) ^ d := by
    have h1 : ((p * q + r : ℕ) : ℤ) - (r : ℤ) ∣ ((p * q + r : ℕ) : ℤ) ^ d - (r : ℤ) ^ d :=
      sub_dvd_pow_sub_pow _ _ d
    have h2 : ((p * q + r : ℕ) : ℤ) - (r : ℤ) = (p : ℤ) * (q : ℤ) := by push_cast; ring
    rw [h2] at h1
    exact dvd_trans (dvd_mul_left (q : ℤ) (p : ℤ)) h1
  obtain ⟨k, hk⟩ := hdvd
  have hreal : n ^ d - (r : ℝ) ^ d = (q : ℝ) * (k : ℝ) := by
    have hcast : ((((p * q + r : ℕ) : ℤ) ^ d - (r : ℤ) ^ d : ℤ) : ℝ) = (((q : ℤ) * k : ℤ) : ℝ) := by
      rw [hk]
    push_cast at hcast
    rw [hn]
    push_cast
    exact hcast
  have hphase : (((a : ℝ) / (q : ℝ) + β) * n ^ d)
      - ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d + β * n ^ d) = (a : ℝ) * (k : ℝ) := by
    rw [show (((a : ℝ) / (q : ℝ) + β) * n ^ d)
        - ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d + β * n ^ d)
        = ((a : ℝ) / (q : ℝ)) * (n ^ d - (r : ℝ) ^ d) by ring, hreal]
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp
  have hkey : ((((a : ℝ) / (q : ℝ) + β) * n ^ d : ℝ) : ℂ)
      - ((((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d : ℝ) : ℂ) + ((β * n ^ d : ℝ) : ℂ))
      = ((a * k : ℤ) : ℂ) := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_sub]
    congr 1
    push_cast
    exact hphase
  rw [expTwoPiI_def, expTwoPiI_def, expTwoPiI_def, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * k, ?_⟩
  linear_combination (2 * Real.pi * Complex.I) * hkey

/-- The residue-class factorisation of the pure-power Weyl sum, phrased with the
character `e(x) = exp(2πi x)`. -/
theorem pow_phase_residue_factor (d N q : ℕ) (hq : 0 < q) (a : ℤ) (β : ℝ) :
    (∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d))
      = ∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)
          * ∑ p ∈ Finset.range ((N + q - 1 - r) / q),
              expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d) := by
  rw [sum_range_residue_split (fun n : ℕ => expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d))
    N q hq]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => pow_phase_factor_term d q hq a β p r)

/-! ## The oscillatory integral of a pure power -/

/-- Continuity of the pure-power character `s ↦ e(a s^d)`. -/
lemma continuous_expTwoPiI_pow (d : ℕ) (a : ℝ) :
    Continuous (fun s : ℝ => expTwoPiI (a * s ^ d)) := by
  rw [show (fun s : ℝ => expTwoPiI (a * s ^ d))
      = (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((a * s ^ d) : ℝ) : ℂ))) from rfl]
  fun_prop

/-- The oscillatory pure-power integral is bounded by `1` on the unit interval. -/
lemma norm_integral_expTwoPiI_pow_le (d : ℕ) (a : ℝ) :
    ‖∫ s in (0 : ℝ)..1, expTwoPiI (a * s ^ d)‖ ≤ 1 := by
  calc ‖∫ s in (0 : ℝ)..1, expTwoPiI (a * s ^ d)‖
      ≤ ∫ s in (0 : ℝ)..1, ‖expTwoPiI (a * s ^ d)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = 1 := by simp_rw [norm_expTwoPiI]; simp

/-- Comparison of two oscillatory pure-power integrals. -/
lemma norm_integral_expTwoPiI_pow_sub_le (d : ℕ) (a b : ℝ) :
    ‖(∫ s in (0 : ℝ)..1, expTwoPiI (a * s ^ d)) - (∫ s in (0 : ℝ)..1, expTwoPiI (b * s ^ d))‖
      ≤ 2 * Real.pi * |a - b| / (d + 1) := by
  have hsub : (∫ s in (0 : ℝ)..1, expTwoPiI (a * s ^ d)) - (∫ s in (0 : ℝ)..1, expTwoPiI (b * s ^ d))
      = ∫ s in (0 : ℝ)..1, (expTwoPiI (a * s ^ d) - expTwoPiI (b * s ^ d)) := by
    rw [intervalIntegral.integral_sub ((continuous_expTwoPiI_pow d a).intervalIntegrable _ _)
      ((continuous_expTwoPiI_pow d b).intervalIntegrable _ _)]
  rw [hsub]
  have hpoint : ∀ s : ℝ, 0 ≤ s →
      ‖expTwoPiI (a * s ^ d) - expTwoPiI (b * s ^ d)‖ ≤ 2 * Real.pi * |a - b| * s ^ d := by
    intro s hs
    calc ‖expTwoPiI (a * s ^ d) - expTwoPiI (b * s ^ d)‖
        ≤ 2 * Real.pi * |a * s ^ d - b * s ^ d| := norm_expTwoPiI_sub_le _ _
      _ = 2 * Real.pi * |a - b| * s ^ d := by
          rw [show a * s ^ d - b * s ^ d = (a - b) * s ^ d by ring, abs_mul,
            abs_of_nonneg (pow_nonneg hs d)]
          ring
  have hint2 : IntervalIntegrable (fun s : ℝ => 2 * Real.pi * |a - b| * s ^ d) volume 0 1 :=
    (by fun_prop : Continuous (fun s : ℝ => 2 * Real.pi * |a - b| * s ^ d)).intervalIntegrable _ _
  calc ‖∫ s in (0 : ℝ)..1, (expTwoPiI (a * s ^ d) - expTwoPiI (b * s ^ d))‖
      ≤ ∫ s in (0 : ℝ)..1, 2 * Real.pi * |a - b| * s ^ d := by
        refine intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num) ?_ hint2
        filter_upwards with s hs
        exact hpoint s (le_of_lt hs.1)
    _ = 2 * Real.pi * |a - b| / (d + 1) := by
        rw [show (∫ s in (0 : ℝ)..1, 2 * Real.pi * |a - b| * s ^ d)
              = (2 * Real.pi * |a - b|) * ∫ s in (0 : ℝ)..1, s ^ d by
              rw [← intervalIntegral.integral_const_mul]]
        rw [integral_pow]
        rw [one_pow, zero_pow (Nat.succ_ne_zero d), sub_zero]
        field_simp

/-! ## Comparing the pure-power `β`-sum with its integral -/

/-- Derivative of `t ↦ e(c t^d)`. -/
private lemma hasDerivAt_expTwoPiI_pow (d : ℕ) (c t : ℝ) :
    HasDerivAt (fun t : ℝ => expTwoPiI (c * t ^ d))
      (expTwoPiI (c * t ^ d) *
        (2 * Real.pi * Complex.I * ((c * ((d : ℝ) * t ^ (d - 1)) : ℝ) : ℂ))) t := by
  have hu : HasDerivAt (fun t : ℝ => c * t ^ d) (c * ((d : ℝ) * t ^ (d - 1))) t :=
    (hasDerivAt_pow d t).const_mul c
  have hv : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * (((c * t ^ d) : ℝ) : ℂ))
      (2 * Real.pi * Complex.I * (((c * ((d : ℝ) * t ^ (d - 1))) : ℝ) : ℂ)) t := by
    simpa using (hu.ofReal_comp).const_mul (2 * Real.pi * Complex.I)
  simpa only [expTwoPiI_def] using hv.cexp

/-- Norm bound for the derivative of `t ↦ e(c t^d)` on `[0,1]`. -/
private lemma norm_deriv_expTwoPiI_pow_le (d : ℕ) (hd : 1 ≤ d) (c t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖expTwoPiI (c * t ^ d) *
        (2 * Real.pi * Complex.I * ((c * ((d : ℝ) * t ^ (d - 1)) : ℝ) : ℂ))‖
      ≤ 2 * Real.pi * d * |c| := by
  have hexp : ‖expTwoPiI (c * t ^ d)‖ = 1 := norm_expTwoPiI _
  have h2 : ‖2 * Real.pi * Complex.I * ((c * ((d : ℝ) * t ^ (d - 1)) : ℝ) : ℂ)‖
      = 2 * Real.pi * |c * ((d : ℝ) * t ^ (d - 1))| := by
    rw [show 2 * Real.pi * Complex.I * ((c * ((d : ℝ) * t ^ (d - 1)) : ℝ) : ℂ)
        = (((2 * Real.pi * (c * ((d : ℝ) * t ^ (d - 1))) : ℝ)) : ℂ) * Complex.I by
          push_cast; ring]
    rw [Complex.norm_mul, Complex.norm_I, mul_one,
        show ‖(((2 * Real.pi * (c * ((d : ℝ) * t ^ (d - 1))) : ℝ)) : ℂ)‖
            = |2 * Real.pi * (c * ((d : ℝ) * t ^ (d - 1)))| from RCLike.norm_ofReal _]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [Complex.norm_mul, hexp, one_mul, h2]
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have htd : t ^ (d - 1) ≤ 1 := by
    have h := pow_le_pow_left₀ ht0 ht1 (d - 1)
    rwa [one_pow] at h
  have hnn : (0 : ℝ) ≤ (d : ℝ) * t ^ (d - 1) := mul_nonneg hd0 (pow_nonneg ht0 _)
  have hdt : (d : ℝ) * t ^ (d - 1) ≤ (d : ℝ) := by
    calc (d : ℝ) * t ^ (d - 1) ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left htd hd0
      _ = (d : ℝ) := mul_one _
  calc 2 * Real.pi * |c * ((d : ℝ) * t ^ (d - 1))|
      = 2 * Real.pi * (|c| * ((d : ℝ) * t ^ (d - 1))) := by rw [abs_mul, abs_of_nonneg hnn]
    _ = |c| * (2 * Real.pi * ((d : ℝ) * t ^ (d - 1))) := by ring
    _ ≤ |c| * (2 * Real.pi * (d : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
        exact mul_le_mul_of_nonneg_left hdt (by positivity)
    _ = 2 * Real.pi * (d : ℝ) * |c| := by ring

/-- Comparison of the `β`-oscillating pure-power sum with its continuous analogue. -/
theorem sum_exp_pow_vs_integral (d : ℕ) (hd : 1 ≤ d) (P : ℕ) (hP : 0 < P) (c : ℝ) :
    ‖(P : ℂ)⁻¹ * ∑ p ∈ Finset.range P, expTwoPiI (c * (p : ℝ) ^ d)
      - ∫ s in (0 : ℝ)..1, expTwoPiI (c * (P : ℝ) ^ d * s ^ d)‖
    ≤ 2 * Real.pi * d * |c| * (P : ℝ) ^ (d - 1) := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hPpos
  have hpow : (P : ℝ) ^ d = (P : ℝ) * (P : ℝ) ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hsum : ∀ p : ℕ,
      expTwoPiI (c * (P : ℝ) ^ d * ((p : ℝ) / (P : ℝ)) ^ d) = expTwoPiI (c * (p : ℝ) ^ d) := by
    intro p
    congr 1
    rw [div_pow]
    field_simp
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => expTwoPiI (c * (P : ℝ) ^ d * t ^ d))
        (expTwoPiI (c * (P : ℝ) ^ d * t ^ d) *
          (2 * Real.pi * Complex.I *
            (((c * (P : ℝ) ^ d) * ((d : ℝ) * t ^ (d - 1)) : ℝ) : ℂ))) t :=
    fun t _ => hasDerivAt_expTwoPiI_pow d (c * (P : ℝ) ^ d) t
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTwoPiI (c * (P : ℝ) ^ d * t ^ d) *
          (2 * Real.pi * Complex.I *
            (((c * (P : ℝ) ^ d) * ((d : ℝ) * t ^ (d - 1)) : ℝ) : ℂ))‖
        ≤ 2 * Real.pi * d * |c * (P : ℝ) ^ d| :=
    fun t ht => norm_deriv_expTwoPiI_pow_le d hd (c * (P : ℝ) ^ d) t ht
  have hM : (0 : ℝ) ≤ 2 * Real.pi * d * |c * (P : ℝ) ^ d| := by positivity
  have hcom := Commons.Analysis.Integral.riemann_sum_sub_integral_le
    (fun t : ℝ => expTwoPiI (c * (P : ℝ) ^ d * t ^ d))
    (fun t : ℝ => expTwoPiI (c * (P : ℝ) ^ d * t ^ d) *
          (2 * Real.pi * Complex.I *
            (((c * (P : ℝ) ^ d) * ((d : ℝ) * t ^ (d - 1)) : ℝ) : ℂ)))
    hM hderiv hbound P hP
  rw [show (∑ p ∈ Finset.range P, expTwoPiI (c * (P : ℝ) ^ d * ((p : ℝ) / (P : ℝ)) ^ d))
      = ∑ p ∈ Finset.range P, expTwoPiI (c * (p : ℝ) ^ d) from
      Finset.sum_congr rfl (fun p _ => hsum p)] at hcom
  have hR : (2 * Real.pi * d * |c * (P : ℝ) ^ d|) / (P : ℝ)
      = 2 * Real.pi * d * |c| * (P : ℝ) ^ (d - 1) := by
    have habs : |c * (P : ℝ) ^ d| = |c| * (P : ℝ) ^ d := by
      rw [abs_mul]
      congr 1
      exact abs_of_nonneg (pow_nonneg (Nat.cast_nonneg P) d)
    rw [habs, hpow]
    field_simp
  exact le_trans hcom (le_of_eq hR)

/-! ## Bound for a single residue block -/

/-- Bound for a single residue block of the pure-power Weyl sum: the contribution of the
residue class `r mod q` to the major-arc sum differs from `(1/q) v_N(β)` by at most
`(4πd + 2πd/(d+1)) |β| (N+q)^d/N + 1/N`. -/
lemma pow_major_arc_block_bound
    (d N q r P : ℕ) (hd : 1 ≤ d) (β : ℝ) (hq : 1 ≤ q) (hN : 1 ≤ N) (hr : r < q)
    (hP1 : 1 ≤ P) (hPq_le : (P : ℝ) * q ≤ (N : ℝ) + q) (hPq_ge : (N : ℝ) - q ≤ (P : ℝ) * q) :
    ‖(N : ℂ)⁻¹ * (∑ p ∈ Finset.range P, expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d))
      - (q : ℂ)⁻¹ * (∫ s in (0 : ℝ)..1, expTwoPiI (β * (N : ℝ) ^ d * s ^ d))‖
    ≤ (4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β| * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ))
        + 1 / (N : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP1
  have hPc : (P : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hP0)
  have hM0 : (0 : ℝ) ≤ (N : ℝ) + (q : ℝ) := by positivity
  have hMd : ((N : ℝ) + (q : ℝ)) * ((N : ℝ) + (q : ℝ)) ^ (d - 1) = ((N : ℝ) + (q : ℝ)) ^ d := by
    conv_rhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hPd : (P : ℝ) ^ d = (P : ℝ) * (P : ℝ) ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
    ring
  set Y : ℝ := ((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ) with hY
  set A : ℂ := ∑ p ∈ Finset.range P, expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d) with hA
  set B : ℂ := ∑ p ∈ Finset.range P, expTwoPiI (β * (q : ℝ) ^ d * (p : ℝ) ^ d) with hB
  set v : ℂ := ∫ s in (0 : ℝ)..1, expTwoPiI (β * (N : ℝ) ^ d * s ^ d) with hv
  set u : ℂ := ∫ s in (0 : ℝ)..1, expTwoPiI (β * (q : ℝ) ^ d * (P : ℝ) ^ d * s ^ d) with hu
  set e : ℂ := (P : ℂ)⁻¹ * B - u with he
  set κ : ℂ := ((((P : ℝ) / (N : ℝ)) : ℝ) : ℂ) with hκ
  set lam : ℂ := (q : ℂ)⁻¹ with hlam
  have hNnorm : ‖(N : ℂ)⁻¹‖ = 1 / (N : ℝ) := by rw [norm_inv, Complex.norm_natCast, one_div]
  have hsplit : (N : ℂ)⁻¹ * A - (q : ℂ)⁻¹ * v
      = ((N : ℂ)⁻¹ * A - (N : ℂ)⁻¹ * B) + ((N : ℂ)⁻¹ * B - (q : ℂ)⁻¹ * v) := by ring
  have hnorm : ‖(N : ℂ)⁻¹ * A - (q : ℂ)⁻¹ * v‖
      ≤ ‖(N : ℂ)⁻¹ * A - (N : ℂ)⁻¹ * B‖ + ‖(N : ℂ)⁻¹ * B - (q : ℂ)⁻¹ * v‖ := by
    rw [hsplit]; exact norm_add_le _ _
  -- PART 1: compare A (the block sum) with B (the pure `q^d p^d` sum).
  have hpq_le : ∀ p : ℕ, p < P → (p : ℝ) * q ≤ (N : ℝ) := by
    intro p hp
    have hp1 : p ≤ P - 1 := by omega
    have h2 : (p : ℝ) ≤ ((P - 1 : ℕ) : ℝ) := by exact_mod_cast hp1
    rw [Nat.cast_sub hP1] at h2; push_cast at h2
    nlinarith [hPq_le]
  have hAB : ‖A - B‖ ≤ 2 * Real.pi * d * |β| * ((N : ℝ) + (q : ℝ)) ^ d := by
    have hper : ∀ p ∈ Finset.range P,
        ‖expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)
          - expTwoPiI (β * (q : ℝ) ^ d * (p : ℝ) ^ d)‖
          ≤ 2 * Real.pi * |β| * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1)) := by
      intro p hp
      have hpP : p < P := Finset.mem_range.mp hp
      have hpq := hpq_le p hpP
      have hpqr0 : (0 : ℝ) ≤ ((p * q + r : ℕ) : ℝ) := by positivity
      have hpq0' : (0 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by positivity
      have hrq : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_lt hr
      have hpqr_le : ((p * q + r : ℕ) : ℝ) ≤ (N : ℝ) + (q : ℝ) := by
        push_cast; linarith
      have hpq_le' : ((p * q : ℕ) : ℝ) ≤ (N : ℝ) + (q : ℝ) := by push_cast; linarith
      have hbd : |(((p * q + r : ℕ) : ℝ)) ^ d - (((p * q : ℕ) : ℝ)) ^ d|
          ≤ (q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1) := by
        have h1 := abs_pow_sub_pow_le ((p * q + r : ℕ) : ℝ) ((p * q : ℕ) : ℝ) d
        have hmax : max |((p * q + r : ℕ) : ℝ)| |((p * q : ℕ) : ℝ)| ≤ (N : ℝ) + (q : ℝ) := by
          rw [max_le_iff, abs_of_nonneg hpqr0, abs_of_nonneg hpq0']
          exact ⟨hpqr_le, hpq_le'⟩
        calc |(((p * q + r : ℕ) : ℝ)) ^ d - (((p * q : ℕ) : ℝ)) ^ d|
            ≤ |((p * q + r : ℕ) : ℝ) - ((p * q : ℕ) : ℝ)| * (d : ℝ)
                * (max |((p * q + r : ℕ) : ℝ)| |((p * q : ℕ) : ℝ)|) ^ (d - 1) := h1
          _ ≤ (q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1) := by
              have hdiff : |((p * q + r : ℕ) : ℝ) - ((p * q : ℕ) : ℝ)| = (r : ℝ) := by
                rw [show ((p * q + r : ℕ) : ℝ) - ((p * q : ℕ) : ℝ) = (r : ℝ) by push_cast; ring,
                  abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ))]
              rw [hdiff]
              have hdq : (0 : ℝ) ≤ (d : ℝ) := by positivity
              have hmaxpow : (max |((p * q + r : ℕ) : ℝ)| |((p * q : ℕ) : ℝ)|) ^ (d - 1)
                  ≤ ((N : ℝ) + (q : ℝ)) ^ (d - 1) :=
                pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax (d - 1)
              exact mul_le_mul (mul_le_mul_of_nonneg_right hrq hdq) hmaxpow
                (pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _) (by positivity)
      calc ‖expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)
            - expTwoPiI (β * (q : ℝ) ^ d * (p : ℝ) ^ d)‖
          ≤ 2 * Real.pi * |β * (((p * q + r : ℕ) : ℝ)) ^ d - β * (q : ℝ) ^ d * (p : ℝ) ^ d| :=
            norm_expTwoPiI_sub_le _ _
        _ = 2 * Real.pi * |β| * |(((p * q + r : ℕ) : ℝ)) ^ d - (((p * q : ℕ) : ℝ)) ^ d| := by
            have hqpd : β * (q : ℝ) ^ d * (p : ℝ) ^ d = β * (((p * q : ℕ) : ℝ)) ^ d := by
              rw [show β * (q : ℝ) ^ d * (p : ℝ) ^ d = β * ((q : ℝ) ^ d * (p : ℝ) ^ d) by ring,
                ← mul_pow]
              push_cast; ring
            rw [show β * (((p * q + r : ℕ) : ℝ)) ^ d - β * (q : ℝ) ^ d * (p : ℝ) ^ d
                = β * ((((p * q + r : ℕ) : ℝ)) ^ d - (((p * q : ℕ) : ℝ)) ^ d) by
                  rw [hqpd]; ring,
              abs_mul]
            ring
        _ ≤ 2 * Real.pi * |β| * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1)) := by
            apply mul_le_mul_of_nonneg_left hbd (by positivity)
    calc ‖A - B‖
        = ‖∑ p ∈ Finset.range P, (expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)
            - expTwoPiI (β * (q : ℝ) ^ d * (p : ℝ) ^ d))‖ := by
          rw [hA, hB, Finset.sum_sub_distrib]
      _ ≤ ∑ p ∈ Finset.range P, ‖expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)
            - expTwoPiI (β * (q : ℝ) ^ d * (p : ℝ) ^ d)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.range P,
            2 * Real.pi * |β| * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1)) :=
          Finset.sum_le_sum hper
      _ = (P : ℝ) * (2 * Real.pi * |β| * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 2 * Real.pi * d * |β| * ((N : ℝ) + (q : ℝ)) ^ d := by
          have hdq : (0 : ℝ) ≤ (d : ℝ) := by positivity
          have hMp : (0 : ℝ) ≤ ((N : ℝ) + (q : ℝ)) ^ (d - 1) := pow_nonneg hM0 _
          calc (P : ℝ) * (2 * Real.pi * |β| * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1)))
              = 2 * Real.pi * |β| * (((P : ℝ) * (q : ℝ)) * ((d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1))) := by ring
            _ ≤ 2 * Real.pi * |β| * (((N : ℝ) + (q : ℝ)) * ((d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_right hPq_le (mul_nonneg hdq hMp)
            _ = 2 * Real.pi * d * |β| * ((N : ℝ) + (q : ℝ)) ^ d := by rw [← hMd]; ring
  have hpart1 : ‖(N : ℂ)⁻¹ * A - (N : ℂ)⁻¹ * B‖ ≤ 2 * Real.pi * d * |β| * Y := by
    rw [hY]
    calc ‖(N : ℂ)⁻¹ * A - (N : ℂ)⁻¹ * B‖ = ‖(N : ℂ)⁻¹‖ * ‖A - B‖ := by rw [← mul_sub, norm_mul]
      _ = (1 / (N : ℝ)) * ‖A - B‖ := by rw [hNnorm]
      _ ≤ (1 / (N : ℝ)) * (2 * Real.pi * d * |β| * ((N : ℝ) + (q : ℝ)) ^ d) :=
          mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = 2 * Real.pi * d * |β| * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) := by ring
  -- PART 2: replace `(P)⁻¹ B` by the integral `u`, then `u` by `v`.
  have hκeq : κ = (P : ℂ) * (N : ℂ)⁻¹ := by rw [hκ]; push_cast; rw [div_eq_mul_inv]
  have hkey1 : (N : ℂ)⁻¹ * B = κ * ((P : ℂ)⁻¹ * B) := by
    rw [hκeq]
    rw [show (P : ℂ) * (N : ℂ)⁻¹ * ((P : ℂ)⁻¹ * B) = (N : ℂ)⁻¹ * B by
      calc (P : ℂ) * (N : ℂ)⁻¹ * ((P : ℂ)⁻¹ * B)
          = (N : ℂ)⁻¹ * ((P : ℂ) * (P : ℂ)⁻¹) * B := by ring
        _ = (N : ℂ)⁻¹ * B := by rw [mul_inv_cancel₀ hPc]; ring]
  have hqinvcast : (q : ℂ)⁻¹ = (((q : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [show (q : ℂ) = ((q : ℝ) : ℂ) by exact Complex.ofReal_natCast q]
    exact (Complex.ofReal_inv (q : ℝ)).symm
  have hlamnorm : ‖lam‖ = 1 / (q : ℝ) := by rw [hlam, norm_inv, Complex.norm_natCast, one_div]
  have hκnorm : ‖κ‖ = (P : ℝ) / (N : ℝ) := by
    have h : ‖κ‖ = |(((P : ℝ) / (N : ℝ)) : ℝ)| := by rw [hκ]; exact RCLike.norm_ofReal _
    rw [h, abs_of_nonneg (by positivity)]
  have hdecomp : (N : ℂ)⁻¹ * B - (q : ℂ)⁻¹ * v = (κ - lam) * u + lam * (u - v) + κ * e := by
    rw [hkey1, he, hlam]; ring
  have hδ : ‖κ - lam‖ ≤ 1 / (N : ℝ) := by
    have hδeq : κ - lam = ((((P : ℝ) / (N : ℝ) - (1 : ℝ) / (q : ℝ)) : ℝ) : ℂ) := by
      rw [hκ, hlam, hqinvcast]; push_cast; ring
    have hδn : ‖κ - lam‖ = |(((P : ℝ) / (N : ℝ) - (1 : ℝ) / (q : ℝ)) : ℝ)| := by
      rw [hδeq]; exact RCLike.norm_ofReal _
    rw [hδn]
    have h1 : (P : ℝ) / (N : ℝ) - (1 : ℝ) / (q : ℝ)
        = ((P : ℝ) * (q : ℝ) - (N : ℝ)) / ((N : ℝ) * (q : ℝ)) := by field_simp
    rw [h1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) * (q : ℝ))]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have habs : |(P : ℝ) * (q : ℝ) - (N : ℝ)| ≤ (q : ℝ) :=
      abs_le.mpr ⟨by linarith [hPq_ge], by linarith [hPq_le]⟩
    nlinarith [habs]
  have hpiece1 : ‖(κ - lam) * u‖ ≤ 1 / (N : ℝ) := by
    rw [norm_mul]
    calc ‖κ - lam‖ * ‖u‖ ≤ (1 / (N : ℝ)) * 1 :=
          mul_le_mul hδ (norm_integral_expTwoPiI_pow_le d (β * (q : ℝ) ^ d * (P : ℝ) ^ d))
            (norm_nonneg _) (by positivity)
      _ = 1 / (N : ℝ) := by ring
  have huv : ‖u - v‖
      ≤ (2 * Real.pi / (d + 1)) * |β| * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1)) := by
    have h1 : ‖u - v‖ ≤ 2 * Real.pi * |β * (q : ℝ) ^ d * (P : ℝ) ^ d - β * (N : ℝ) ^ d| / (d + 1) := by
      rw [hu, hv]
      exact norm_integral_expTwoPiI_pow_sub_le d (β * (q : ℝ) ^ d * (P : ℝ) ^ d) (β * (N : ℝ) ^ d)
    have h2 : |β * (q : ℝ) ^ d * (P : ℝ) ^ d - β * (N : ℝ) ^ d|
        = |β| * |(q : ℝ) ^ d * (P : ℝ) ^ d - (N : ℝ) ^ d| := by
      rw [show β * (q : ℝ) ^ d * (P : ℝ) ^ d - β * (N : ℝ) ^ d
          = β * ((q : ℝ) ^ d * (P : ℝ) ^ d - (N : ℝ) ^ d) by ring, abs_mul]
    have h3 : |(q : ℝ) ^ d * (P : ℝ) ^ d - (N : ℝ) ^ d|
        ≤ (q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1) := by
      have hqp : (q : ℝ) ^ d * (P : ℝ) ^ d = ((q : ℝ) * (P : ℝ)) ^ d := by rw [mul_pow]
      rw [hqp]
      have h1 := abs_pow_sub_pow_le ((q : ℝ) * (P : ℝ)) (N : ℝ) d
      have hqP0 : (0 : ℝ) ≤ (q : ℝ) * (P : ℝ) := by positivity
      have hmax : max |(q : ℝ) * (P : ℝ)| |(N : ℝ)| ≤ (N : ℝ) + (q : ℝ) := by
        rw [max_le_iff, abs_of_nonneg hqP0, abs_of_nonneg (le_of_lt hN0)]
        exact ⟨by linarith [hPq_le], by linarith⟩
      have hqPm : |(q : ℝ) * (P : ℝ) - (N : ℝ)| ≤ (q : ℝ) :=
        abs_le.mpr ⟨by linarith [hPq_ge], by linarith [hPq_le]⟩
      have hmaxpow : (max |(q : ℝ) * (P : ℝ)| |(N : ℝ)|) ^ (d - 1)
          ≤ ((N : ℝ) + (q : ℝ)) ^ (d - 1) :=
        pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax (d - 1)
      calc |((q : ℝ) * (P : ℝ)) ^ d - (N : ℝ) ^ d|
          ≤ |(q : ℝ) * (P : ℝ) - (N : ℝ)| * (d : ℝ)
              * (max |(q : ℝ) * (P : ℝ)| |(N : ℝ)|) ^ (d - 1) := h1
        _ ≤ (q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1) := by
            have hdq : (0 : ℝ) ≤ (d : ℝ) := by positivity
            exact mul_le_mul (mul_le_mul_of_nonneg_right hqPm hdq) hmaxpow
              (pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _) (by positivity)
    calc ‖u - v‖ ≤ 2 * Real.pi * |β * (q : ℝ) ^ d * (P : ℝ) ^ d - β * (N : ℝ) ^ d| / (d + 1) := h1
      _ = 2 * Real.pi * |β| * |(q : ℝ) ^ d * (P : ℝ) ^ d - (N : ℝ) ^ d| / (d + 1) := by rw [h2]; ring
      _ = (2 * Real.pi * |β| / (d + 1)) * |(q : ℝ) ^ d * (P : ℝ) ^ d - (N : ℝ) ^ d| := by ring
      _ ≤ (2 * Real.pi * |β| / (d + 1)) * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1)) := by
          apply mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (2 * Real.pi / (d + 1)) * |β| * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1)) := by ring
  have hpiece2 : ‖lam * (u - v)‖ ≤ (2 * Real.pi * d / (d + 1)) * |β| * Y := by
    rw [norm_mul, hlamnorm, hY]
    calc (1 / (q : ℝ)) * ‖u - v‖
        ≤ (1 / (q : ℝ)) * ((2 * Real.pi / (d + 1)) * |β|
            * ((q : ℝ) * (d : ℝ) * ((N : ℝ) + (q : ℝ)) ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left huv (by positivity)
      _ = (2 * Real.pi * d / (d + 1)) * |β| * ((N : ℝ) + (q : ℝ)) ^ (d - 1) := by
          field_simp
      _ ≤ (2 * Real.pi * d / (d + 1)) * |β| * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [le_div_iff₀ hN0, ← hMd, mul_comm (((N : ℝ) + (q : ℝ)) ^ (d - 1)) (N : ℝ)]
          have hMp : (0 : ℝ) ≤ ((N : ℝ) + (q : ℝ)) ^ (d - 1) := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith) hMp
  have he_bd : ‖e‖ ≤ 2 * Real.pi * d * |β| * (q : ℝ) ^ d * (P : ℝ) ^ (d - 1) := by
    rw [he]
    have h := sum_exp_pow_vs_integral d hd P hP1 (β * (q : ℝ) ^ d)
    have habs : |β * (q : ℝ) ^ d| = |β| * (q : ℝ) ^ d := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ)) d)]
    rw [habs] at h
    simpa only [hB, hu, mul_assoc] using h
  have hpiece3 : ‖κ * e‖ ≤ 2 * Real.pi * d * |β| * Y := by
    rw [norm_mul, hκnorm, hY]
    calc (P : ℝ) / (N : ℝ) * ‖e‖
        ≤ ((P : ℝ) / (N : ℝ)) * (2 * Real.pi * d * |β| * (q : ℝ) ^ d * (P : ℝ) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left he_bd (by positivity)
      _ = 2 * Real.pi * d * |β| * ((((P : ℝ) * (q : ℝ)) ^ d) / (N : ℝ)) := by
          rw [mul_pow, hPd]
          field_simp
      _ ≤ 2 * Real.pi * d * |β| * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ (le_of_lt hN0)
          exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (P : ℝ) * (q : ℝ)) hPq_le d
  have hpart2 : ‖(N : ℂ)⁻¹ * B - (q : ℂ)⁻¹ * v‖
      ≤ (2 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β| * Y + 1 / (N : ℝ) := by
    rw [hdecomp]
    calc ‖(κ - lam) * u + lam * (u - v) + κ * e‖
        ≤ ‖(κ - lam) * u + lam * (u - v)‖ + ‖κ * e‖ := norm_add_le _ _
      _ ≤ (‖(κ - lam) * u‖ + ‖lam * (u - v)‖) + ‖κ * e‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (1 / (N : ℝ) + (2 * Real.pi * d / (d + 1)) * |β| * Y) + 2 * Real.pi * d * |β| * Y :=
          add_le_add (add_le_add hpiece1 hpiece2) hpiece3
      _ = (2 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β| * Y + 1 / (N : ℝ) := by ring
  calc ‖(N : ℂ)⁻¹ * A - (q : ℂ)⁻¹ * v‖
      ≤ ‖(N : ℂ)⁻¹ * A - (N : ℂ)⁻¹ * B‖ + ‖(N : ℂ)⁻¹ * B - (q : ℂ)⁻¹ * v‖ := hnorm
    _ ≤ 2 * Real.pi * d * |β| * Y + ((2 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β| * Y + 1 / (N : ℝ)) :=
        add_le_add hpart1 hpart2
    _ = (4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β| * Y + 1 / (N : ℝ) := by ring

/-- **Major-arc approximation for the pure-power Weyl sum `∑_{n<N} e(α n^d)`.**  Writing
`α = a/q + β`, the normalized sum is, up to an explicit error, the product of the complete
`d`-th power Gauss-type sum `q⁻¹ ∑_{r<q} e(a r^d/q)` with the oscillatory integral
`∫_0^1 e(β N^d s^d) ds`.

The proof is the residue-class factorisation `n = p q + r`: the phase
`α n^d = (a/q + β)(pq+r)^d` splits as `a r^d/q` plus a phase whose `p`-dependence is
`β (q p)^d` up to corrections of size `β q^{d-1}p^{d-1}r`, and the `p`-sum is compared with
its continuous analogue (a Riemann sum with mesh `q`, derivative bound
`2π d |β| (N+q)^{d-1}`).  The two error sources are the Riemann-sum error
`≈ |β| q (N+q)^d / N` and the endpoint discrepancy `≈ q/N`. -/
theorem pure_power_major_arc_approx (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q : ℕ) (a : ℤ) (β : ℝ), 1 ≤ q → 1 ≤ N →
      ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d : ℝ) : ℂ)))
          - (q : ℂ)⁻¹ * (∑ r ∈ Finset.range q,
                Complex.exp (2 * Real.pi * Complex.I *
                  (((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d : ℝ) : ℂ)))
              * (∫ s in (0 : ℝ)..1,
                  Complex.exp (2 * Real.pi * Complex.I *
                    ((β * (N : ℝ) ^ d * s ^ d : ℝ) : ℂ)))‖
        ≤ C * (|β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ) + (q : ℝ) / (N : ℝ)) := by
  refine ⟨6 * Real.pi * d + 2, by positivity, ?_⟩
  intro N q a β hq hN
  have hd1 : 1 ≤ d := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hCpos : (0 : ℝ) < 6 * Real.pi * d + 2 := by positivity
  change ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d))
      - (q : ℂ)⁻¹ * (∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d))
        * (∫ s in (0 : ℝ)..1, expTwoPiI (β * (N : ℝ) ^ d * s ^ d))‖
      ≤ (6 * Real.pi * d + 2) * (|β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ) + (q : ℝ) / (N : ℝ))
  set S : ℂ := ∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d) with hS
  set G : ℂ := ∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d) with hG
  set v : ℂ := ∫ s in (0 : ℝ)..1, expTwoPiI (β * (N : ℝ) ^ d * s ^ d) with hv
  set T : ℝ := |β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ) + (q : ℝ) / (N : ℝ) with hT
  have hNnorm : ‖(N : ℂ)⁻¹‖ = 1 / (N : ℝ) := by rw [norm_inv, Complex.norm_natCast, one_div]
  have hqnorm : ‖(q : ℂ)⁻¹‖ = 1 / (q : ℝ) := by rw [norm_inv, Complex.norm_natCast, one_div]
  by_cases hqN : q ≤ N
  · have hq0 : 0 < q := by omega
    have hTY : T = |β| * (q : ℝ) * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) + (q : ℝ) / (N : ℝ) := by
      rw [hT]; ring
    have hfac : S = ∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)
        * ∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d) := by
      rw [hS]; exact pow_phase_residue_factor d N q hq0 a β
    have hGv : (q : ℂ)⁻¹ * G * v
        = ∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d) * ((q : ℂ)⁻¹ * v) := by
      rw [hG, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun r hr => ?_); ring
    have hblock : ∀ r ∈ Finset.range q,
        ‖(N : ℂ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
              expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)) - (q : ℂ)⁻¹ * v‖
        ≤ (4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β| * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ))
            + 1 / (N : ℝ) := by
      intro r hr
      have hrq : r < q := Finset.mem_range.mp hr
      have hb := div_block_bounds hq hrq hqN
      rw [hv]
      exact pow_major_arc_block_bound d N q r ((N + q - 1 - r) / q) hd1 β hq hN hrq hb.1 hb.2.1 hb.2.2
    have hsum_eq : (N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v
        = ∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)
            * ((N : ℂ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
                expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)) - (q : ℂ)⁻¹ * v) := by
      rw [hfac, hGv, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun r hr => ?_); ring
    have hmain : ‖(N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v‖
        ≤ (q : ℝ) * ((4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β| * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ))
            + 1 / (N : ℝ)) := by
      rw [hsum_eq]
      calc ‖∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)
              * ((N : ℂ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
                  expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)) - (q : ℂ)⁻¹ * v)‖
          ≤ ∑ r ∈ Finset.range q, ‖expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)
              * ((N : ℂ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
                  expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)) - (q : ℂ)⁻¹ * v)‖ := norm_sum_le _ _
        _ = ∑ r ∈ Finset.range q, ‖(N : ℂ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
              expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ d)) - (q : ℂ)⁻¹ * v‖ := by
            refine Finset.sum_congr rfl (fun r hr => ?_)
            rw [norm_mul, norm_expTwoPiI, one_mul]
        _ ≤ ∑ r ∈ Finset.range q, ((4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β|
              * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) + 1 / (N : ℝ)) := Finset.sum_le_sum hblock
        _ = (q : ℝ) * ((4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β|
              * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) + 1 / (N : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ‖(N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v‖
        ≤ (q : ℝ) * ((4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β|
              * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) + 1 / (N : ℝ)) := hmain
      _ ≤ (6 * Real.pi * d + 2) * T := by
          rw [hTY]
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
          have hden : (0 : ℝ) < (d : ℝ) + 1 := by positivity
          have hK : 4 * Real.pi * d + 2 * Real.pi * d / (d + 1) ≤ 6 * Real.pi * d + 2 := by
            have hnum : (0 : ℝ) ≤ 2 * Real.pi * d := by positivity
            have hmul : (0 : ℝ) ≤ (2 * Real.pi * d) * (d : ℝ) := mul_nonneg hnum hd0
            have hb : 2 * Real.pi * d / (d + 1) ≤ 2 * Real.pi * d := by
              rw [div_le_iff₀ hden]
              nlinarith [hmul]
            linarith
          have hY : (0 : ℝ) ≤ |β| * (q : ℝ) * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) := by positivity
          have hqN0 : (0 : ℝ) ≤ (q : ℝ) / (N : ℝ) := by positivity
          have hC6 : (1 : ℝ) ≤ 6 * Real.pi * d + 2 := by nlinarith [Real.pi_pos, hd0]
          have hqq : (q : ℝ) / (N : ℝ) ≤ (6 * Real.pi * d + 2) * ((q : ℝ) / (N : ℝ)) :=
            le_mul_of_one_le_left hqN0 hC6
          calc (q : ℝ) * ((4 * Real.pi * d + 2 * Real.pi * d / (d + 1)) * |β|
                  * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) + 1 / (N : ℝ))
              = (4 * Real.pi * d + 2 * Real.pi * d / (d + 1))
                  * (|β| * (q : ℝ) * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ))) + (q : ℝ) / (N : ℝ) := by ring
            _ ≤ (6 * Real.pi * d + 2) * (|β| * (q : ℝ) * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)))
                  + (6 * Real.pi * d + 2) * ((q : ℝ) / (N : ℝ)) :=
                add_le_add (mul_le_mul_of_nonneg_right hK hY) hqq
            _ = (6 * Real.pi * d + 2)
                  * (|β| * (q : ℝ) * (((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ)) + (q : ℝ) / (N : ℝ)) := by ring
  · have hNq : (N : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : N < q)
    have hSle : ‖S‖ ≤ (N : ℝ) := by
      rw [hS]
      calc ‖∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d)‖
          ≤ ∑ n ∈ Finset.range N, ‖expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d)‖ := norm_sum_le _ _
        _ = (N : ℝ) := by simp [norm_expTwoPiI]
    have hGle : ‖G‖ ≤ (q : ℝ) := by
      rw [hG]
      calc ‖∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)‖
          ≤ ∑ r ∈ Finset.range q, ‖expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d)‖ := norm_sum_le _ _
        _ = (q : ℝ) := by simp [norm_expTwoPiI]
    have hvle : ‖v‖ ≤ 1 := by rw [hv]; exact norm_integral_expTwoPiI_pow_le d _
    have h1 : ‖(N : ℂ)⁻¹ * S‖ ≤ 1 := by
      rw [norm_mul, hNnorm]
      calc (1 / (N : ℝ)) * ‖S‖ ≤ (1 / (N : ℝ)) * (N : ℝ) := mul_le_mul_of_nonneg_left hSle (by positivity)
        _ = 1 := by field_simp
    have h2 : ‖(q : ℂ)⁻¹ * G * v‖ ≤ 1 := by
      have hstep : ‖(q : ℂ)⁻¹ * G * v‖ = (1 / (q : ℝ)) * ‖G‖ * ‖v‖ := by rw [norm_mul, norm_mul, hqnorm]
      rw [hstep]
      calc (1 / (q : ℝ)) * ‖G‖ * ‖v‖ ≤ (1 / (q : ℝ)) * (q : ℝ) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hGle (by positivity)) hvle (norm_nonneg _) (by positivity)
        _ = 1 := by field_simp
    calc ‖(N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v‖ ≤ ‖(N : ℂ)⁻¹ * S‖ + ‖(q : ℂ)⁻¹ * G * v‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
      _ ≤ (6 * Real.pi * d + 2) * T := by
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
          have h1q : 1 < (q : ℝ) / (N : ℝ) := by rw [lt_div_iff₀ hNpos]; linarith
          have hTge : (q : ℝ) / (N : ℝ) ≤ T := by
            rw [hT]
            have : (0 : ℝ) ≤ |β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ) := by positivity
            linarith
          have hC2 : (2 : ℝ) ≤ 6 * Real.pi * d + 2 := by nlinarith [Real.pi_pos, hd0]
          nlinarith [hTge, h1q, hC2, hCpos]

end Commons.Analysis.ExponentialSums
