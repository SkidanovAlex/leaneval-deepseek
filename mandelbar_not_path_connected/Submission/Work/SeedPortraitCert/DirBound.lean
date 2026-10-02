/-
# SeedPortraitCert — the ten base ray directions of the certificate

Area `Submission/Work/SeedPortraitCert/`.  The chain certificate needs, for each of the ten angle
classes `angP j` (`j < 10`), the fact that the *exact* direction `e^{2πi θ_j}` of the external ray
is within `10⁻⁴` of the rational model `qdirP j` emitted by the generator (the mantissas
`dirBaseP` at scale `2 ^ 40`).

This is the `/33`-denominator analogue of `Work.SeedCertRay.dir_bound` and
`Work.TripodCert.dirBoundT`; the proof is the same rigorous, kernel-checked numerical
computation.  Writing `x = 2πi·(m/33)` (so that `rayDirection (m/33) = exp x`) and
`w = 2π*i·(m/33)` with the 20-digit rational `π* = 3.14159265358979323846`:

* `‖exp x - Etrunc x‖ ≤ 1/40000` — the `24`-term Taylor remainder at `‖x‖ ≤ 61/10`
  (`m ≤ 32`, so `2π·32/33 ≈ 6.091 < 6.1`);
* `‖Etrunc x - Etrunc w‖ ≤ ‖x - w‖ · 500` — the polynomial difference, `‖x - w‖` tiny by
  `|π - π*| ≤ 10⁻²⁰`;
* `‖Etrunc w - qdirP j‖ ≤ 1/50000` — the *rational* part: `Work.SeedCertRay.taylor_split` splits
  the partial sum of `exp (i t)` into its real (even) and imaginary (odd) parts, evaluated in
  exact rational arithmetic by `norm_num` (`dirnumP_re_j`, `dirnumP_im_j`).

The total `1/40000 + 10⁻⁵ + 1/50000 < 10⁻⁴` gives the claim. -/
import Mathlib
import Submission.Work.SeedPortraitCert.Data
import Submission.Work.SeedPortraitCert.Angles
import Submission.Work.SeedCertRay.dir_bound
import Submission.Work.SeedCertRay.norm_sum_taylor_diff_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay

noncomputable section

/-! ## The rational model of the angle denominator -/

/-- The model exponent `2 π* m / 33` of the angle `m/33`. -/
def tq33 (m : ℕ) : ℝ := 2 * (piq : ℝ) * m / 33

/-! ## The Taylor remainder at `‖z‖ ≤ 61/10` -/

/-- The `24`-term Taylor polynomial of `exp` is `1/40000`-close to `exp` on the disc
`‖z‖ ≤ 61/10`. -/
theorem exp_taylor_truncP {z : ℂ} (hz : ‖z‖ ≤ 61 / 10) :
    ‖Complex.exp z - Etrunc z‖ ≤ (1 / 40000 : ℝ) := by
  have harg : ‖z‖ / (25 : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 25)]
    linarith
  have h := Complex.exp_bound' (x := z) (n := 24) harg
  have hE : (∑ m ∈ Finset.range 24, z ^ m / ((m.factorial : ℕ) : ℂ)) = Etrunc z := by
    simp [Etrunc]
  rw [hE] at h
  refine h.trans ?_
  have hnum : ‖z‖ ^ 24 / ((24 : ℕ).factorial : ℝ) * 2 ≤ (1 / 40000 : ℝ) := by
    calc ‖z‖ ^ 24 / ((24 : ℕ).factorial : ℝ) * 2
        ≤ (61 / 10) ^ 24 / ((24 : ℕ).factorial : ℝ) * 2 := by gcongr
      _ ≤ (1 / 40000 : ℝ) := by norm_num
  exact hnum

/-! ## The Lipschitz bound on the `24`-term Taylor sum -/

/-- Difference of powers bound (the `M`-parametric form of
`Work.SeedCertRay.norm_pow_sub_pow_le`). -/
private lemma norm_pow_sub_pow_leP (z w : ℂ) {M : ℝ} (hM : 0 ≤ M) (hz : ‖z‖ ≤ M)
    (hw : ‖w‖ ≤ M) : ∀ k : ℕ, ‖z^(k+1) - w^(k+1)‖ ≤ ‖z - w‖ * ((k:ℝ)+1) * M^k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : z^(k+1+1) - w^(k+1+1) = z*(z^(k+1) - w^(k+1)) + (z - w)*w^(k+1) := by ring
    rw [h1]
    have step1 : ‖z * (z ^ (k + 1) - w ^ (k + 1)) + (z - w) * w ^ (k + 1)‖
        ≤ ‖z‖ * ‖z ^ (k + 1) - w ^ (k + 1)‖ + ‖z - w‖ * ‖w ^ (k + 1)‖ := by
      calc ‖z * (z^(k+1) - w^(k+1)) + (z - w)*w^(k+1)‖
          ≤ ‖z * (z^(k+1) - w^(k+1))‖ + ‖(z - w)*w^(k+1)‖ := norm_add_le _ _
        _ = ‖z‖ * ‖z^(k+1) - w^(k+1)‖ + ‖z - w‖ * ‖w^(k+1)‖ := by rw [norm_mul, norm_mul]
    refine le_trans step1 ?_
    have hA : ‖z ^ (k + 1) - w ^ (k + 1)‖ ≤ ‖z - w‖ * ((k:ℝ)+1) * M^k := ih
    have hB : ‖w^(k+1)‖ ≤ M^(k+1) := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg w) hw (k+1)
    have hm1 : ‖z‖ * ‖z^(k+1)-w^(k+1)‖ ≤ M * (‖z-w‖ * ((k:ℝ)+1) * M^k) :=
      mul_le_mul hz hA (norm_nonneg _) hM
    have hm2 : ‖z-w‖ * ‖w^(k+1)‖ ≤ ‖z-w‖ * M^(k+1) :=
      mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    refine le_trans (add_le_add hm1 hm2) ?_
    have key : M * (‖z - w‖ * ((k:ℝ)+1) * M^k) + ‖z - w‖ * M^(k+1)
        = ‖z - w‖ * (((k+1 : ℕ) : ℝ) + 1) * M^(k+1) := by
      push_cast
      ring
    exact le_of_eq key

/-- Termwise Taylor bound at `M = 61/10`. -/
private lemma norm_taylor_term_leP (z w : ℂ) (hz : ‖z‖ ≤ 61/10) (hw : ‖w‖ ≤ 61/10) (k : ℕ) :
    ‖(z^(k+1) - w^(k+1)) / (((k+1).factorial : ℕ) : ℂ)‖
      ≤ ‖z - w‖ * ((61/10)^k / ((k.factorial : ℝ))) := by
  have hM : (0:ℝ) ≤ 61/10 := by norm_num
  have h := norm_pow_sub_pow_leP z w hM hz hw k
  rw [norm_div, Complex.norm_natCast]
  have hfac : (((k+1).factorial : ℕ) : ℝ) = ((k:ℝ)+1) * ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring
  rw [hfac]
  calc ‖z ^ (k + 1) - w ^ (k + 1)‖ / (((k:ℝ)+1) * ((k.factorial : ℕ) : ℝ))
      ≤ (‖z - w‖ * ((k:ℝ)+1) * (61/10)^k) / (((k:ℝ)+1) * ((k.factorial : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right h (by positivity)
    _ = ‖z - w‖ * ((61/10)^k / ((k.factorial : ℕ) : ℝ)) := by
        field_simp

/-- Partial Taylor-sum difference bound at `M = 61/10`: on the disc of radius `61/10` the first
`24` Taylor terms of `exp` are Lipschitz with constant `500`. -/
theorem norm_sum_taylor_diff_leP {z w : ℂ} (hz : ‖z‖ ≤ 61/10) (hw : ‖w‖ ≤ 61/10) :
    ‖∑ k ∈ Finset.range 24, (z^k - w^k) / ((k.factorial : ℕ) : ℂ)‖ ≤ ‖z - w‖ * 500 := by
  have h1 : ‖∑ k ∈ Finset.range 24, (z^k - w^k)/((k.factorial : ℕ):ℂ)‖
      ≤ ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1)) / (((k+1).factorial : ℕ) : ℂ)‖ := by
    calc ‖∑ k ∈ Finset.range 24, (z^k - w^k)/((k.factorial:ℕ):ℂ)‖
        ≤ ∑ k ∈ Finset.range 24, ‖(z^k - w^k)/((k.factorial:ℕ):ℂ)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1))/(((k+1).factorial:ℕ):ℂ)‖
            + ‖(z^0 - w^0)/(((0).factorial:ℕ):ℂ)‖ := by rw [Finset.sum_range_succ']
      _ = ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1))/(((k+1).factorial:ℕ):ℂ)‖ := by simp
  refine le_trans h1 ?_
  have h2 : ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1))/(((k+1).factorial:ℕ):ℂ)‖
      ≤ ∑ k ∈ Finset.range 23, ‖z - w‖ * ((61/10)^k / ((k.factorial:ℕ):ℝ)) :=
    Finset.sum_le_sum (fun k _ => norm_taylor_term_leP z w hz hw k)
  refine le_trans h2 ?_
  have h3 : ∑ k ∈ Finset.range 23, ‖z - w‖ * ((61/10)^k / ((k.factorial:ℕ):ℝ))
      = ‖z - w‖ * ∑ k ∈ Finset.range 23, (61/10)^k / ((k.factorial:ℕ):ℝ) := by
    rw [Finset.mul_sum]
  rw [h3]
  have h4 : (∑ k ∈ Finset.range 23, ((61:ℝ)/10)^k / ((k.factorial:ℕ):ℝ)) ≤ 500 := by norm_num
  exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

/-! ## The abstract step: a rational model direction is close to the true one -/

/-- If the real and imaginary parts of the `24`-term Taylor polynomial of `exp (i tq33 m)` are
within `1/100000` of `a` and `b`, then the direction `e^{2πi m/33}` is within `10⁻⁴` of
`a + b I`. -/
theorem dir_close33 (m : ℕ) (hm : m ≤ 32) (a b : ℝ)
    (hre : |(∑ k ∈ Finset.range 12, (-((tq33 m)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - a|
      ≤ (1 / 100000 : ℝ))
    (him : |tq33 m * (∑ k ∈ Finset.range 12, (-((tq33 m)^2))^k / (((2*k+1).factorial : ℕ) : ℝ)) - b|
      ≤ (1 / 100000 : ℝ)) :
    ‖Work.Landing.rayDirection ((m : ℝ) / 33) - ((a : ℂ) + (b : ℂ) * Complex.I)‖
      ≤ (1 / 10000 : ℝ) := by
  set x : ℂ := Complex.I * (((2 * Real.pi * (m : ℝ) / 33 : ℝ)) : ℂ) with hxdef
  set w : ℂ := Complex.I * ((tq33 m : ℝ) : ℂ) with hwdef
  have hray : Work.Landing.rayDirection ((m : ℝ) / 33) = Complex.exp x := by
    rw [Work.Landing.rayDirection, hxdef]
    congr 1
    push_cast
    ring
  rw [hray]
  have hm32 : (m : ℝ) ≤ 32 := by exact_mod_cast hm
  have hxnorm : ‖x‖ ≤ 61 / 10 := by
    have hnorm : ‖x‖ = 2 * Real.pi * (m : ℝ) / 33 := by
      rw [hxdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hnorm]
    have h1 : (2 : ℝ) * Real.pi * (m : ℝ) ≤ 2 * 3.14159265358979323847 * 32 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (le_of_lt Real.pi_lt_d20) (by norm_num))
        hm32 (Nat.cast_nonneg m) (by norm_num)
    have hfin : (2 : ℝ) * 3.14159265358979323847 * 32 / 33 ≤ 61 / 10 := by norm_num
    linarith
  have hwnorm : ‖w‖ ≤ 61 / 10 := by
    have hp : (piq : ℝ) = 3.14159265358979323846 := by norm_num [piq]
    have hnorm : ‖w‖ = tq33 m := by
      rw [hwdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, tq33,
        abs_of_nonneg (by rw [hp]; positivity)]
    rw [hnorm, tq33, hp]
    have h1 : (2 : ℝ) * 3.14159265358979323846 * (m : ℝ)
        ≤ 2 * 3.14159265358979323846 * 32 :=
      mul_le_mul_of_nonneg_left hm32 (by norm_num)
    have hfin : (2 : ℝ) * 3.14159265358979323846 * 32 / 33 ≤ 61 / 10 := by norm_num
    linarith
  have hxw : ‖x - w‖ ≤ 1 / 100000000 := by
    have hsub : x - w = Complex.I * (((2 * Real.pi * (m : ℝ) / 33 - tq33 m) : ℝ) : ℂ) := by
      rw [hxdef, hwdef]
      push_cast
      ring
    rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : 2 * Real.pi * (m : ℝ) / 33 - tq33 m
        = (2 * (m : ℝ) / 33) * (Real.pi - (piq : ℝ)) := by
      rw [tq33]
      ring
    rw [hsplit, abs_mul]
    have hm0 : (0 : ℝ) ≤ 2 * (m : ℝ) / 33 := by positivity
    have hm2 : 2 * (m : ℝ) / 33 ≤ 2 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 33)]
      linarith
    have hpi : |Real.pi - (piq : ℝ)| ≤ 1 / 10 ^ 20 := by
      rw [abs_sub_comm]
      exact piq_close
    rw [abs_of_nonneg hm0]
    calc (2 * (m : ℝ) / 33) * |Real.pi - (piq : ℝ)|
        ≤ 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ 1 / 100000000 := by norm_num
  have h1 : ‖Complex.exp x - Etrunc x‖ ≤ (1 / 40000 : ℝ) := exp_taylor_truncP hxnorm
  have h2 : ‖Etrunc x - Etrunc w‖ ≤ (1 / 100000 : ℝ) := by
    have hsum : Etrunc x - Etrunc w
        = ∑ k ∈ Finset.range 24, (x ^ k - w ^ k) / ((k.factorial : ℕ) : ℂ) := by
      simp only [Etrunc, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [sub_div]
    rw [hsum]
    calc _ ≤ ‖x - w‖ * 500 := norm_sum_taylor_diff_leP hxnorm hwnorm
      _ ≤ 1 / 100000 := by linarith
  have h3 : ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ (1 / 50000 : ℝ) := by
    have hw' : Etrunc w = (∑ k ∈ Finset.range (2*12), (Complex.I * ((tq33 m : ℝ) : ℂ))^k
        / ((k.factorial : ℕ) : ℂ)) := by
      simp only [Etrunc, hwdef]
    rw [hw', taylor_split (tq33 m) 12]
    exact norm_ofReal_pair_sub_le hre him
  calc ‖Complex.exp x - ((a : ℂ) + (b : ℂ) * Complex.I)‖
      = ‖(Complex.exp x - Etrunc x) + (Etrunc x - Etrunc w)
          + (Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I))‖ := by ring_nf
    _ ≤ ‖Complex.exp x - Etrunc x‖ + ‖Etrunc x - Etrunc w‖
          + ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ := by
        calc ‖(Complex.exp x - Etrunc x) + (Etrunc x - Etrunc w)
              + (Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I))‖
            ≤ ‖(Complex.exp x - Etrunc x) + (Etrunc x - Etrunc w)‖
              + ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ := norm_add_le _ _
          _ ≤ (‖Complex.exp x - Etrunc x‖ + ‖Etrunc x - Etrunc w‖)
              + ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ := by
              gcongr
              exact norm_add_le _ _
    _ ≤ 1 / 10000 := by linarith

/-! ## The twenty exact rational evaluations

The even (real) and odd (imaginary) parts of the 24-term Taylor sum at `tq33 m`, against the
mantissas of `dirBaseP` (scale `2 ^ 40`).  All twenty are one-line `norm_num` calls.
-/

/-- class `0` (`12/33`), real part against the mantissa `-720026991547` (scale `2^40`). -/
lemma dirnumP_re_zero :
    |(∑ k ∈ Finset.range 12, (-((tq33 12)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-720026991547 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `0` (`12/33`), imaginary part against the mantissa `830955444689` (scale `2^40`). -/
lemma dirnumP_im_zero :
    |tq33 12 * (∑ k ∈ Finset.range 12, (-((tq33 12)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((830955444689 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `1` (`9/33`), real part against the mantissa `-156476819487` (scale `2^40`). -/
lemma dirnumP_re_one :
    |(∑ k ∈ Finset.range 12, (-((tq33 9)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-156476819487 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `1` (`9/33`), imaginary part against the mantissa `1088320184770` (scale `2^40`). -/
lemma dirnumP_im_one :
    |tq33 9 * (∑ k ∈ Finset.range 12, (-((tq33 9)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((1088320184770 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `2` (`15/33`), real part against the mantissa `-1054973681259` (scale `2^40`). -/
lemma dirnumP_re_two :
    |(∑ k ∈ Finset.range 12, (-((tq33 15)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-1054973681259 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `2` (`15/33`), imaginary part against the mantissa `309768222170` (scale `2^40`). -/
lemma dirnumP_im_two :
    |tq33 15 * (∑ k ∈ Finset.range 12, (-((tq33 15)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((309768222170 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `3` (`3/33`), real part against the mantissa `924968041256` (scale `2^40`). -/
lemma dirnumP_re_three :
    |(∑ k ∈ Finset.range 12, (-((tq33 3)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((924968041256 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `3` (`3/33`), imaginary part against the mantissa `594440865243` (scale `2^40`). -/
lemma dirnumP_im_three :
    |tq33 3 * (∑ k ∈ Finset.range 12, (-((tq33 3)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((594440865243 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `4` (`27/33`), real part against the mantissa `456753637148` (scale `2^40`). -/
lemma dirnumP_re_four :
    |(∑ k ∈ Finset.range 12, (-((tq33 27)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((456753637148 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `4` (`27/33`), imaginary part against the mantissa `-1000150955889` (scale `2^40`). -/
lemma dirnumP_im_four :
    |tq33 27 * (∑ k ∈ Finset.range 12, (-((tq33 27)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((-1000150955889 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `5` (`13/33`), real part against the mantissa `-864274517719` (scale `2^40`). -/
lemma dirnumP_re_five :
    |(∑ k ∈ Finset.range 12, (-((tq33 13)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-864274517719 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `5` (`13/33`), imaginary part against the mantissa `679672993164` (scale `2^40`). -/
lemma dirnumP_im_five :
    |tq33 13 * (∑ k ∈ Finset.range 12, (-((tq33 13)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((679672993164 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `6` (`7/33`), real part against the mantissa `259219690945` (scale `2^40`). -/
lemma dirnumP_re_six :
    |(∑ k ∈ Finset.range 12, (-((tq33 7)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((259219690945 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `6` (`7/33`), imaginary part against the mantissa `1068518119379` (scale `2^40`). -/
lemma dirnumP_im_six :
    |tq33 7 * (∑ k ∈ Finset.range 12, (-((tq33 7)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((1068518119379 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `7` (`19/33`), real part against the mantissa `-977284910976` (scale `2^40`). -/
lemma dirnumP_re_seven :
    |(∑ k ∈ Finset.range 12, (-((tq33 19)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-977284910976 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `7` (`19/33`), imaginary part against the mantissa `-503825388795` (scale `2^40`). -/
lemma dirnumP_im_seven :
    |tq33 19 * (∑ k ∈ Finset.range 12, (-((tq33 19)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((-503825388795 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `8` (`28/33`), real part against the mantissa `637779316845` (scale `2^40`). -/
lemma dirnumP_re_eight :
    |(∑ k ∈ Finset.range 12, (-((tq33 28)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((637779316845 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `8` (`28/33`), imaginary part against the mantissa `-895635730986` (scale `2^40`). -/
lemma dirnumP_im_eight :
    |tq33 28 * (∑ k ∈ Finset.range 12, (-((tq33 28)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((-895635730986 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `9` (`10/33`), real part against the mantissa `-359615028741` (scale `2^40`). -/
lemma dirnumP_re_nine :
    |(∑ k ∈ Finset.range 12, (-((tq33 10)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-359615028741 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-- class `9` (`10/33`), imaginary part against the mantissa `1039039388435` (scale `2^40`). -/
lemma dirnumP_im_nine :
    |tq33 10 * (∑ k ∈ Finset.range 12, (-((tq33 10)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((1039039388435 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq33, piq, Finset.sum_range_succ]

/-! ## The ten directions -/

/-- The direction of class `0` (`12/33`) against `qdirP 0`. -/
theorem dirjP_zero : ‖Work.Landing.rayDirection (angP 0) - qdirP 0‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 0 = (12 : ℝ)/33 := angP_zero
  have hq : qdirP 0 = (((-720026991547 : ℝ)/2^40 : ℝ) : ℂ)
      + (((830955444689 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 12 (by norm_num) _ _ dirnumP_re_zero dirnumP_im_zero

/-- The direction of class `1` (`9/33`) against `qdirP 1`. -/
theorem dirjP_one : ‖Work.Landing.rayDirection (angP 1) - qdirP 1‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 1 = (9 : ℝ)/33 := angP_one
  have hq : qdirP 1 = (((-156476819487 : ℝ)/2^40 : ℝ) : ℂ)
      + (((1088320184770 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 9 (by norm_num) _ _ dirnumP_re_one dirnumP_im_one

/-- The direction of class `2` (`15/33`) against `qdirP 2`. -/
theorem dirjP_two : ‖Work.Landing.rayDirection (angP 2) - qdirP 2‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 2 = (15 : ℝ)/33 := angP_two
  have hq : qdirP 2 = (((-1054973681259 : ℝ)/2^40 : ℝ) : ℂ)
      + (((309768222170 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 15 (by norm_num) _ _ dirnumP_re_two dirnumP_im_two

/-- The direction of class `3` (`3/33`) against `qdirP 3`. -/
theorem dirjP_three : ‖Work.Landing.rayDirection (angP 3) - qdirP 3‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 3 = (3 : ℝ)/33 := angP_three
  have hq : qdirP 3 = (((924968041256 : ℝ)/2^40 : ℝ) : ℂ)
      + (((594440865243 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 3 (by norm_num) _ _ dirnumP_re_three dirnumP_im_three

/-- The direction of class `4` (`27/33`) against `qdirP 4`. -/
theorem dirjP_four : ‖Work.Landing.rayDirection (angP 4) - qdirP 4‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 4 = (27 : ℝ)/33 := angP_four
  have hq : qdirP 4 = (((456753637148 : ℝ)/2^40 : ℝ) : ℂ)
      + (((-1000150955889 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 27 (by norm_num) _ _ dirnumP_re_four dirnumP_im_four

/-- The direction of class `5` (`13/33`) against `qdirP 5`. -/
theorem dirjP_five : ‖Work.Landing.rayDirection (angP 5) - qdirP 5‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 5 = (13 : ℝ)/33 := angP_five
  have hq : qdirP 5 = (((-864274517719 : ℝ)/2^40 : ℝ) : ℂ)
      + (((679672993164 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 13 (by norm_num) _ _ dirnumP_re_five dirnumP_im_five

/-- The direction of class `6` (`7/33`) against `qdirP 6`. -/
theorem dirjP_six : ‖Work.Landing.rayDirection (angP 6) - qdirP 6‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 6 = (7 : ℝ)/33 := angP_six
  have hq : qdirP 6 = (((259219690945 : ℝ)/2^40 : ℝ) : ℂ)
      + (((1068518119379 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 7 (by norm_num) _ _ dirnumP_re_six dirnumP_im_six

/-- The direction of class `7` (`19/33`) against `qdirP 7`. -/
theorem dirjP_seven : ‖Work.Landing.rayDirection (angP 7) - qdirP 7‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 7 = (19 : ℝ)/33 := angP_seven
  have hq : qdirP 7 = (((-977284910976 : ℝ)/2^40 : ℝ) : ℂ)
      + (((-503825388795 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 19 (by norm_num) _ _ dirnumP_re_seven dirnumP_im_seven

/-- The direction of class `8` (`28/33`) against `qdirP 8`. -/
theorem dirjP_eight : ‖Work.Landing.rayDirection (angP 8) - qdirP 8‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 8 = (28 : ℝ)/33 := angP_eight
  have hq : qdirP 8 = (((637779316845 : ℝ)/2^40 : ℝ) : ℂ)
      + (((-895635730986 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 28 (by norm_num) _ _ dirnumP_re_eight dirnumP_im_eight

/-- The direction of class `9` (`10/33`) against `qdirP 9`. -/
theorem dirjP_nine : ‖Work.Landing.rayDirection (angP 9) - qdirP 9‖ ≤ (1 / 10000 : ℝ) := by
  have hth : angP 9 = (10 : ℝ)/33 := angP_nine
  have hq : qdirP 9 = (((-359615028741 : ℝ)/2^40 : ℝ) : ℂ)
      + (((1039039388435 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirP, Q, MS, gI, dirBaseP]
    norm_num
  rw [hth, hq]
  exact dir_close33 10 (by norm_num) _ _ dirnumP_re_nine dirnumP_im_nine

/-! ## The target -/

/-- **The direction bound for the ten classes of the certificate.** -/
theorem dirBoundP (j : ℕ) (hj : j < 10) :
    ‖Work.Landing.rayDirection (angP j) - qdirP j‖ ≤ (1 / 10000 : ℝ) := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dirjP_zero
  · exact dirjP_one
  · exact dirjP_two
  · exact dirjP_three
  · exact dirjP_four
  · exact dirjP_five
  · exact dirjP_six
  · exact dirjP_seven
  · exact dirjP_eight
  · exact dirjP_nine

/-- **The direction bound for the `12/33`-cycle** (`angA j` against the direction data of class
`j % 5`). -/
theorem dirBoundA (j : ℕ) (hj : j < 5) :
    ‖Work.Landing.rayDirection (angA j) - qdirP (j % 5)‖ ≤ (1 / 10000 : ℝ) := by
  have hmod : j % 5 = j := Nat.mod_eq_of_lt hj
  rw [hmod]
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · simpa only [angP_zero, angA_zero] using dirjP_zero
  · simpa only [angP_one, angA_one] using dirjP_one
  · simpa only [angP_two, angA_two] using dirjP_two
  · simpa only [angP_three, angA_three] using dirjP_three
  · simpa only [angP_four, angA_four] using dirjP_four

/-- **The direction bound for the `13/33`-cycle** (`angB j` against the direction data of class
`5 + j % 5`). -/
theorem dirBoundB (j : ℕ) (hj : j < 5) :
    ‖Work.Landing.rayDirection (angB j) - qdirP (5 + j % 5)‖ ≤ (1 / 10000 : ℝ) := by
  have hmod : j % 5 = j := Nat.mod_eq_of_lt hj
  rw [hmod]
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · simpa only [angP_five, angB_zero] using dirjP_five
  · simpa only [angP_six, angB_one] using dirjP_six
  · simpa only [angP_seven, angB_two] using dirjP_seven
  · simpa only [angP_eight, angB_three] using dirjP_eight
  · simpa only [angP_nine, angB_four] using dirjP_nine

end

end Work.SeedPortraitCert
