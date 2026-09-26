/-
# Auxiliary estimates for the theta q-expansions

This file collects the elementary estimates used to bound the tails of the `q`-expansions of
Jacobi's theta functions at the cusp, together with the two pure-algebra norm estimates that
turn those expansions into the numerical bounds required by `Work.Asymptotics.ThetaQExp`.
-/
import Mathlib
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.LogLambda.ThetaLower.ratio_estimate
import Submission.Work.Asymptotics.theta00_pow_series

namespace Work.Asymptotics

open scoped Topology
open Work.Kernels.LogLambda.ThetaLower

noncomputable section

/-- **Geometric comparison.**  If `0 ≤ r ≤ 1/2` and `‖F n‖ ≤ r ^ (m + n)` for all `n`, then
`‖∑' n, F n‖ ≤ 2 * r ^ m`.  (The exact value of the geometric sum is `r ^ m / (1 - r)`, which
is at most `2 * r ^ m` because `1 - r ≥ 1/2`.) -/
theorem norm_tsum_le_two_mul_pow {F : ℕ → ℂ} {r : ℝ} {m : ℕ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hF : ∀ n, ‖F n‖ ≤ r ^ (m + n)) :
    ‖∑' n, F n‖ ≤ 2 * r ^ m := by
  have hr1 : r < 1 := by linarith
  have hg : Summable (fun n : ℕ => r ^ (m + n)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ m)
    refine h.congr (fun n => ?_)
    rw [← pow_add]
  have hFsum : Summable F := Summable.of_norm_bounded hg hF
  have hcmp : (∑' n : ℕ, ‖F n‖) ≤ ∑' n : ℕ, r ^ (m + n) :=
    Summable.tsum_le_tsum hF hFsum.norm hg
  have hval : (∑' n : ℕ, r ^ (m + n)) = r ^ m / (1 - r) := by
    rw [show (∑' n : ℕ, r ^ (m + n)) = ∑' n : ℕ, r ^ m * r ^ n from
      tsum_congr (fun n => by rw [← pow_add])]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  rw [hval] at hcmp
  have h2 : r ^ m / (1 - r) ≤ 2 * r ^ m := by
    have hden : (1 : ℝ) / 2 ≤ 1 - r := by linarith
    have hp : 0 ≤ r ^ m := pow_nonneg hr0 m
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)]
    nlinarith
  calc ‖∑' n, F n‖ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hFsum.norm
    _ ≤ r ^ m / (1 - r) := hcmp
    _ ≤ 2 * r ^ m := h2

/-- Summability companion of `norm_tsum_le_two_mul_pow`. -/
theorem summable_of_norm_le_pow {F : ℕ → ℂ} {r : ℝ} {m : ℕ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hF : ∀ n, ‖F n‖ ≤ r ^ (m + n)) : Summable F := by
  have hr1 : r < 1 := by linarith
  have hg : Summable (fun n : ℕ => r ^ (m + n)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ m)
    refine h.congr (fun n => ?_)
    rw [← pow_add]
  exact Summable.of_norm_bounded hg hF

/-- **Power series tail bound.**  If `‖e‖ ≤ 1/2` and the exponents `f n` satisfy
`m + n ≤ f n`, then `‖∑' n, e ^ (f n)‖ ≤ 2 ‖e‖ ^ m`. -/
theorem norm_tsum_pow_le {e : ℂ} {f : ℕ → ℕ} {m : ℕ} (he : ‖e‖ ≤ 1 / 2)
    (hf : ∀ n, m + n ≤ f n) : ‖∑' n : ℕ, e ^ f n‖ ≤ 2 * ‖e‖ ^ m := by
  have he0 : 0 ≤ ‖e‖ := norm_nonneg e
  have he1 : ‖e‖ ≤ 1 := by linarith
  refine norm_tsum_le_two_mul_pow he0 he (F := fun n => e ^ f n) (m := m) (fun n => ?_)
  rw [norm_pow]
  exact pow_le_pow_of_le_one he0 he1 (hf n)

/-- Summability companion of `norm_tsum_pow_le`. -/
theorem summable_pow_of_le {e : ℂ} {f : ℕ → ℕ} {m : ℕ} (he : ‖e‖ ≤ 1 / 2)
    (hf : ∀ n, m + n ≤ f n) : Summable (fun n : ℕ => e ^ f n) := by
  have he0 : 0 ≤ ‖e‖ := norm_nonneg e
  have he1 : ‖e‖ ≤ 1 := by linarith
  refine summable_of_norm_le_pow he0 he (F := fun n => e ^ f n) (m := m) (fun n => ?_)
  rw [norm_pow]
  exact pow_le_pow_of_le_one he0 he1 (hf n)

/-! ## Two elementary numerical facts -/

/-- `2 r ^ 9 ≤ r ^ 4` for `0 ≤ r ≤ 1/2`. -/
private lemma two_mul_pow_nine_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    2 * r ^ 9 ≤ r ^ 4 := by
  rw [show r ^ 9 = r ^ 4 * r ^ 5 by ring]
  have h5 : 2 * r ^ 5 ≤ 1 := by
    have h := pow_le_pow_left₀ hr0 hr 5
    norm_num at h
    linarith
  nlinarith [pow_nonneg hr0 4, pow_nonneg hr0 5]

/-- `2 r ^ 6 ≤ r ^ 2` for `0 ≤ r ≤ 1/2`. -/
private lemma two_mul_pow_six_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    2 * r ^ 6 ≤ r ^ 2 := by
  rw [show r ^ 6 = r ^ 2 * r ^ 4 by ring]
  have h4 : 2 * r ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ hr0 hr 4
    norm_num at h
    linarith
  nlinarith [pow_nonneg hr0 2, pow_nonneg hr0 4]

/-! ## The `q`-expansions of `θ₀₁` and of the `θ₂` ratio -/

/-- `(-1) ^ ((n+1)^2) = (-1) ^ (n+1)`: the parity of `(n+1)^2` is that of `n+1`. -/
private lemma neg_one_pow_sq_succ (n : ℕ) :
    ((-1 : ℂ) ^ ((n + 1) ^ 2)) = (-1 : ℂ) ^ (n + 1) := by
  have hmod : (n + 1) ^ 2 % 2 = (n + 1) % 2 := by
    rw [pow_two, Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h
    · rw [h]
    · rw [h]
  rw [neg_one_pow_eq_pow_mod_two ((n + 1) ^ 2), neg_one_pow_eq_pow_mod_two (n + 1), hmod]

/-- **The `q`-expansion of `θ₀₁`**: `θ₀₁ = 1 + 2 ∑_{n ≥ 0} (-1)^{n+1} e^{(n+1)²}` with
`e = nomeE = exp (π i τ)`. -/
theorem theta01_pow_series (w : UpperHalfPlane) :
    Work.Kernels.theta01Fun w
      = 1 + 2 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * (nomeE w) ^ ((n + 1) ^ 2) := by
  have h01 : Work.Kernels.theta01Fun w = jacobiTheta ((w : ℂ) + 1) := by
    rw [← Work.Kernels.theta00Fun_T w]
    show jacobiTheta (((ModularGroup.T • w : UpperHalfPlane) : ℂ)) = jacobiTheta ((w : ℂ) + 1)
    rw [Work.Kernels.coe_T_smul]
  have him : 0 < ((w : ℂ) + 1).im := by
    have h : ((w : ℂ) + 1).im = w.im := by simp
    rw [h]; exact w.im_pos
  have hsum : (∑' n : ℕ, (Complex.exp (Real.pi * Complex.I * ((w : ℂ) + 1))) ^ ((n + 1) ^ 2))
      = ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * (nomeE w) ^ ((n + 1) ^ 2) := by
    apply tsum_congr
    intro n
    have hexp : Complex.exp (Real.pi * Complex.I * ((w : ℂ) + 1)) = -(nomeE w) := by
      rw [nomeE_def]
      rw [show (Real.pi : ℂ) * Complex.I * ((w : ℂ) + 1)
          = Real.pi * Complex.I * (w : ℂ) + Real.pi * Complex.I by ring]
      rw [Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [hexp, neg_pow, neg_one_pow_sq_succ]
  rw [h01, theta00_pow_series ((w : ℂ) + 1) him, hsum]

/-- **The `θ₂` ratio as a power series**: `θ(z/2, z)/2 = ∑_{k ≥ 0} e^{k²+k}` with
`e = exp (π i z)`. -/
theorem thetaPair_pow_series (z : ℂ) (hz : 0 < z.im) :
    jacobiTheta₂ (z / 2) z / 2
      = ∑' k : ℕ, (Complex.exp (Real.pi * Complex.I * z)) ^ (k ^ 2 + k) := by
  have hjac : Summable (fun n : ℤ => jacobiTheta₂_term n (z / 2) z) :=
    (summable_jacobiTheta₂_term_iff (z / 2) z).mpr hz
  have hu : Summable (thetaSummand z) := hjac.congr (fun n => jacobiTheta₂_term_half z n)
  have hw : Summable (thetaPairSummand z) :=
    (hu.comp_injective Nat.cast_injective).congr (fun k => thetaSummand_ofNat z k)
  have h1 : HasSum (fun k : ℕ => thetaSummand z (k : ℤ)) (∑' k : ℕ, thetaPairSummand z k) :=
    hw.hasSum.congr_fun (fun k => thetaSummand_ofNat z k)
  have h2 : HasSum (fun m : ℕ => thetaSummand z (-((m : ℤ) + 1)))
      (∑' k : ℕ, thetaPairSummand z k) :=
    hw.hasSum.congr_fun (fun m => thetaSummand_negSucc z m)
  have hsum_u : HasSum (thetaSummand z)
      ((∑' k : ℕ, thetaPairSummand z k) + (∑' k : ℕ, thetaPairSummand z k)) :=
    HasSum.of_nat_of_neg_add_one h1 h2
  have hS : jacobiTheta₂ (z / 2) z / 2 = (∑' n : ℤ, thetaSummand z n) / 2 := by
    rw [jacobiTheta₂]
    congr 1
    exact tsum_congr (fun n => jacobiTheta₂_term_half z n)
  have hpow : ∀ k : ℕ, thetaPairSummand z k
      = (Complex.exp (Real.pi * Complex.I * z)) ^ (k ^ 2 + k) := by
    intro k
    rw [thetaPairSummand]
    rw [show (Real.pi : ℂ) * Complex.I * z * ((k : ℂ) ^ 2 + (k : ℂ))
        = ((k ^ 2 + k : ℕ) : ℂ) * (Real.pi * Complex.I * z) by push_cast; ring]
    rw [Complex.exp_nat_mul]
  have hterm : (∑' k : ℕ, thetaPairSummand z k)
      = ∑' k : ℕ, (Complex.exp (Real.pi * Complex.I * z)) ^ (k ^ 2 + k) := tsum_congr hpow
  rw [hS, hsum_u.tsum_eq, hterm]
  ring

/-! ## Pure algebra: the fourth-power and `V`-expansion estimates -/

/-- **Fourth-power expansion bound.**  If `x = e⁴ + x₂`, `‖e‖ = r ≤ 1/2`, `‖a‖ ≤ 2r` and
`‖x₂‖ ≤ 2 r⁹`, then
`(1 + a + 2x)⁴ = (1+a)⁴ + 8e⁴ + O(r⁵)`, with an explicit constant `10000`.  This is the shape
of the expansion of `U = θ₀₀⁴ = (1 + a + 2x)⁴` (with `a = ±2e`), in which the `e⁴` term of the
series cancels the fourth-order term of `(1+a)⁴`. -/
theorem quart_bound (a e x x₂ : ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (he : ‖e‖ = r) (ha : ‖a‖ ≤ 2 * r) (hx : x = e ^ 4 + x₂) (hx₂ : ‖x₂‖ ≤ 2 * r ^ 9) :
    ‖(1 + a + 2 * x) ^ 4 - ((1 + a) ^ 4 + 8 * e ^ 4)‖ ≤ 10000 * r ^ 5 := by
  have hr1 : r ≤ 1 := by linarith
  have hp : ∀ k : ℕ, 5 ≤ k → r ^ k ≤ r ^ 5 := fun k hk => pow_le_pow_of_le_one hr0 hr1 hk
  have hA : ‖(1 : ℂ) + a‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) a
    rw [norm_one] at h
    linarith
  have hxr : ‖x‖ ≤ 2 * r ^ 4 := by
    have h1 : ‖x‖ ≤ ‖e ^ 4‖ + ‖x₂‖ := by
      rw [hx]; exact norm_add_le _ _
    rw [norm_pow, he] at h1
    have h9 := two_mul_pow_nine_le r hr0 hr
    linarith
  have hcub : ‖((1 : ℂ) + a) ^ 3 - 1‖ ≤ 14 * r := by
    have hfac : ((1 : ℂ) + a) ^ 3 - 1 = a * (3 + 3 * a + a ^ 2) := by ring
    rw [hfac, norm_mul]
    have hA1 : ‖a‖ ≤ 1 := by linarith
    have h1 : ‖3 + 3 * a + a ^ 2‖ ≤ 7 := by
      have h2 : ‖(3 : ℂ) + (3 * a + a ^ 2)‖ ≤ 3 + ‖3 * a + a ^ 2‖ := by
        simpa [Complex.norm_ofNat] using norm_add_le (3 : ℂ) (3 * a + a ^ 2)
      have h3 : ‖3 * a + a ^ 2‖ ≤ 3 * ‖a‖ + ‖a‖ ^ 2 := by
        have h4 : ‖3 * a + a ^ 2‖ ≤ ‖(3 : ℂ) * a‖ + ‖a ^ 2‖ := norm_add_le _ _
        rw [norm_mul, Complex.norm_ofNat, norm_pow] at h4
        exact h4
      have h5 : ‖3 + 3 * a + a ^ 2‖ = ‖(3 : ℂ) + (3 * a + a ^ 2)‖ := by
        congr 1; ring
      have h6 : 3 * ‖a‖ ≤ 3 := by linarith
      have h7 : ‖a‖ ^ 2 ≤ 1 := by
        simpa using pow_le_pow_left₀ (norm_nonneg a) hA1 2
      have h8 : 3 + (3 * ‖a‖ + ‖a‖ ^ 2) ≤ 7 := by linarith
      linarith [h2, h3, h5, h8]
    have hfin : ‖a‖ * ‖3 + 3 * a + a ^ 2‖ ≤ (2 * r) * 7 :=
      mul_le_mul ha h1 (norm_nonneg _) (by positivity)
    linarith
  have hkey : (1 + a + 2 * x) ^ 4 - ((1 + a) ^ 4 + 8 * e ^ 4)
      = 8 * e ^ 4 * (((1 + a) ^ 3 - 1)) + 8 * (1 + a) ^ 3 * x₂
        + 24 * (1 + a) ^ 2 * x ^ 2 + 32 * (1 + a) * x ^ 3 + 16 * x ^ 4 := by
    rw [hx]; ring
  have hA3 : ‖(1 : ℂ) + a‖ ^ 3 ≤ 8 := by
    have h := pow_le_pow_left₀ (norm_nonneg ((1 : ℂ) + a)) hA 3
    norm_num at h
    exact h
  have hA2 : ‖(1 : ℂ) + a‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg ((1 : ℂ) + a)) hA 2
    norm_num at h
    exact h
  have t1 : ‖8 * e ^ 4 * (((1 + a) ^ 3 - 1))‖ ≤ 112 * r ^ 5 := by
    have hnorm : ‖8 * e ^ 4 * (((1 + a) ^ 3 - 1))‖ = 8 * r ^ 4 * ‖((1 : ℂ) + a) ^ 3 - 1‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat, he]
    rw [hnorm]
    calc 8 * r ^ 4 * ‖((1 : ℂ) + a) ^ 3 - 1‖ ≤ 8 * r ^ 4 * (14 * r) :=
          mul_le_mul_of_nonneg_left hcub (by positivity)
      _ = 112 * r ^ 5 := by ring
  have t2 : ‖8 * (1 + a) ^ 3 * x₂‖ ≤ 128 * r ^ 9 := by
    have hnorm : ‖8 * (1 + a) ^ 3 * x₂‖ = 8 * ‖(1 : ℂ) + a‖ ^ 3 * ‖x₂‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hnorm]
    calc 8 * ‖(1 : ℂ) + a‖ ^ 3 * ‖x₂‖ ≤ (8 * 8) * (2 * r ^ 9) :=
          mul_le_mul (by linarith : 8 * ‖(1 : ℂ) + a‖ ^ 3 ≤ 8 * 8) hx₂ (norm_nonneg x₂)
            (by norm_num)
      _ = 128 * r ^ 9 := by ring
  have t3 : ‖24 * (1 + a) ^ 2 * x ^ 2‖ ≤ 384 * r ^ 8 := by
    have hnorm : ‖24 * (1 + a) ^ 2 * x ^ 2‖ = 24 * ‖(1 : ℂ) + a‖ ^ 2 * ‖x‖ ^ 2 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hnorm]
    have hx2 : ‖x‖ ^ 2 ≤ (2 * r ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxr 2
    calc 24 * ‖(1 : ℂ) + a‖ ^ 2 * ‖x‖ ^ 2 ≤ (24 * 4) * (2 * r ^ 4) ^ 2 :=
          mul_le_mul (by linarith : 24 * ‖(1 : ℂ) + a‖ ^ 2 ≤ 24 * 4) hx2
            (pow_nonneg (norm_nonneg x) 2) (by norm_num)
      _ = 384 * r ^ 8 := by ring
  have t4 : ‖32 * (1 + a) * x ^ 3‖ ≤ 512 * r ^ 12 := by
    have hnorm : ‖32 * (1 + a) * x ^ 3‖ = 32 * ‖(1 : ℂ) + a‖ * ‖x‖ ^ 3 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hnorm]
    have hx3 : ‖x‖ ^ 3 ≤ (2 * r ^ 4) ^ 3 := pow_le_pow_left₀ (norm_nonneg x) hxr 3
    calc 32 * ‖(1 : ℂ) + a‖ * ‖x‖ ^ 3 ≤ (32 * 2) * (2 * r ^ 4) ^ 3 :=
          mul_le_mul (by linarith : 32 * ‖(1 : ℂ) + a‖ ≤ 32 * 2) hx3
            (pow_nonneg (norm_nonneg x) 3) (by norm_num)
      _ = 512 * r ^ 12 := by ring
  have t5 : ‖16 * x ^ 4‖ ≤ 256 * r ^ 16 := by
    have hnorm : ‖16 * x ^ 4‖ = 16 * ‖x‖ ^ 4 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hnorm]
    have hx4 : ‖x‖ ^ 4 ≤ (2 * r ^ 4) ^ 4 := pow_le_pow_left₀ (norm_nonneg x) hxr 4
    calc 16 * ‖x‖ ^ 4 ≤ 16 * (2 * r ^ 4) ^ 4 := mul_le_mul_of_nonneg_left hx4 (by norm_num)
      _ = 256 * r ^ 16 := by ring
  rw [hkey]
  have h1 := norm_add_le (8 * e ^ 4 * (((1 + a) ^ 3 - 1)) + 8 * (1 + a) ^ 3 * x₂
      + 24 * (1 + a) ^ 2 * x ^ 2 + 32 * (1 + a) * x ^ 3) (16 * x ^ 4)
  have h2 := norm_add_le (8 * e ^ 4 * (((1 + a) ^ 3 - 1)) + 8 * (1 + a) ^ 3 * x₂
      + 24 * (1 + a) ^ 2 * x ^ 2) (32 * (1 + a) * x ^ 3)
  have h3 := norm_add_le (8 * e ^ 4 * (((1 + a) ^ 3 - 1)) + 8 * (1 + a) ^ 3 * x₂)
      (24 * (1 + a) ^ 2 * x ^ 2)
  have h4 := norm_add_le (8 * e ^ 4 * (((1 + a) ^ 3 - 1))) (8 * (1 + a) ^ 3 * x₂)
  have hs : ‖8 * e ^ 4 * (((1 + a) ^ 3 - 1)) + 8 * (1 + a) ^ 3 * x₂
      + 24 * (1 + a) ^ 2 * x ^ 2 + 32 * (1 + a) * x ^ 3 + 16 * x ^ 4‖
      ≤ 112 * r ^ 5 + 128 * r ^ 9 + 384 * r ^ 8 + 512 * r ^ 12 + 256 * r ^ 16 := by
    linarith
  refine le_trans hs ?_
  have h9 := hp 9 (by norm_num)
  have h8 := hp 8 (by norm_num)
  have h12 := hp 12 (by norm_num)
  have h16 := hp 16 (by norm_num)
  have h5 : 0 ≤ r ^ 5 := pow_nonneg hr0 5
  nlinarith

/-- **`V`-expansion bound.**  If `u = 1 + G`, `‖e‖ = r ≤ 1/2` and `‖G - e²‖ ≤ 2 r⁶`, then
`16 e u⁴ = 16 e + 64 e³ + O(r⁵)`, with an explicit constant `10000`. -/
theorem V_bound (e u G : ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (he : ‖e‖ = r) (hu : u = 1 + G) (hG : ‖G - e ^ 2‖ ≤ 2 * r ^ 6) :
    ‖16 * e * u ^ 4 - (16 * e + 64 * e ^ 3)‖ ≤ 10000 * r ^ 5 := by
  have hr1 : r ≤ 1 := by linarith
  have hp : ∀ k : ℕ, 5 ≤ k → r ^ k ≤ r ^ 5 := fun k hk => pow_le_pow_of_le_one hr0 hr1 hk
  have hGr : ‖G‖ ≤ 2 * r ^ 2 := by
    have h1 : ‖G‖ ≤ ‖e ^ 2‖ + ‖G - e ^ 2‖ := by
      have h := norm_add_le (e ^ 2) (G - e ^ 2)
      rwa [add_sub_cancel] at h
    rw [norm_pow, he] at h1
    have h6 := two_mul_pow_six_le r hr0 hr
    linarith
  have hkey : 16 * e * u ^ 4 - (16 * e + 64 * e ^ 3)
      = 16 * e * (4 * (G - e ^ 2) + 6 * G ^ 2 + 4 * G ^ 3 + G ^ 4) := by
    rw [hu]; ring
  have hsplit : 16 * e * (4 * (G - e ^ 2) + 6 * G ^ 2 + 4 * G ^ 3 + G ^ 4)
      = 16 * e * (4 * (G - e ^ 2)) + 16 * e * (6 * G ^ 2) + 16 * e * (4 * G ^ 3)
        + 16 * e * G ^ 4 := by ring
  rw [hkey, hsplit]
  have hG2 : ‖G‖ ^ 2 ≤ (2 * r ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg G) hGr 2
  have hG3 : ‖G‖ ^ 3 ≤ (2 * r ^ 2) ^ 3 := pow_le_pow_left₀ (norm_nonneg G) hGr 3
  have hG4 : ‖G‖ ^ 4 ≤ (2 * r ^ 2) ^ 4 := pow_le_pow_left₀ (norm_nonneg G) hGr 4
  have t1 : ‖16 * e * (4 * (G - e ^ 2))‖ ≤ 128 * r ^ 7 := by
    have hnorm : ‖16 * e * (4 * (G - e ^ 2))‖ = 16 * r * (4 * ‖G - e ^ 2‖) := by
      simp only [norm_mul, Complex.norm_ofNat, he]
    rw [hnorm]
    calc 16 * r * (4 * ‖G - e ^ 2‖) ≤ 16 * r * (4 * (2 * r ^ 6)) :=
          mul_le_mul_of_nonneg_left (by linarith [hG]) (by positivity)
      _ = 128 * r ^ 7 := by ring
  have t2 : ‖16 * e * (6 * G ^ 2)‖ ≤ 384 * r ^ 5 := by
    have hnorm : ‖16 * e * (6 * G ^ 2)‖ = 16 * r * (6 * ‖G‖ ^ 2) := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat, he]
    rw [hnorm]
    calc 16 * r * (6 * ‖G‖ ^ 2) ≤ 16 * r * (6 * (2 * r ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hG2]) (by positivity)
      _ = 384 * r ^ 5 := by ring
  have t3 : ‖16 * e * (4 * G ^ 3)‖ ≤ 512 * r ^ 7 := by
    have hnorm : ‖16 * e * (4 * G ^ 3)‖ = 16 * r * (4 * ‖G‖ ^ 3) := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat, he]
    rw [hnorm]
    calc 16 * r * (4 * ‖G‖ ^ 3) ≤ 16 * r * (4 * (2 * r ^ 2) ^ 3) :=
          mul_le_mul_of_nonneg_left (by linarith [hG3]) (by positivity)
      _ = 512 * r ^ 7 := by ring
  have t4 : ‖16 * e * G ^ 4‖ ≤ 256 * r ^ 9 := by
    have hnorm : ‖16 * e * G ^ 4‖ = 16 * r * ‖G‖ ^ 4 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat, he]
    rw [hnorm]
    calc 16 * r * ‖G‖ ^ 4 ≤ 16 * r * (2 * r ^ 2) ^ 4 :=
          mul_le_mul_of_nonneg_left hG4 (by positivity)
      _ = 256 * r ^ 9 := by ring
  have h1 := norm_add_le (16 * e * (4 * (G - e ^ 2)) + 16 * e * (6 * G ^ 2)
      + 16 * e * (4 * G ^ 3)) (16 * e * G ^ 4)
  have h2 := norm_add_le (16 * e * (4 * (G - e ^ 2)) + 16 * e * (6 * G ^ 2))
      (16 * e * (4 * G ^ 3))
  have h3 := norm_add_le (16 * e * (4 * (G - e ^ 2))) (16 * e * (6 * G ^ 2))
  have hs : ‖16 * e * (4 * (G - e ^ 2)) + 16 * e * (6 * G ^ 2) + 16 * e * (4 * G ^ 3)
      + 16 * e * G ^ 4‖ ≤ 128 * r ^ 7 + 384 * r ^ 5 + 512 * r ^ 7 + 256 * r ^ 9 := by
    linarith
  refine le_trans hs ?_
  have h7 := hp 7 (by norm_num)
  have h9 := hp 9 (by norm_num)
  have h5 : 0 ≤ r ^ 5 := pow_nonneg hr0 5
  nlinarith

end

end Work.Asymptotics
