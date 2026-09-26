import Mathlib
import Submission.Work.Rigidity.LambdaSeries
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.LogLambda.ThetaLower.ratio_estimate

/-!
# `λ(τ) = lambdaSeries (e^{π i τ})`

The modular lambda function `λ = θ₁₀⁴ / θ₀₀⁴` (with `θ₀₀ = jacobiTheta`, `θ₁₀` the
half-period shifted theta) is the `q`-expansion `lambdaSeries` evaluated at `q = e^{π i τ}`.

The proof rewrites both theta series as `ℤ`-indexed sums that pair into the `ℕ`-indexed
series `aSeries`, `bSeries` defining `lambdaSeries`:

* `jacobiTheta τ = ∑_{n ∈ ℤ} q^{n²} = 1 + 2 ∑_{m ≥ 1} q^{m²} = bSeries q`,
* `jacobiTheta₂ (τ/2) τ = ∑_{n ∈ ℤ} q^{n(n+1)} = 2 ∑_{m ≥ 0} q^{m(m+1)} = 2 aSeries q`,

with `q = e^{π i τ}`.  Since `θ₁₀(τ)⁴ = q · (2 aSeries q)⁴ = 16 q (aSeries q)⁴` and
`θ₀₀(τ)⁴ = (bSeries q)⁴`, the quotient is `16 q (aSeries q)⁴ / (bSeries q)⁴ = lambdaSeries q`.
-/

noncomputable section

open UpperHalfPlane

namespace Work.Rigidity

/-! ## The `ℤ`-indexed families summing to `aSeries` and `bSeries` -/

/-- `bFam z n = z ^ (n²)`, the `ℤ`-indexed version of the summands of `bSeries`. -/
private noncomputable def bFam (z : ℂ) (n : ℤ) : ℂ := z ^ ((n ^ 2).toNat)

/-- `aFam z n = z ^ (n (n+1))`, the `ℤ`-indexed version of the summands of `aSeries`. -/
private noncomputable def aFam (z : ℂ) (n : ℤ) : ℂ := z ^ ((n * (n + 1)).toNat)

private lemma bFam_natCast (z : ℂ) (n : ℕ) : bFam z (n : ℤ) = z ^ (n ^ 2) := by
  rw [bFam]
  have h : ((n : ℤ) ^ 2).toNat = n ^ 2 := by rw [← Int.natCast_pow, Int.toNat_natCast]
  rw [h]

private lemma bFam_neg (z : ℂ) (n : ℤ) : bFam z (-n) = bFam z n := by rw [bFam, bFam, neg_sq]

private lemma bFam_zero (z : ℂ) : bFam z 0 = 1 := by rw [bFam]; norm_num

private lemma bFam_add_one (z : ℂ) (n : ℕ) : bFam z ((n : ℤ) + 1) = z ^ ((n + 1) ^ 2) := by
  have : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, bFam]
  have h : (((n + 1 : ℕ) : ℤ) ^ 2).toNat = (n + 1) ^ 2 := by
    rw [← Int.natCast_pow, Int.toNat_natCast]
  rw [h]

private lemma aFam_natCast (z : ℂ) (n : ℕ) : aFam z (n : ℤ) = z ^ (n * (n + 1)) := by
  rw [aFam]
  have h : (((n : ℤ) * ((n : ℤ) + 1))).toNat = n * (n + 1) := by
    have : ((n : ℤ) * ((n : ℤ) + 1)) = ((n * (n + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [h]

private lemma aFam_neg_add_one (z : ℂ) (n : ℕ) : aFam z (-((n : ℤ) + 1)) = z ^ (n * (n + 1)) := by
  rw [aFam]
  have h : ((-((n : ℤ) + 1)) * ((-((n : ℤ) + 1)) + 1)).toNat = n * (n + 1) := by
    have : ((-((n : ℤ) + 1)) * ((-((n : ℤ) + 1)) + 1)) = ((n * (n + 1) : ℕ) : ℤ) := by
      push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [h]

/-! ## Summability of the two families -/

private lemma summable_pow_sq (z : ℂ) (hz : ‖z‖ < 1) : Summable (fun n : ℕ => z ^ (n ^ 2)) := by
  apply Summable.of_norm_bounded (g := fun n => ‖z‖ ^ n)
  · simpa using hz
  · intro n
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg z) (le_of_lt hz) (Nat.le_self_pow (by norm_num) n)

private lemma summable_pow_mul_succ (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ (n * (n + 1))) := by
  apply Summable.of_norm_bounded (g := fun n => ‖z‖ ^ n)
  · simpa using hz
  · intro n
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg z) (le_of_lt hz)
      (Nat.le_mul_of_pos_right (m := n + 1) n (Nat.succ_pos n))

private lemma summable_bFam (z : ℂ) (hz : ‖z‖ < 1) : Summable (bFam z) := by
  apply Summable.of_nat_of_neg_add_one
  · have h : (fun n : ℕ => bFam z (n : ℤ)) = fun n => z ^ (n ^ 2) := by
      funext n; exact bFam_natCast z n
    rw [h]; exact summable_pow_sq z hz
  · have h : (fun n : ℕ => bFam z (-((n : ℤ) + 1))) = fun n => z ^ ((n + 1) ^ 2) := by
      funext n; rw [bFam_neg, bFam_add_one]
    rw [h]
    exact (summable_nat_add_iff (f := fun n : ℕ => z ^ (n ^ 2)) 1).mpr (summable_pow_sq z hz)

private lemma summable_aFam (z : ℂ) (hz : ‖z‖ < 1) : Summable (aFam z) := by
  apply Summable.of_nat_of_neg_add_one
  · have h : (fun n : ℕ => aFam z (n : ℤ)) = fun n => z ^ (n * (n + 1)) := by
      funext n; exact aFam_natCast z n
    rw [h]; exact summable_pow_mul_succ z hz
  · have h : (fun n : ℕ => aFam z (-((n : ℤ) + 1))) = fun n => z ^ (n * (n + 1)) := by
      funext n; exact aFam_neg_add_one z n
    rw [h]; exact summable_pow_mul_succ z hz

/-! ## Evaluation of the `ℤ`-indexed sums -/

private lemma tsum_bFam (z : ℂ) (hz : ‖z‖ < 1) : ∑' n : ℤ, bFam z n = bSeries z := by
  have hs := summable_bFam z hz
  have hs0 := summable_pow_sq z hz
  have hsplit := tsum_nat_add_neg (f := bFam z) hs
  have hπ : ∑' n : ℕ, (bFam z (n : ℤ) + bFam z (-(n : ℤ))) = 2 * (1 + bCore z) := by
    have hc : ∀ n : ℕ, (bFam z (n : ℤ) + bFam z (-(n : ℤ))) = 2 * z ^ (n ^ 2) := by
      intro n; rw [bFam_neg, bFam_natCast]; ring
    rw [tsum_congr hc, tsum_mul_left]
    congr 1
    rw [hs0.tsum_eq_zero_add]
    congr 1
    rw [bCore]
    exact tsum_congr (fun n => by rw [pow_two])
  have hR : ∑' n : ℤ, bFam z n + bFam z 0 = 2 * (1 + bCore z) := hsplit.symm.trans hπ
  have hR' : ∑' n : ℤ, bFam z n + 1 = 2 * (1 + bCore z) := by
    simpa [bFam_zero] using hR
  rw [bSeries_apply]
  linear_combination hR'

private lemma tsum_aFam (z : ℂ) (hz : ‖z‖ < 1) : ∑' n : ℤ, aFam z n = 2 * aSeries z := by
  have hs := summable_aFam z hz
  rw [← tsum_nat_add_neg_add_one (f := aFam z) hs]
  have hc : ∀ n : ℕ, (aFam z (n : ℤ) + aFam z (-((n : ℤ) + 1))) = 2 * z ^ (n * (n + 1)) := by
    intro n; rw [aFam_natCast, aFam_neg_add_one]; ring
  rw [tsum_congr hc, tsum_mul_left]
  rfl

/-! ## Exponential bookkeeping -/

private lemma exp_mul_nat (x : ℂ) (m : ℕ) : Complex.exp (x * (m : ℂ)) = Complex.exp x ^ m := by
  rw [mul_comm, Complex.exp_nat_mul]

private lemma intCast_sq_toNat (n : ℤ) : (((n ^ 2).toNat : ℕ) : ℂ) = ((n : ℂ)) ^ 2 := by
  have h : (((n ^ 2).toNat : ℕ) : ℤ) = n ^ 2 := Int.toNat_of_nonneg (sq_nonneg n)
  have h1 : ((n : ℂ)) ^ 2 = ((n ^ 2 : ℤ) : ℂ) := by push_cast; ring
  rw [h1]
  exact congrArg (fun k : ℤ => (k : ℂ)) h

private lemma intCast_mul_succ_toNat (n : ℤ) :
    (((n * (n + 1)).toNat : ℕ) : ℂ) = ((n : ℂ)) ^ 2 + (n : ℂ) := by
  have hnonneg : (0 : ℤ) ≤ n * (n + 1) := by
    by_cases hn : 0 ≤ n
    · exact mul_nonneg hn (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have h1 : ((n : ℂ)) ^ 2 + (n : ℂ) = ((n * (n + 1) : ℤ) : ℂ) := by push_cast; ring
  rw [h1]
  exact_mod_cast (Int.toNat_of_nonneg hnonneg)

/-! ## The two theta functions as power series -/

private lemma term_bFam (τ : ℍ) (n : ℤ) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))
      = bFam (Complex.exp (Real.pi * Complex.I * (τ : ℂ))) n := by
  rw [bFam, ← exp_mul_nat]
  congr 1
  rw [intCast_sq_toNat]
  ring

private lemma term_aFam (τ : ℍ) (n : ℤ) :
    jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)
      = aFam (Complex.exp (Real.pi * Complex.I * (τ : ℂ))) n := by
  rw [jacobiTheta₂_term, aFam, ← exp_mul_nat]
  congr 1
  rw [intCast_mul_succ_toNat]
  ring

/-- `θ₀₀(τ) = jacobiTheta τ = bSeries q` with `q = e^{π i τ}`. -/
lemma jacobiTheta_eq_bSeries (τ : UpperHalfPlane) :
    jacobiTheta (τ : ℂ) = bSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ))) := by
  set q := Complex.exp (Real.pi * Complex.I * (τ : ℂ)) with hq
  have hz : ‖q‖ < 1 := by
    rw [hq, Complex.norm_exp]
    have hre : (Real.pi * Complex.I * (τ : ℂ)).re = -(Real.pi * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
    rw [hre, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, τ.im_pos]
  have h1 : jacobiTheta (τ : ℂ) = ∑' n : ℤ, bFam q n := by
    rw [jacobiTheta]
    refine tsum_congr (fun n => ?_)
    rw [hq]
    exact term_bFam τ n
  rw [h1, tsum_bFam q hz]

/-- `θ₁₀(τ) = e^{π i τ/4} · jacobiTheta₂ (τ/2) τ`, and
`jacobiTheta₂ (τ/2) τ = 2 aSeries q` with `q = e^{π i τ}`. -/
lemma jacobiTheta₂_half_eq (τ : UpperHalfPlane) :
    jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)
      = 2 * aSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ))) := by
  set q := Complex.exp (Real.pi * Complex.I * (τ : ℂ)) with hq
  have hz : ‖q‖ < 1 := by
    rw [hq, Complex.norm_exp]
    have hre : (Real.pi * Complex.I * (τ : ℂ)).re = -(Real.pi * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
    rw [hre, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, τ.im_pos]
  have h1 : jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) = ∑' n : ℤ, aFam q n := by
    rw [jacobiTheta₂]
    refine tsum_congr (fun n => ?_)
    rw [hq]
    exact term_aFam τ n
  rw [h1, tsum_aFam q hz]

/-! ## The main identity -/

theorem lambdaFun_eq_lambdaSeries (τ : UpperHalfPlane) :
    Work.Kernels.lambdaFun τ
      = Work.Rigidity.lambdaSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ))) := by
  have h4 : (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)) ^ 4
      = Complex.exp (Real.pi * Complex.I * (τ : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hV : Work.Kernels.VFun τ
      = Complex.exp (Real.pi * Complex.I * (τ : ℂ))
          * (2 * aSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))) ^ 4 := by
    calc Work.Kernels.VFun τ
        = (Work.Kernels.theta10Fun τ) ^ 4 := rfl
      _ = (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)
              * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)) ^ 4 := rfl
      _ = (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)) ^ 4
              * (jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)) ^ 4 := by rw [mul_pow]
      _ = Complex.exp (Real.pi * Complex.I * (τ : ℂ))
              * (2 * aSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))) ^ 4 := by
            rw [h4, jacobiTheta₂_half_eq τ]
  have hU : Work.Kernels.UFun τ
      = (bSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))) ^ 4 := by
    calc Work.Kernels.UFun τ
        = (Work.Kernels.theta00Fun τ) ^ 4 := rfl
      _ = (jacobiTheta (τ : ℂ)) ^ 4 := rfl
      _ = (bSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))) ^ 4 := by
            rw [jacobiTheta_eq_bSeries τ]
  calc Work.Kernels.lambdaFun τ
      = Work.Kernels.VFun τ / Work.Kernels.UFun τ := rfl
    _ = (Complex.exp (Real.pi * Complex.I * (τ : ℂ))
            * (2 * aSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))) ^ 4)
          / (bSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))) ^ 4 := by rw [hV, hU]
    _ = Work.Rigidity.lambdaSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ))) := by
          rw [Work.Rigidity.lambdaSeries_apply]; ring

end Work.Rigidity
