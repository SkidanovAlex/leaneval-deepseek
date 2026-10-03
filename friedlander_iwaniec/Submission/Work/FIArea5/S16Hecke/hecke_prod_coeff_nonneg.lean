/-
# `Submission.Work.FIArea5.S16Hecke.hecke_prod_coeff_nonneg`

The product `L(s,1) · L(s,χ₁) · L(s,χ₂) · L(s,χ₁χ₂)` of Hecke `L`-series of `ℚ(i)` attached to
real, completely multiplicative, bounded characters has a Dirichlet series expansion whose
coefficients are real and non-negative.  The coefficient sequence is the Dirichlet convolution
`Conv χ₁ χ₂ = λ_1 ⍟ λ_{χ₁} ⍟ λ_{χ₂} ⍟ λ_{χ₁χ₂}`, and non-negativity is reduced, via multiplicativity
of `λ_χ` (and hence of the convolution), to the prime powers, where the local factor is
`Gab`-positive by `hecke_prod_local` (`Conv_re_nonneg`, whose prime-power input is
`conv_prime_pow`).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.hecke_prod_local
import Submission.Work.FIArea5.S16Hecke.conv_prime_pow
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-! ## `ψ(χ,0,·) = χ` and realness of the Hecke eigenvalues -/

lemma psi_zero_apply (chi : GaussianInt → ℂ) (z : GaussianInt) : psi chi 0 z = chi z := by
  rw [psi, zpow_zero, mul_one]

lemma im_sum_zero {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i, (f i).im = 0) :
    (∑ i ∈ s, f i).im = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Complex.add_im, h a, ih, add_zero]

/-- A real-valued character gives real Hecke eigenvalues. -/
lemma heckeLam_zero_im (chi : GaussianInt → ℂ) (hre : ∀ z : GaussianInt, chi z = star (chi z))
    (n : ℕ) : (heckeLam chi 0 n).im = 0 := by
  classical
  rw [heckeLam]
  apply im_sum_zero
  intro z
  rw [psi_zero_apply, Complex.conj_eq_iff_im.mp (hre z).symm]

lemma mul_im_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) : (z*w).im = 0 := by
  rw [Complex.mul_im, hz, hw]; ring

lemma convolution_im_zero {f g : ℕ → ℂ} (hf : ∀ n, (f n).im = 0) (hg : ∀ n, (g n).im = 0) :
    ∀ n, ((LSeries.convolution f g) n).im = 0 := by
  intro n
  rw [LSeries.convolution_def]
  apply im_sum_zero
  rintro ⟨a,b⟩
  exact mul_im_zero (hf a) (hg b)

/-! ## The coefficient sequence and its multiplicativity -/

/-- The Dirichlet convolution `λ_1 ⍟ λ_{χ₁} ⍟ λ_{χ₂} ⍟ λ_{χ₁χ₂}`. -/
def Conv (chi₁ chi₂ : GaussianInt → ℂ) : ℕ → ℂ :=
  LSeries.convolution (LSeries.convolution (LSeries.convolution
    (heckeLam (fun _ => (1:ℂ)) 0) (heckeLam chi₁ 0)) (heckeLam chi₂ 0))
    (heckeLam (fun z => chi₁ z * chi₂ z) 0)

lemma toArithmeticFunction_of_ne_zero {R : Type*} [Zero R] (f : ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    toArithmeticFunction f n = f n := by simp [toArithmeticFunction, hn]

lemma isMult_coe (chi : GaussianInt → ℂ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z*w) = chi z * chi w) :
    (toArithmeticFunction (heckeLam chi 0)).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · simp [toArithmeticFunction, heckeLam_one, h1]
  · intro m n hm hn hcop
    rw [show toArithmeticFunction (heckeLam chi 0) (m*n) = heckeLam chi 0 (m*n) by
          simp [toArithmeticFunction, mul_ne_zero hm hn],
        show toArithmeticFunction (heckeLam chi 0) m = heckeLam chi 0 m by
          simp [toArithmeticFunction, hm],
        show toArithmeticFunction (heckeLam chi 0) n = heckeLam chi 0 n by
          simp [toArithmeticFunction, hn]]
    exact heckeLam_mul chi 0 hmul (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop

lemma taf_Conv (chi₁ chi₂ : GaussianInt → ℂ) :
    toArithmeticFunction (Conv chi₁ chi₂)
      = ((toArithmeticFunction (heckeLam (fun _ => (1:ℂ)) 0) *
          toArithmeticFunction (heckeLam chi₁ 0)) *
          toArithmeticFunction (heckeLam chi₂ 0)) *
          toArithmeticFunction (heckeLam (fun z => chi₁ z * chi₂ z) 0) := by
  simp only [Conv, LSeries.convolution, ArithmeticFunction.toArithmeticFunction_eq_self]

lemma isMult_Conv (chi₁ chi₂ : GaussianInt → ℂ)
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z*w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z*w) = chi₂ z * chi₂ w) :
    (toArithmeticFunction (Conv chi₁ chi₂)).IsMultiplicative := by
  rw [taf_Conv]
  have h1 := isMult_coe (fun _ => (1:ℂ)) rfl (by intro z w; ring)
  have h2 := isMult_coe chi₁ h1₁ hmul₁
  have h3 := isMult_coe chi₂ h1₂ hmul₂
  have h4 := isMult_coe (fun z => chi₁ z * chi₂ z) (by rw [h1₁, h1₂, one_mul])
    (by intro z w; rw [hmul₁, hmul₂]; ring)
  exact ((h1.mul h2).mul h3).mul h4

lemma Conv_one (chi₁ chi₂ : GaussianInt → ℂ) (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1) :
    Conv chi₁ chi₂ 1 = 1 := by
  simp only [Conv, LSeries.convolution_def, Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
  simp [heckeLam_one, h1₁, h1₂]

/-- Multiplicativity of the coefficient sequence, in the form of the product over prime powers. -/
lemma Conv_factorization (chi₁ chi₂ : GaussianInt → ℂ)
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z*w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z*w) = chi₂ z * chi₂ w)
    (n : ℕ) (hn : n ≠ 0) :
    Conv chi₁ chi₂ n = ∏ p ∈ n.primeFactors, Conv chi₁ chi₂ (p ^ n.factorization p) := by
  have hf := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (toArithmeticFunction (Conv chi₁ chi₂)) (isMult_Conv chi₁ chi₂ h1₁ h1₂ hmul₁ hmul₂) hn
  rw [Finsupp.prod_of_support_subset (n.factorization) (Finset.Subset.refl _)
      (fun p k => toArithmeticFunction (Conv chi₁ chi₂) (p^k)) ?_] at hf
  · rw [show toArithmeticFunction (Conv chi₁ chi₂) n = Conv chi₁ chi₂ n from
        toArithmeticFunction_of_ne_zero (Conv chi₁ chi₂) hn, Nat.support_factorization] at hf
    rw [hf]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact toArithmeticFunction_of_ne_zero (Conv chi₁ chi₂) (pow_ne_zero (n.factorization p) hp'.ne_zero)
  · intro i hi
    rw [pow_zero]
    rw [toArithmeticFunction_of_ne_zero (Conv chi₁ chi₂) one_ne_zero]
    exact Conv_one chi₁ chi₂ h1₁ h1₂

/-! ## Realness of the coefficients -/

lemma prod_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, (f i).im = 0) :
    (∏ i ∈ s, f i) = ((∏ i ∈ s, (f i).re : ℝ) : ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), Complex.ofReal_mul]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h a (Finset.mem_insert_self a s)]

lemma Conv_im (chi₁ chi₂ : GaussianInt → ℂ)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z)) (n : ℕ) :
    (Conv chi₁ chi₂ n).im = 0 := by
  have h0 : ∀ n, ((heckeLam (fun _ => (1:ℂ)) 0) n).im = 0 :=
    heckeLam_zero_im _ (by intro z; simp)
  have h1 : ∀ n, ((heckeLam chi₁ 0) n).im = 0 := heckeLam_zero_im _ hre₁
  have h2 : ∀ n, ((heckeLam chi₂ 0) n).im = 0 := heckeLam_zero_im _ hre₂
  have h3 : ∀ n, ((heckeLam (fun z => chi₁ z * chi₂ z) 0) n).im = 0 :=
    heckeLam_zero_im _ (by intro z; rw [star_mul, ← hre₂ z, ← hre₁ z]; ring)
  exact convolution_im_zero (convolution_im_zero (convolution_im_zero h0 h1) h2) h3 n

/-! ## Non-negativity of the coefficients -/

theorem Conv_re_nonneg (chi₁ chi₂ : GaussianInt → ℂ)
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z*w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z*w) = chi₂ z * chi₂ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1)
    (n : ℕ) (hn : 0 < n) : 0 ≤ (Conv chi₁ chi₂ n).re := by
  rw [Conv_factorization chi₁ chi₂ h1₁ h1₂ hmul₁ hmul₂ n hn.ne']
  rw [prod_ofReal _ (fun p => Conv chi₁ chi₂ (p ^ n.factorization p))
        (fun i _ => Conv_im chi₁ chi₂ hre₁ hre₂ _), Complex.ofReal_re]
  refine Finset.prod_nonneg (fun p hp => ?_)
  obtain ⟨c, hc, hconv⟩ := conv_prime_pow chi₁ chi₂ h1₁ h1₂ hre₁ hre₂ hmul₁ hmul₂ hb₁ hb₂ p
    (Nat.prime_of_mem_primeFactors hp) (n.factorization p)
  have hconv' : Conv chi₁ chi₂ (p ^ n.factorization p) = (c : ℂ) := hconv
  rw [hconv', Complex.ofReal_re]; exact hc

/-! ## Summability -/

lemma summable_heckeLam (chi : GaussianInt → ℂ) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (heckeLam chi 0) s := by
  rw [LSeriesSummable]
  rw [← summable_norm_iff]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_card_divisors_mul_rpow_neg hs).mul_left 4)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq, if_neg hn]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have h1 : ‖heckeLam chi 0 n‖ ≤ 4 * (n.divisors.card : ℝ) := by
      have := heckeLam_bound chi 0 hb (show 1 ≤ n from hnpos)
      simpa using this
    have h2 : 0 < (n:ℝ)^s.re := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
    calc ‖heckeLam chi 0 n‖ / (n:ℝ)^s.re
        ≤ (4 * (n.divisors.card : ℝ)) / (n:ℝ)^s.re := div_le_div_of_nonneg_right h1 h2.le
      _ = 4 * ((n.divisors.card : ℝ) * (n:ℝ)^(-s.re)) := by
          rw [Real.rpow_neg (Nat.cast_nonneg n)]; ring

/-! ## The main theorem -/

theorem hecke_prod_coeff_nonneg (chi₁ chi₂ : GaussianInt → ℂ)
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z)) (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z * w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z * w) = chi₂ z * chi₂ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1) :
    ∃ a : ℕ → ℝ, a 1 = 1 ∧ (∀ n : ℕ, 0 < n → 0 ≤ a n) ∧ ∀ s : ℂ, 1 < s.re →
      (∑' n : ℕ, (a n : ℂ) * (n : ℂ) ^ (-s))
        = heckeLSeries (fun _ => (1 : ℂ)) 0 s * heckeLSeries chi₁ 0 s * heckeLSeries chi₂ 0 s *
            heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := by
  refine ⟨fun n => (Conv chi₁ chi₂ n).re, ?_, ?_, ?_⟩
  · simp [Conv_one chi₁ chi₂ h1₁ h1₂]
  · intro n hn
    exact Conv_re_nonneg chi₁ chi₂ h1₁ h1₂ hre₁ hre₂ hmul₁ hmul₂ hb₁ hb₂ n hn
  · intro s hs
    have hConv0 : Conv chi₁ chi₂ 0 = 0 := by simp [Conv, LSeries.convolution_def]
    have hre : ∀ n, (Conv chi₁ chi₂ n) = (((Conv chi₁ chi₂ n).re) : ℂ) :=
      fun n => Complex.ext rfl (by rw [Complex.ofReal_im, Conv_im chi₁ chi₂ hre₁ hre₂ n])
    have hterm : (∑' n : ℕ, ((Conv chi₁ chi₂ n).re : ℂ) * (n:ℂ)^(-s)) = LSeries (Conv chi₁ chi₂) s := by
      rw [show LSeries (Conv chi₁ chi₂) s = ∑' n, Conv chi₁ chi₂ n * (n:ℂ)^(-s) from by
            rw [LSeries]; exact tsum_congr (fun n => LSeries.term_def₀ hConv0 s n)]
      exact tsum_congr (fun n => by rw [hre n, Complex.ofReal_re])
    rw [hterm]
    have hsumm0 : LSeriesSummable (heckeLam (fun _ => (1:ℂ)) 0) s :=
      summable_heckeLam _ (by intro z; simp) hs
    have hsumm1 : LSeriesSummable (heckeLam chi₁ 0) s := summable_heckeLam _ hb₁ hs
    have hsumm2 : LSeriesSummable (heckeLam chi₂ 0) s := summable_heckeLam _ hb₂ hs
    have hsumm3 : LSeriesSummable (heckeLam (fun z => chi₁ z * chi₂ z) 0) s :=
      summable_heckeLam _ (by intro z; rw [norm_mul]; exact mul_le_one₀ (hb₁ z) (norm_nonneg _) (hb₂ z)) hs
    have e1 := LSeries_convolution' hsumm0 hsumm1
    have e2 := LSeries_convolution' (hsumm0.convolution hsumm1) hsumm2
    have e3 := LSeries_convolution' ((hsumm0.convolution hsumm1).convolution hsumm2) hsumm3
    rw [Conv, e3, e2, e1]
    simp only [heckeLSeries]

end

end Work.FIArea5.S16Hecke
