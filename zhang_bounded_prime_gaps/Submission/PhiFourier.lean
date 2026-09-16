import Mathlib
import Submission.PhiKernel
import Submission.DivisorKernel
import Submission.PairwiseFourier

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The `φ`-denominator Fubini identity (the `2k`-fold divisor sum)

Mirror of `Submission.PairwiseFourier` for the `φ`-denominator weight of the
prime (θ-weighted) sums: with `mobiusTotientWeight q a b := μ(a)μ(b)/φ([a,b])`
(guarded by `([a,b], q) = 1`),

    Σ_{x} [pairwise good] ∏_j μ(d_j)μ(d′_j)/φ([d_j,d′_j])·F_j(log_R d_j)·G_j(log_R d′_j)
      = ∫_{ℝ^{2k}} (∏_{p ∤ q} K^φ_p)(ξ,ξ′) · ∏_j 𝓕(eᵘF_j)(ξ_j)·𝓕(eᵘG_j)(ξ′_j) .

The kernel is the `φ`-Euler product `pairKernelPhi` (`Submission.PhiKernel`).
All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## The `φ`-denominator weights and majorants -/

/-- The Möbius/totient weight of the `φ`-denominator kernel:
`μ(a)μ(b)/φ([a,b])` for `([a,b], q) = 1`, and `0` otherwise. -/
noncomputable def mobiusTotientWeight (q a b : ℕ) : ℂ :=
  if (Nat.lcm a b).Coprime q then
    ((ArithmeticFunction.moebius a : ℤ) : ℂ) * ((ArithmeticFunction.moebius b : ℤ) : ℂ) *
      ((((Nat.lcm a b).totient : ℕ) : ℂ))⁻¹
  else 0

/-- The majorant of the `φ`-denominator kernel weight:
`φ([a,b])⁻¹·a^{−1/log R}·b^{−1/log R}` in norm form. -/
noncomputable def kernelMajorantPhi (R : ℕ) (x : ℕ × ℕ) : ℝ :=
  ‖((((Nat.lcm x.1 x.2).totient : ℕ) : ℂ))⁻¹ *
    (x.1 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ)) *
    (x.2 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ))‖

/-- The Möbius/totient weight vanishes in the first coordinate at `0`. -/
lemma mobiusTotientWeight_zero_fst (q b : ℕ) : mobiusTotientWeight q 0 b = 0 := by
  unfold mobiusTotientWeight
  split_ifs with hc
  · have h : ArithmeticFunction.moebius 0 = 0 := by simp [ArithmeticFunction.moebius]
    rw [h]; ring
  · rfl

/-- The Möbius/totient weight vanishes in the second coordinate at `0`. -/
lemma mobiusTotientWeight_zero_snd (q a : ℕ) : mobiusTotientWeight q a 0 = 0 := by
  unfold mobiusTotientWeight
  split_ifs with hc
  · have h : ArithmeticFunction.moebius 0 = 0 := by simp [ArithmeticFunction.moebius]
    rw [h]; ring
  · rfl

/-- The majorant is non-negative. -/
lemma kernelMajorantPhi_nonneg (R : ℕ) (x : ℕ × ℕ) : 0 ≤ kernelMajorantPhi R x :=
  norm_nonneg _

/-- Norm of a real `cpow` with negative real exponent, including the base `0`. -/
private lemma norm_ofReal_cpow_neg (r s : ℝ) (hr : 0 ≤ r) :
    ‖((r : ℂ)) ^ (-(s : ℂ))‖ = r ^ (-s) := by
  rcases lt_or_eq_of_le hr with h | h
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h]; simp
  · subst h
    by_cases hs : s = 0
    · subst hs; norm_num
    · have hs' : -((s : ℂ)) ≠ 0 := by simpa using hs
      rw [show ((0 : ℝ) : ℂ) = 0 by simp, Complex.zero_cpow hs', norm_zero,
        Real.zero_rpow (show -(s) ≠ 0 by intro h0; exact hs (by linarith))]

/-- `‖(x : ℂ)^{−1/log R}‖ = x^{−1/log R}` for natural `x`. -/
private lemma norm_natCast_cpow_neg {R : ℕ} (x : ℕ) :
    ‖(x : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ))‖ =
      (x : ℝ) ^ (-(1 / Real.log (R : ℝ))) := by
  have h := norm_ofReal_cpow_neg (x : ℝ) (1 / Real.log (R : ℝ)) (Nat.cast_nonneg x)
  simpa using h

/-- The norm of the Möbius/totient weight is at most the totient factor. -/
lemma norm_mobiusTotientWeight_le (q a b : ℕ) :
    ‖mobiusTotientWeight q a b‖ ≤ ‖((((Nat.lcm a b).totient : ℕ) : ℂ))⁻¹‖ := by
  rw [mobiusTotientWeight]
  by_cases hc : (Nat.lcm a b).Coprime q
  · rw [if_pos hc, norm_mul, norm_mul]
    have h1 := norm_moebius_intCast_complex_le_one a
    have h2 := norm_moebius_intCast_complex_le_one b
    calc ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ * ‖((ArithmeticFunction.moebius b : ℤ) : ℂ)‖ *
          ‖((((Nat.lcm a b).totient : ℕ) : ℂ))⁻¹‖
        ≤ (1 * 1) * ‖((((Nat.lcm a b).totient : ℕ) : ℂ))⁻¹‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = ‖((((Nat.lcm a b).totient : ℕ) : ℂ))⁻¹‖ := by ring
  · rw [if_neg hc, norm_zero]; positivity

/-- The norm of the weighted divisor phase is at most the majorant. -/
lemma norm_weight_phase_phi (q R a b : ℕ) (hR : 1 < R) (ξ ξ' : ℝ) :
    ‖mobiusTotientWeight q a b * divisorPhase R a ξ * divisorPhase R b ξ'‖ ≤
      kernelMajorantPhi R (a, b) := by
  have hfac : kernelMajorantPhi R (a, b) =
      ‖((((Nat.lcm a b).totient : ℕ) : ℂ))⁻¹‖ * ((a : ℝ) ^ (-(1 / Real.log (R : ℝ)))) *
        ((b : ℝ) ^ (-(1 / Real.log (R : ℝ)))) := by
    rw [kernelMajorantPhi, norm_mul, norm_mul, norm_natCast_cpow_neg (R := R) a,
      norm_natCast_cpow_neg (R := R) b]
  rw [hfac, norm_mul, norm_mul]
  by_cases ha : a = 0
  · subst ha
    rw [mobiusTotientWeight_zero_fst, norm_zero, zero_mul, zero_mul]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · by_cases hb : b = 0
    · subst hb
      rw [mobiusTotientWeight_zero_snd, norm_zero, zero_mul, zero_mul]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · rw [norm_divisorPhase hR ha ξ, norm_divisorPhase hR hb ξ']
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_mobiusTotientWeight_le q a b) (by positivity))
        (by positivity)

/-- The norm of the `φ`-kernel weight at the real points `(1/log R, 1/log R)` is
at most the majorant. -/
lemma norm_kernelWeightPhi_le_majorant (R : ℕ) (hR : 1 < R) (x : ℕ × ℕ) :
    ‖kernelWeightPhi (((1 / Real.log (R : ℝ)) : ℝ) : ℂ)
        (((1 / Real.log (R : ℝ)) : ℝ) : ℂ) x‖ ≤ kernelMajorantPhi R x := by
  have hfac : kernelWeightPhi (((1 / Real.log (R : ℝ)) : ℝ) : ℂ)
      (((1 / Real.log (R : ℝ)) : ℝ) : ℂ) x =
      (((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)) *
        (((((Nat.lcm x.1 x.2).totient : ℕ) : ℂ))⁻¹ *
          (x.1 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ)) *
          (x.2 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ))) := by
    rw [kernelWeightPhi]; ring
  rw [hfac, kernelMajorantPhi, norm_mul]
  calc ‖((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)‖ *
        ‖((((Nat.lcm x.1 x.2).totient : ℕ) : ℂ))⁻¹ *
          (x.1 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ)) *
          (x.2 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ))‖
      ≤ (1 * 1) * ‖((((Nat.lcm x.1 x.2).totient : ℕ) : ℂ))⁻¹ *
          (x.1 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ)) *
          (x.2 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ))‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul (norm_moebius_intCast_complex_le_one x.1)
          (norm_moebius_intCast_complex_le_one x.2) (norm_nonneg _) (by norm_num)
    _ = ‖((((Nat.lcm x.1 x.2).totient : ℕ) : ℂ))⁻¹ *
          (x.1 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ)) *
          (x.2 : ℂ) ^ (-(((1 / Real.log (R : ℝ)) : ℝ) : ℂ))‖ := by ring

/-- **Summability of the `φ`-majorant.** -/
lemma summable_kernelMajorantPhi (R : ℕ) (hR : 1 < R) :
    Summable (kernelMajorantPhi R) := by
  have hL : (0 : ℝ) < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have h1 : (0 : ℝ) < ((((1 / Real.log (R : ℝ)) : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; positivity
  exact Commons.NumberTheory.Zeta.summable_totient_lcm_cpow
    (a := (((1 / Real.log (R : ℝ)) : ℝ) : ℂ)) (b := (((1 / Real.log (R : ℝ)) : ℝ) : ℂ)) h1 h1

/-- **Factorization of the `φ`-kernel weight into the weighted divisor phases**
(under the coprimality guard that makes `mobiusTotientWeight` nonzero). -/
lemma kernelWeightPhi_eq_phase_mul (q R a b : ℕ) (hR : 1 < R)
    (hc : (Nat.lcm a b).Coprime q) (ξ ξ' : ℝ) :
    kernelWeightPhi (logZ (-(2 * Real.pi * ξ)) R) (logZ (-(2 * Real.pi * ξ')) R) (a, b)
      = mobiusTotientWeight q a b * divisorPhase R a ξ * divisorPhase R b ξ' := by
  rw [kernelWeightPhi, mobiusTotientWeight, if_pos hc]
  simp only [Prod.fst, Prod.snd]
  by_cases ha : a = 0
  · rw [ha]
    simp [ArithmeticFunction.moebius]
  · by_cases hb : b = 0
    · rw [hb]
      simp [ArithmeticFunction.moebius]
    · rw [divisorPhase_eq_cpow hR ha ξ, divisorPhase_eq_cpow hR hb ξ']

/-! ## The pairwise per-term kernel -/

/-- The pairwise-restricted `k`-coordinate `φ`-divisor-summand with the smooth
cutoffs. -/
noncomputable def pairWeightDivPhi {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (x : Fin k → ℕ × ℕ) : ℂ :=
  if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
    ∏ j : Fin k, (mobiusTotientWeight q (x j).1 (x j).2 * (F j (logR (x j).1 R) : ℂ) *
      (G j (logR (x j).2 R) : ℂ))
  else 0

/-- The per-term Fourier kernel of the `φ`-Fubini step. -/
noncomputable def pairKernelPhasePhi {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (x : Fin k → ℕ × ℕ) (p : Fin k → ℝ × ℝ) : ℂ :=
  if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
    (∏ j : Fin k, mobiusTotientWeight q (x j).1 (x j).2) *
      (∏ j : Fin k, divisorPhase R (x j).1 (p j).1) *
      (∏ j : Fin k, divisorPhase R (x j).2 (p j).2) *
      (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2))
  else 0

lemma pairWeightDivPhi_apply {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ) (x : Fin k → ℕ × ℕ) :
    pairWeightDivPhi F G q R x =
      (if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
        ∏ j : Fin k, (mobiusTotientWeight q (x j).1 (x j).2 * (F j (logR (x j).1 R) : ℂ) *
          (G j (logR (x j).2 R) : ℂ))
      else 0) := rfl

lemma pairKernelPhasePhi_apply {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (x : Fin k → ℕ × ℕ) (p : Fin k → ℝ × ℝ) :
    pairKernelPhasePhi F G q R x p =
      (if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
        (∏ j : Fin k, mobiusTotientWeight q (x j).1 (x j).2) *
          (∏ j : Fin k, divisorPhase R (x j).1 (p j).1) *
          (∏ j : Fin k, divisorPhase R (x j).2 (p j).2) *
          (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2))
      else 0) := rfl

/-- The norm of the per-term kernel is bounded by the `φ`-majorants times the
Fourier transforms. -/
theorem norm_pairKernelPhasePhi_le {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ) (hR : 1 < R)
    (x : Fin k → ℕ × ℕ) (p : Fin k → ℝ × ℝ) :
    ‖pairKernelPhasePhi F G q R x p‖ ≤
      (∏ j : Fin k, kernelMajorantPhi R (x j)) * phaseMajorant F G p := by
  rw [phaseMajorant]
  rw [pairKernelPhasePhi]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
    rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod, norm_prod, norm_prod]
    simp only [norm_mul]
    have hper : ∀ j : Fin k,
        ‖mobiusTotientWeight q (x j).1 (x j).2‖ * ‖divisorPhase R (x j).1 (p j).1‖ *
          ‖divisorPhase R (x j).2 (p j).2‖ ≤ kernelMajorantPhi R (x j) := by
      intro j
      have h := norm_weight_phase_phi q R (x j).1 (x j).2 hR (p j).1 (p j).2
      rw [norm_mul, norm_mul] at h
      exact h
    have hthree : (∏ j : Fin k, ‖mobiusTotientWeight q (x j).1 (x j).2‖) *
        (∏ j : Fin k, ‖divisorPhase R (x j).1 (p j).1‖) *
        (∏ j : Fin k, ‖divisorPhase R (x j).2 (p j).2‖) =
        ∏ j : Fin k, (‖mobiusTotientWeight q (x j).1 (x j).2‖ *
          ‖divisorPhase R (x j).1 (p j).1‖ * ‖divisorPhase R (x j).2 (p j).2‖) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [hthree]
    exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod
      (fun j _ => by positivity) (fun j _ => hper j))
      (Finset.prod_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  · rw [if_neg hg, norm_zero]
    refine mul_nonneg (Finset.prod_nonneg (fun j _ => kernelMajorantPhi_nonneg R (x j)))
      (Finset.prod_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))


/-! ## Integrability, the integral bound and summability -/

/-- Measurability of the per-term `φ`-kernel in `p`. -/
lemma aestronglyMeasurable_pairKernelPhasePhi {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (x : Fin k → ℕ × ℕ) :
    AEStronglyMeasurable (pairKernelPhasePhi F G q R x) := by
  classical
  have hfc : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => fourierCut (F j) (p j).1 := by
    intro j
    have h : Continuous (fourierCut (F j)) := by
      have h2 := (schwartzCut (F j) (hcsF j) (hsmF j)).continuous
      rw [schwartzCut_coe (F j) (hcsF j) (hsmF j)] at h2
      exact h2
    fun_prop (disch := exact h)
  have hgc : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => fourierCut (G j) (p j).2 := by
    intro j
    have h : Continuous (fourierCut (G j)) := by
      have h2 := (schwartzCut (G j) (hcsG j) (hsmG j)).continuous
      rw [schwartzCut_coe (G j) (hcsG j) (hsmG j)] at h2
      exact h2
    fun_prop (disch := exact h)
  have hph : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => divisorPhase R (x j).1 (p j).1 := by
    intro j
    have h : Continuous fun q : ℝ × ℝ => divisorPhase R (x j).1 q.1 := by
      unfold divisorPhase logR; fun_prop
    fun_prop (disch := exact h)
  have hph' : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => divisorPhase R (x j).2 (p j).2 := by
    intro j
    have h : Continuous fun q : ℝ × ℝ => divisorPhase R (x j).2 q.2 := by
      unfold divisorPhase logR; fun_prop
    fun_prop (disch := exact h)
  rw [show pairKernelPhasePhi F G q R x = fun p : Fin k → ℝ × ℝ =>
      if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
        (∏ j : Fin k, mobiusTotientWeight q (x j).1 (x j).2) *
          (∏ j : Fin k, divisorPhase R (x j).1 (p j).1) *
          (∏ j : Fin k, divisorPhase R (x j).2 (p j).2) *
          (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2))
      else 0 from rfl]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · simp only [if_pos hg]
    exact (((continuous_const.mul (continuous_finsetProd _ (fun j _ => hph j))).mul
      (continuous_finsetProd _ (fun j _ => hph' j))).mul
      (continuous_finsetProd _ (fun j _ => (hfc j).mul (hgc j)))).aestronglyMeasurable
  · simp only [if_neg hg]
    exact aestronglyMeasurable_const

/-- Integrability of the per-term `φ`-kernel. -/
theorem integrable_pairKernelPhasePhi {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (hR : 1 < R) (x : Fin k → ℕ × ℕ) :
    Integrable (pairKernelPhasePhi F G q R x) := by
  refine Integrable.mono'
    ((integrable_phaseMajorant F G hcsF hsmF hcsG hsmG).const_mul
      (∏ j : Fin k, kernelMajorantPhi R (x j)))
    (aestronglyMeasurable_pairKernelPhasePhi F G q R hcsF hsmF hcsG hsmG x) ?_
  filter_upwards with p
  simpa using norm_pairKernelPhasePhi_le F G q R hR x p

/-- The integral bound for one `φ`-term. -/
theorem integral_norm_pairKernelPhasePhi_le {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (hR : 1 < R) (x : Fin k → ℕ × ℕ) :
    ∫ p : Fin k → ℝ × ℝ, ‖pairKernelPhasePhi F G q R x p‖ ≤
      (∏ j : Fin k, kernelMajorantPhi R (x j)) *
        ∏ j : Fin k, (l1Cut (F j) * l1Cut (G j)) := by
  have hbase := integrable_phaseMajorant F G hcsF hsmF hcsG hsmG
  have hmono := integral_mono (integrable_pairKernelPhasePhi F G q R hcsF hsmF hcsG hsmG hR x).norm
    (hbase.const_mul (∏ j : Fin k, kernelMajorantPhi R (x j)))
    (fun p => by simpa using norm_pairKernelPhasePhi_le F G q R hR x p)
  rw [integral_const_mul] at hmono
  rw [integral_phaseMajorant F G] at hmono
  exact hmono

/-- Summability of the integrals of the norms of the per-term `φ`-kernels. -/
theorem summable_integral_norm_pairKernelPhasePhi {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (hR : 1 < R) :
    Summable fun x : Fin k → ℕ × ℕ => ∫ p : Fin k → ℝ × ℝ, ‖pairKernelPhasePhi F G q R x p‖ := by
  have hsingle : ∀ j : Fin k, Summable fun d : ℕ × ℕ => ‖(kernelMajorantPhi R d : ℂ)‖ := by
    intro j
    have h : (fun d : ℕ × ℕ => ‖(kernelMajorantPhi R d : ℂ)‖) = kernelMajorantPhi R := by
      funext d
      rw [Complex.norm_of_nonneg (kernelMajorantPhi_nonneg R d)]
    rw [h]
    exact summable_kernelMajorantPhi R hR
  have hprod := summable_norm_prod_pi k (fun _ (d : ℕ × ℕ) => (kernelMajorantPhi R d : ℂ)) hsingle
  have hprod' : Summable fun x : Fin k → ℕ × ℕ => ∏ j : Fin k, kernelMajorantPhi R (x j) := by
    have h : (fun x : Fin k → ℕ × ℕ => ∏ j : Fin k, kernelMajorantPhi R (x j)) =
        fun x : Fin k → ℕ × ℕ => ‖∏ j : Fin k, ((kernelMajorantPhi R (x j) : ℝ) : ℂ)‖ := by
      funext x
      rw [norm_prod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Complex.norm_of_nonneg (kernelMajorantPhi_nonneg R (x j))]
    rw [h]
    exact hprod
  exact Summable.of_nonneg_of_le (fun x => integral_nonneg (fun p => norm_nonneg _))
    (fun x => integral_norm_pairKernelPhasePhi_le F G q R hcsF hsmF hcsG hsmG hR x)
    (hprod'.mul_right _)

/-! ## The per-term Fourier expansion -/

/-- **Per-term Fourier expansion** for the `φ`-denominator sum. -/
theorem pairWeightDivPhi_eq_integral_pairKernelPhasePhi {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (q R : ℕ) (hR : 1 < R) (x : Fin k → ℕ × ℕ) :
    pairWeightDivPhi F G q R x = ∫ p : Fin k → ℝ × ℝ, pairKernelPhasePhi F G q R x p := by
  classical
  rw [pairWeightDivPhi_apply]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
    have hexp : (∏ j : Fin k, (mobiusTotientWeight q (x j).1 (x j).2 *
          (F j (logR (x j).1 R) : ℂ) * (G j (logR (x j).2 R) : ℂ))) =
        ∏ j : Fin k, (mobiusTotientWeight q (x j).1 (x j).2 *
          (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ) *
          (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [divisorForm_fourierCut (F j) (hcsF j) (hsmF j) R (x j).1,
        divisorForm_fourierCut (G j) (hcsG j) (hsmG j) R (x j).2]
    rw [hexp, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hint : (∏ j : Fin k, (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ)) *
        (∏ j : Fin k, (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')) =
        ∫ p : Fin k → ℝ × ℝ, ∏ j : Fin k,
          ((divisorPhase R (x j).1 (p j).1 * fourierCut (F j) (p j).1) *
            (divisorPhase R (x j).2 (p j).2 * fourierCut (G j) (p j).2)) := by
      rw [← Finset.prod_mul_distrib]
      rw [show (∏ j : Fin k, ((∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ) *
            (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ'))) =
          ∏ j : Fin k, (∫ u : ℝ × ℝ,
            (divisorPhase R (x j).1 u.1 * fourierCut (F j) u.1) *
            (divisorPhase R (x j).2 u.2 * fourierCut (G j) u.2)) from
        Finset.prod_congr rfl (fun j _ => integral_mul_integral_eq _ _)]
      rw [← MeasureTheory.integral_fintype_prod_volume_eq_prod
        (fun j (u : ℝ × ℝ) => (divisorPhase R (x j).1 u.1 * fourierCut (F j) u.1) *
          (divisorPhase R (x j).2 u.2 * fourierCut (G j) u.2))]
    rw [show (∏ j : Fin k, mobiusTotientWeight q (x j).1 (x j).2) *
          (∏ j : Fin k, (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ)) *
          (∏ j : Fin k, (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')) =
        (∏ j : Fin k, mobiusTotientWeight q (x j).1 (x j).2) *
          ((∏ j : Fin k, (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ)) *
            (∏ j : Fin k, (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')))
        from by ring]
    rw [hint, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    rw [pairKernelPhasePhi_apply, if_pos hg]
    dsimp only
    simp only [Finset.prod_mul_distrib]
    ring
  · rw [if_neg hg]
    rw [show (∫ p : Fin k → ℝ × ℝ, pairKernelPhasePhi F G q R x p) =
        ∫ p : Fin k → ℝ × ℝ, 0 from by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      rw [pairKernelPhasePhi_apply, if_neg hg]]
    simp

/-! ## The `φ`-Fubini identity -/

/-- The per-term `φ`-kernel is the guarded `φ`-kernel weight times the Fourier
transforms of the cutoffs. -/
lemma pairKernelPhasePhi_eq_kernelWeightKPhi_mul {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hR : 1 < R) (x : Fin k → ℕ × ℕ) (p : Fin k → ℝ × ℝ) :
    pairKernelPhasePhi F G q R x p =
      pairKernelWeightPhi q (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) x *
        ∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2) := by
  classical
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [pairKernelPhasePhi_apply, if_pos hg, pairKernelWeightPhi, if_pos hg,
      kernelWeightKPhi]
    have hkern : ∀ j : Fin k, kernelWeightPhi
        (logZ (-(2 * Real.pi * (p j).1)) R) (logZ (-(2 * Real.pi * (p j).2)) R) (x j) =
        mobiusTotientWeight q (x j).1 (x j).2 * divisorPhase R (x j).1 (p j).1 *
          divisorPhase R (x j).2 (p j).2 := by
      intro j
      have h := kernelWeightPhi_eq_phase_mul q R (x j).1 (x j).2 hR (hg.1 j) (p j).1 (p j).2
      rw [h]
    rw [Finset.prod_congr rfl (fun j _ => hkern j)]
    simp only [Finset.prod_mul_distrib]
  · rw [pairKernelPhasePhi_apply, if_neg hg, pairKernelWeightPhi, if_neg hg, zero_mul]

/-- **The `φ`-Fubini identity, in terms of the ℕ-level sum.** -/
theorem pairwiseDivisorSumPhi_eq_kernelSumIntegralPhi {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (q R : ℕ) (hq : q ≠ 0) (hR : 1 < R) :
    (∑' x : Fin k → ℕ × ℕ, pairWeightDivPhi F G q R x) =
      ∫ p : Fin k → ℝ × ℝ, pairKernelSumPhi q
          (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) := by
  classical
  have hterm : ∀ x : Fin k → ℕ × ℕ,
      pairWeightDivPhi F G q R x = ∫ p : Fin k → ℝ × ℝ, pairKernelPhasePhi F G q R x p :=
    fun x => pairWeightDivPhi_eq_integral_pairKernelPhasePhi F G hcsF hsmF hcsG hsmG q R hR x
  have hInt : ∀ x : Fin k → ℕ × ℕ, Integrable (pairKernelPhasePhi F G q R x) :=
    fun x => integrable_pairKernelPhasePhi F G q R hcsF hsmF hcsG hsmG hR x
  have hSumm : Summable fun x : Fin k → ℕ × ℕ =>
      ∫ p : Fin k → ℝ × ℝ, ‖pairKernelPhasePhi F G q R x p‖ :=
    summable_integral_norm_pairKernelPhasePhi F G q R hcsF hsmF hcsG hsmG hR
  calc (∑' x : Fin k → ℕ × ℕ, pairWeightDivPhi F G q R x)
      = ∑' x : Fin k → ℕ × ℕ, ∫ p : Fin k → ℝ × ℝ, pairKernelPhasePhi F G q R x p :=
        tsum_congr hterm
    _ = ∫ p : Fin k → ℝ × ℝ, ∑' x : Fin k → ℕ × ℕ, pairKernelPhasePhi F G q R x p :=
        integral_tsum_of_summable_integral_norm hInt hSumm
    _ = ∫ p : Fin k → ℝ × ℝ, pairKernelSumPhi q
          (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        have h1 : (∑' x : Fin k → ℕ × ℕ, pairKernelPhasePhi F G q R x p) =
            ∑' x : Fin k → ℕ × ℕ, (pairKernelWeightPhi q
                (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
                (fun j => logZ (-(2 * Real.pi * (p j).2)) R) x *
              ∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) :=
          tsum_congr (fun x => pairKernelPhasePhi_eq_kernelWeightKPhi_mul F G q R hR x p)
        rw [h1, tsum_mul_right, pairKernelSumPhi]

/-- **The `φ`-denominator Fubini identity** (Lemma 4.1 with `φ([d,d′])`
denominators). -/
theorem pairwiseDivisorSumPhi_eq_kernelIntegralPhi {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (q R : ℕ) (hq : q ≠ 0) (hR : 1 < R) :
    (∑' x : Fin k → ℕ × ℕ, pairWeightDivPhi F G q R x) =
      ∫ p : Fin k → ℝ × ℝ, pairKernelPhi q
          (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) := by
  rw [pairwiseDivisorSumPhi_eq_kernelSumIntegralPhi F G hcsF hsmF hcsG hsmG q R hq hR]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hlt : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).1)) R).re := fun j => by
    rw [logZ_re]; exact div_pos one_pos hlog
  have hrt : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).2)) R).re := fun j => by
    rw [logZ_re]; exact div_pos one_pos hlog
  rw [pairKernelSumPhi_eq_pairKernelPhi q hq hlt hrt]

end Commons.NumberTheory.MaynardSieve
