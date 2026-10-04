import Mathlib
import Submission.Work.Diff.STE.fourierCoeff_pdVec_normSq
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.wt_pow_le_wordSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_ge_weighted_fourierCoeff`: the energy dominates the weighted Fourier sum

For a `C^k`, `1`-periodic function `P` on `ι → ℝ` (the flat torus of the STE development),
the physical-space energy of order `k`,

  `ENormSq k P = Σ_{l : Fin k → ι} ∫_{unitCube} ‖∂^l P‖²`

dominates the weighted Fourier sum

  `(2π)^{2k} Σ_{m : ι → ℤ} (Σᵢ mᵢ²)^k ‖û(m)‖²`.

The proof is a short Fourier computation, in the direction *opposite* to the Sobolev
comparison `CSq_le_ENormSq` (there the weight `⟨m⟩^{2k} = (1 + Σ mᵢ²)^k` is bounded above by
the energy; here the weight is the pure `(Σ mᵢ²)^k`, which is what the `2π`-scaled derivative
multipliers produce *exactly* on the Fourier side).

* The Fourier multiplier of `∂^l` is `∏_{i} 2πi m_{l i}`, so by
  `fourierCoeff_pdVec_normSq`

    `‖\widehat{∂^l P}(m)‖² = (∏_{i} (2π m_{l i})²) ‖û(m)‖²`.

* Summing over all words `l : Fin k → ι` and using the multinomial expansion `wordSum_eq`,

    `Σ_l ∏_{i} (2π m_{l i})² = (Σᵢ (2π mᵢ)²)^k = (2π)^{2k} (Σᵢ mᵢ²)^k`,

  so the weighted Fourier sum is `(2π)^{-2k}` times `Σ_m Σ_l ‖\widehat{∂^l P}(m)‖²`.

* Interchanging the finite sum over `l` with the sum over `m` and applying Bessel's
  inequality (`bessel_continuous`) to each `∂^l P` gives

    `Σ_m Σ_l ‖\widehat{∂^l P}(m)‖² = Σ_l Σ_m ‖\widehat{∂^l P}(m)‖²
       ≤ Σ_l ∫_{unitCube} ‖∂^l P‖² = ENormSq k P`.

This is exactly the estimate needed to compare the `Hᵏ` energy used in the Galerkin
estimates with the weighted `ℓ²` norm of the Fourier coefficients.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

theorem ENormSq_ge_weighted_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (P : (ι → ℝ) → ℂ) (hP : ContDiff ℝ k P)
    (hper : Work.Diff.STE.Periodic1 P) :
    Summable (fun m : ι → ℤ =>
        (∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2) ∧
      (2 * Real.pi) ^ (2 * k) * (∑' m : ι → ℤ,
          (∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k * ‖Work.Diff.STE.fourierCoeff P m‖ ^ 2)
        ≤ Work.Diff.STE.ENormSq k P := by
  classical
  -- the hypothesis `1 ≤ k` is not needed by the argument below (which even covers `k = 0`),
  -- but it is part of the requested statement
  have hk' : (0 : ℕ) < k := hk
  clear hk'
  -- Bessel's inequality for each iterated derivative `∂^l P`
  have hB : ∀ l : Fin k → ι,
      Summable (fun m : ι → ℤ => ‖fourierCoeff (pdVec k l P) m‖ ^ 2) ∧
        (∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l P) m‖ ^ 2)
          ≤ ∫ x in unitCube, ‖pdVec k l P x‖ ^ 2 :=
    fun l => bessel_continuous (pdVec k l P) (continuous_pdVec k l P hP)
  have hderiv : ∀ l : Fin k → ι,
      Summable (fun m : ι → ℤ => ‖fourierCoeff (pdVec k l P) m‖ ^ 2) :=
    fun l => (hB l).1
  have hderiv_le : ∀ l : Fin k → ι,
      (∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l P) m‖ ^ 2)
        ≤ ∫ x in unitCube, ‖pdVec k l P x‖ ^ 2 :=
    fun l => (hB l).2
  -- the sum over the (finitely many) words `l` is summable
  have hsum_l : Summable (fun m : ι → ℤ =>
      ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l P) m‖ ^ 2) :=
    summable_sum (fun l _ => hderiv l)
  -- the pointwise identification of the word sum with the weighted coefficient
  have hpt : ∀ m : ι → ℤ,
      (∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l P) m‖ ^ 2)
        = (2 * Real.pi) ^ (2 * k)
            * ((∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k * ‖fourierCoeff P m‖ ^ 2) := by
    intro m
    have hsum_eq : (∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l P) m‖ ^ 2)
        = ∑ l : Fin k → ι,
            (∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2)
              * ‖fourierCoeff P m‖ ^ 2 :=
      Finset.sum_congr rfl (fun l _ => fourierCoeff_pdVec_normSq k l P hP hper m)
    rw [hsum_eq, ← Finset.sum_mul, wordSum_eq k m, mul_pow]
    rw [show ((2 * Real.pi) ^ 2) ^ k = (2 * Real.pi) ^ (2 * k) from (pow_mul _ 2 k).symm]
    ring
  -- `(2π)^{2k} ≥ 1`, so the weighted family is dominated by the summable word-sum family
  have htwo_pi_one : (1 : ℝ) ≤ (2 * Real.pi) ^ (2 * k) := by
    have hp : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    calc (1 : ℝ) = 1 ^ (2 * k) := (one_pow _).symm
      _ ≤ (2 * Real.pi) ^ (2 * k) := pow_le_pow_left₀ (by norm_num) hp _
  have hSnn : ∀ m : ι → ℤ, 0 ≤ (∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k :=
    fun m => pow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) k
  have htarget_sum : Summable (fun m : ι → ℤ =>
      (∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k * ‖fourierCoeff P m‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hSnn m) (sq_nonneg _)) ?_ hsum_l
    intro m
    rw [hpt m]
    exact le_mul_of_one_le_left (mul_nonneg (hSnn m) (sq_nonneg _)) htwo_pi_one
  refine ⟨htarget_sum, ?_⟩
  rw [← tsum_mul_left]
  calc (∑' m : ι → ℤ, (2 * Real.pi) ^ (2 * k)
        * ((∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k * ‖fourierCoeff P m‖ ^ 2))
      = ∑' m : ι → ℤ, ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l P) m‖ ^ 2 :=
        tsum_congr (fun m => (hpt m).symm)
    _ = ∑ l : Fin k → ι, ∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l P) m‖ ^ 2 :=
        Summable.tsum_finsetSum (s := Finset.univ) (fun l _ => hderiv l)
    _ ≤ ∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l P x‖ ^ 2 :=
        Finset.sum_le_sum (fun l _ => hderiv_le l)
    _ = ENormSq k P := rfl

end Work.Diff.STE.B3
