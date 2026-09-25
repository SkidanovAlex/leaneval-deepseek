/-
The exponential of the logarithmic Euler product of an Artin `L`-series.

`NK.HeckeL.artinLogEulerProduct` is the sum of the principal logarithms `-log (1 - χ(Frob_𝔭) N𝔭^{-s})`
of the Euler factors of `NK.HeckeL.artinLSeries`.  For `s > 1` the family
`χ(Frob_𝔭) N𝔭^{-s}` is summable and of norm `N𝔭^{-s} < 1`, so each Euler factor is a genuine
logarithm and exponentiating the sum of the logarithms gives back the Euler product.
-/
import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors Topology
open Filter

noncomputable section

namespace NK.HeckeL.Series

/-- **`exp` of a sum of logarithms is the corresponding Euler product.**

If `f : ι → ℂ` is summable and `‖f i‖ < 1` for every `i`, then `1 - f i ≠ 0`, so the principal
logarithm `Complex.log (1 - f i)` is a genuine logarithm of the Euler factor `(1 - f i)⁻¹`.
Consequently, exponentiating the (summable) series of principal logarithms returns the infinite
product of the Euler factors. -/
lemma exp_tsum_neg_log_one_sub_eq_tprod {ι : Type*} (f : ι → ℂ) (hf : Summable f)
    (h1 : ∀ i, ‖f i‖ < 1) :
    Complex.exp (∑' i, -Complex.log (1 - f i)) = ∏' i, (1 - f i)⁻¹ := by
  have hne : ∀ i, 1 - f i ≠ 0 := by
    intro i h
    have hfi : (1 : ℂ) = f i := sub_eq_zero.mp h
    have hlt := h1 i
    rw [← hfi, norm_one] at hlt
    exact absurd hlt (lt_irrefl 1)
  have hsum : Summable fun i => -Complex.log (1 - f i) := hf.clog_one_sub.neg
  have hcongr : (Complex.exp ∘ fun i => -Complex.log (1 - f i)) = fun i => (1 - f i)⁻¹ := by
    funext i
    rw [Function.comp_apply, Complex.exp_neg, Complex.exp_log (hne i)]
  have h := hsum.hasSum.cexp
  rw [hcongr] at h
  exact h.tprod_eq.symm

theorem exp_artinLogEulerProduct {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (χ : Gal(L/K) →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    Complex.exp (NK.HeckeL.artinLogEulerProduct K L S χ s) =
      NK.HeckeL.artinLSeries K L S χ s := by
  -- the summability of the underlying family `𝔭 ↦ χ(Frob_𝔭) · N𝔭^{-s}`
  have hbase : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) := by
    exact (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs).subtype
      (fun 𝔭 : NK.HeckeL.PrimeIdeal K => 𝔭 ∉ S)
  have hnorm {𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}} :
      ‖(((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖
        = (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hf : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
        (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) := by
    refine Summable.of_norm_bounded hbase (fun 𝔭 => ?_)
    rw [norm_mul, NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ _, one_mul, hnorm]
  have h1 : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      ‖(χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
        (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖ < 1 := by
    intro 𝔭
    rw [norm_mul, NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ _, one_mul, hnorm]
    exact Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one
      (lt_trans zero_lt_one hs) 𝔭.1
  have hmain := exp_tsum_neg_log_one_sub_eq_tprod
    (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
        (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) hf h1
  simpa only [NK.HeckeL.artinLogEulerProduct, NK.HeckeL.artinLSeries,
    NK.HeckeL.artinEulerFactor] using hmain

end NK.HeckeL.Series
