import Mathlib
import Submission.NK.HeckeL.Product.dedekindZeta_eulerProduct
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal

open scoped BigOperators
open NK.HeckeL

namespace NK.HeckeL.Nonvanishing

/-- **The unramified Euler product of `L` versus the full Dedekind zeta function.**

Splitting the Euler product of the Dedekind zeta function of `L` at the finite set `T` of primes
lying over the modulus `S`, the product `zetaUnramified K L S s` over the primes of `L` outside `T`
is the full Dedekind zeta value of `L` at `s`, multiplied by the Euler factors at the primes of
`T`; and those factors are precisely the reciprocal factors that were removed. -/
theorem zetaUnramified_eq_dedekindZeta_mul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (T : Finset (NK.HeckeL.PrimeIdeal L))
    (hT : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L, 𝔮 ∈ T ↔ ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal)
    {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.zetaUnramified K L S s =
      ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) *
        ∏ 𝔮 ∈ T, (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) := by
  classical
  -- The two local factors: `φ` is the Euler factor, `ψ = φ⁻¹` its inverse.
  let φ : PrimeIdeal L → ℂ :=
    fun 𝔮 => (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
  let ψ : PrimeIdeal L → ℂ :=
    fun 𝔮 => 1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)
  have hs0 : (0:ℝ) < s := lt_trans zero_lt_one hs
  -- The Euler factor is the reciprocal of a positive real number, and its logarithm is summable.
  have hposg : ∀ 𝔭 : PrimeIdeal L,
      0 < Commons.NumberTheory.NumberField.DedekindZeta.localFactor L s 𝔭.asIdeal := by
    intro 𝔭
    rw [Commons.NumberTheory.NumberField.DedekindZeta.localFactor]
    exact inv_pos.mpr (sub_pos.mpr
      (Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one (K:=L) hs0 𝔭))
  have hsumlog : Summable (fun 𝔭 : PrimeIdeal L =>
      Real.log (Commons.NumberTheory.NumberField.DedekindZeta.localFactor L s 𝔭.asIdeal)) :=
    Commons.NumberTheory.NumberField.DedekindZeta.summable_log_localFactor (K := L) hs
  -- Hence the product of the local factors over the primes outside `T` is multipliable.
  have hmultR : Multipliable (fun 𝔮 : {𝔮 : PrimeIdeal L // 𝔮 ∉ T} =>
      Commons.NumberTheory.NumberField.DedekindZeta.localFactor L s 𝔮.1.asIdeal) :=
    Real.multipliable_of_summable_log (fun 𝔮 => hposg 𝔮.1) (hsumlog.subtype (fun 𝔮 => 𝔮 ∉ T))
  have hbase : ∀ 𝔮 : PrimeIdeal L,
      ((Commons.NumberTheory.NumberField.DedekindZeta.localFactor L s 𝔮.asIdeal : ℝ) : ℂ) = φ 𝔮 := by
    intro 𝔮
    simp only [φ, Commons.NumberTheory.NumberField.DedekindZeta.localFactor]
    simp only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
  have hmultC : Multipliable (fun 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∉ T}) => φ 𝔮) :=
    (hmultR.map Complex.ofRealHom Complex.continuous_ofReal).congr (fun 𝔮 => hbase 𝔮.1)
  -- The product over the finite set `T` is multipliable (finiteness).
  have hmultT : Multipliable (fun 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∈ T}) => φ 𝔮) :=
    (T.hasProd φ).multipliable
  -- The primes outside `T` are exactly those lying over no prime of `S`.
  have hset : {𝔮 : PrimeIdeal L | ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal} =
      {𝔮 : PrimeIdeal L | 𝔮 ∉ T} := by
    ext 𝔮
    simp only [Set.mem_ofPred_eq, hT 𝔮, not_exists, not_and]
  have hzeta : zetaUnramified K L S s =
      ∏' 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∉ T}), φ 𝔮 := by
    unfold NK.HeckeL.zetaUnramified
    exact tprod_congr_set_coe φ hset
  -- Splitting the Euler product of `L` at `T`.
  have hsplit := Multipliable.tprod_mul_tprod_compl (f := φ)
    (s := {𝔮 : PrimeIdeal L | 𝔮 ∈ T}) hmultT hmultC
  have hsplit' : (∏ 𝔮 ∈ T, φ 𝔮) *
      (∏' 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∉ T}), φ 𝔮) = ∏' 𝔮 : PrimeIdeal L, φ 𝔮 := by
    rw [← Finset.tprod_subtype T φ]
    exact hsplit
  have hD : ∏' 𝔮 : PrimeIdeal L, φ 𝔮 = ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) := by
    simp only [φ]
    exact NK.HeckeL.Product.dedekindZeta_eulerProduct (K := L) hs
  -- The product over `T` of the reciprocal factors is the inverse of the product over `T`.
  have hAG : (∏ 𝔮 ∈ T, φ 𝔮) * (∏ 𝔮 ∈ T, ψ 𝔮) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro 𝔮 h𝔮
    have hxne : (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) ≠ 1 :=
      ne_of_lt (Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one (K:=L) hs0 𝔮)
    have hψ : ψ 𝔮 ≠ 0 := by
      simp only [ψ]
      intro h
      have h1 : (1:ℂ) = (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) := sub_eq_zero.mp h
      exact hxne (Complex.ofReal_injective (by simpa using h1.symm))
    show (ψ 𝔮)⁻¹ * ψ 𝔮 = 1
    exact inv_mul_cancel₀ hψ
  rw [hzeta]
  calc ∏' 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∉ T}), φ 𝔮
      = 1 * (∏' 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∉ T}), φ 𝔮) := (one_mul _).symm
    _ = ((∏ 𝔮 ∈ T, φ 𝔮) * (∏ 𝔮 ∈ T, ψ 𝔮)) *
          (∏' 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∉ T}), φ 𝔮) := by rw [hAG]
    _ = (∏ 𝔮 ∈ T, ψ 𝔮) *
          ((∏ 𝔮 ∈ T, φ 𝔮) * (∏' 𝔮 : ↑({𝔮 : PrimeIdeal L | 𝔮 ∉ T}), φ 𝔮)) := by ring
    _ = (∏ 𝔮 ∈ T, ψ 𝔮) * ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) := by rw [hsplit', hD]
    _ = ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) * ∏ 𝔮 ∈ T, ψ 𝔮 := by ring

end NK.HeckeL.Nonvanishing
