import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HeckeL.Series

open scoped BigOperators Classical Topology

/-- A convergent sum splits into its restriction to a finset and the sum over the complement. -/
lemma tsum_eq_sum_add_tsum_compl {α : Type*} (f : α → ℂ) (S : Finset α) (h : Summable f) :
    ∑' x, f x = (∑ x ∈ S, f x) + ∑' x : {x // x ∉ S}, f x := by
  have hkey := h.sum_add_tsum_compl (s := S)
  rw [← hkey]
  congr 1

/-- The character-twisted prime sum over **all** the primes of `K` splits, for any finite set `S`
of primes, into the finite sum over `S` plus the character-twisted prime sum over the primes
outside `S`.  The analytic content is the convergence of `∑_𝔭 N𝔭^{-s}` for `s > 1`
(`summable_primeIdealNorm`), which makes `tsum` additive over the complementary subtypes. -/
theorem charPrimeSum_eq_sum_add_artinPrimeSum {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (ψ : Gal(L/K) →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    NK.Chebotarev.charPrimeSum (K := K) (L := L) (NK.HeckeL.galoisToComplex ψ) s =
      (∑ 𝔭 ∈ S, NK.HeckeL.galoisToComplex ψ
          (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) *
        (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) +
      NK.HeckeL.artinPrimeSum K L S ψ s := by
  haveI : Fintype Gal(L/K) := AlgEquiv.fintype K L
  let f : NK.HeckeL.PrimeIdeal K → ℂ := fun 𝔭 =>
    (ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
      (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)
  have hsumm : Summable f := by
    refine ((Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K hs).congr
      (fun 𝔭 => ?_)).of_norm
    rw [show f 𝔭 = (ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : ℂ) *
        (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) from rfl, norm_mul,
      NK.Chebotarev.norm_monoidHom_units_apply_eq_one, one_mul]
    simp [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  change (∑' 𝔭 : NK.HeckeL.PrimeIdeal K, f 𝔭) = (∑ 𝔭 ∈ S, f 𝔭) + ∑' 𝔭 : {𝔭 // 𝔭 ∉ S}, f 𝔭
  exact tsum_eq_sum_add_tsum_compl f S hsumm

end NK.HeckeL.Series
