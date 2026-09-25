/-
Work of the Neukirch–Uchida team: the general Čebotarev density theorem.

# Auxiliary lemmas for the density form of the transfer

* the primes of an intermediate field have residue degree at least one over the prime below;
* the fibre decomposition of a Dirichlet series in the set-builder form used by the transfer.
-/
import Mathlib
import Submission.NK.ChebotarevGeneral.Basic
import Submission.NK.ChebotarevGeneral.primeIdealZetaSum_eq_tsum_fibre
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log

namespace NK.ChebotarevGeneral

noncomputable section

open IsDedekindDomain
open NK.Chebotarev

/-- **The set of all finite places of a number field has Dirichlet density one.** -/
theorem hasDirichletDensity_univ (K : Type*) [Field K] [NumberField K] :
    NumberField.Set.HasDirichletDensity (Set.univ : Set (PrimeIdeal K)) 1 :=
  Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log (by
    simpa using Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log K)

set_option linter.unusedSectionVars false

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [FiniteDimensional K M]

/-- **A prime of `M` has residue degree at least one over the prime of `K` below it.** -/
theorem one_le_inertiaDeg'_under (𝒬 : NK.Chebotarev.PrimeIdeal M) :
    1 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal := by
  haveI : 𝒬.asIdeal.LiesOver (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal) :=
    (Ideal.liesOver_iff _ _).mpr rfl
  have hpos := Ideal.inertiaDeg'_pos (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal) 𝒬.asIdeal
  omega

/-- **The fibre decomposition of a Dirichlet series, set-builder form.** -/
theorem primeIdealZetaSum_eq_tsum_fibre' {S : Set (NK.Chebotarev.PrimeIdeal M)}
    (hS : ∀ 𝒬 ∈ S,
      (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1)
    {s : ℝ} (hs : 1 < s) :
    NumberField.Set.primeIdealZetaSum S s =
      ∑' 𝔭 : NK.Chebotarev.PrimeIdeal K,
        (Nat.card {𝒬 : NK.Chebotarev.PrimeIdeal M //
            𝒬 ∈ S ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal} : ℝ) *
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  rw [primeIdealZetaSum_eq_tsum_fibre hS hs]
  refine tsum_congr fun 𝔭 => ?_
  congr 1
  have e : {𝒬 : S // (𝒬 : NK.Chebotarev.PrimeIdeal M).asIdeal.LiesOver 𝔭.asIdeal} ≃
      {𝒬 : NK.Chebotarev.PrimeIdeal M // 𝒬 ∈ S ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  exact_mod_cast Nat.card_congr e

end

end NK.ChebotarevGeneral
