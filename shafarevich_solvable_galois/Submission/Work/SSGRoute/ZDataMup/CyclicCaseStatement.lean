import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclic case of the conductor drop at the ramified primes

`Work.SSGRoute.ZDataMup.CyclicCaseStatement` is the statement of
`Work.SSGRoute.ZDataMup.artinSym_spanSingleton_eq_one_of_ramifiedCongr` with the hypothesis
`IsCyclic (L ≃ₐ[K] L)` added: for a **cyclic** extension `L/K` of number fields, a modulus `M > 0`
whose prime divisors are unramified in `L` (`hramM`) and for which the ideal-theoretic reciprocity
law holds (`hprincM`), and `b ∈ Kˣ` congruent to `1` modulo `M` at every ramified prime dividing
`M` (`hcong`) and totally positive (`hpos`), the Artin symbol of the principal ideal `(b)` is
trivial.

It is stated as a `Prop` so that the reduction of the abelian case to the cyclic one (via the
cyclic quotients `Gal(L/K) ⧸ H`, `iInf_subgroup_isCyclic_quotient`) can be delegated without
importing the final target.
-/

namespace Work.SSGRoute.ZDataMup

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- The statement of the conductor drop `artinSym (b·𝒪_K) = 1` for a **cyclic** extension. -/
def CyclicCaseStatement : Prop :=
  ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (M : ℕ) (hM : 0 < M)
    (hramM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprincM : NK.CFTLib.artinKillsPrincipal K L M)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))),
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1

end Work.SSGRoute.ZDataMup
