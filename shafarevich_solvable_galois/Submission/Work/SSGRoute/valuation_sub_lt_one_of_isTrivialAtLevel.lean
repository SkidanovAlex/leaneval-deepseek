import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Work.SSGRoute.valuation_lt_one_algebraMap_iff
import Submission.Work.SSGRoute.valuation_lt_one_of_inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Triviality on a level residue field implies triviality on the local ring

Let `k` be a number field, `Ω` an algebraic closure of `k`, `B` a place of `Ω` over a finite prime
of `k` and `L ⊆ Ω` a finite normal level.  Write `P_L` for the prime of `𝓞 L` below `B`; the
isomorphism `B ∩ L = O_{L,P_L}` is `NK.Reconstruct.primeOfLevel_spec`, i.e. `B ∩ L` is the
localization of `𝓞 L` at `P_L`.

If `σ ∈ G_k` acts trivially on the residue field `𝓞 L / P_L` of the level `L`
(`Work.SSGRoute.IsTrivialAtLevel`), then for every `y ∈ L` which is `B`-integral the difference
`σ y - y` lies in the maximal ideal of `B`, i.e. has `B.valuation`-value `< 1`.

The proof splits into two independent general lemmas:

* `Work.SSGRoute.valuation_lt_one_algebraMap_iff` transfers the comparison `< 1` along the
  restriction `L ⧸ B ∩ L` of a valuation ring to a finite extension (`W.comap = O`);
* `Work.SSGRoute.valuation_lt_one_of_inertia` is the local computation: on the localization
  `O_{L,P_L}` of a Dedekind domain, an endomorphism which is congruent to the identity modulo
  `P_L` on `𝓞 L` is congruent to the identity modulo `P_L O_{L,P_L}`.
-/

open scoped NumberField

set_option linter.unusedVariables false

namespace Work.SSGRoute

theorem valuation_sub_lt_one_of_isTrivialAtLevel {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (B : ValuationSubring Ω) (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k B)
    (htriv : Work.SSGRoute.IsTrivialAtLevel k Ω B hB L σ)
    {y : Ω} (hyL : y ∈ L) (hyB : y ∈ B) : B.valuation (σ y - y) < 1 := by
  -- The prime of `𝓞 L` below `B`, and the local ring `A = O_{L,P}`.
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L) :=
    NK.Reconstruct.primeOfLevel B L (NK.Reconstruct.comap_level_ne_top hB L)
  let A : ValuationSubring ↥L :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P
  have hspec : B.comap (algebraMap ↥L Ω) = A := NK.Reconstruct.primeOfLevel_spec B L _
  -- `y`, viewed as an element of `L`, is integral at `P`.
  let yL : ↥L := ⟨y, hyL⟩
  have hya : yL ∈ A := by
    rw [← hspec, ValuationSubring.mem_comap]
    exact hyB
  -- The hypothesis, in the raw form in which the local computation consumes it.
  have htriv' : ∀ x : 𝓞 ↥L,
      galRestrict (𝓞 k) k ↥L (𝓞 ↥L) (AlgEquiv.restrictNormalHom L σ) x - x ∈ P.asIdeal := htriv
  -- The local computation at `P`.
  have hcore : P.valuation ↥L ((AlgEquiv.restrictNormalHom L σ) yL - yL) < 1 := by
    refine valuation_lt_one_of_inertia (P := P)
      ((AlgEquiv.restrictNormalHom L σ : ↥L ≃ₐ[k] ↥L) : ↥L →+* ↥L)
      ((galRestrict (𝓞 k) k ↥L (𝓞 ↥L) (AlgEquiv.restrictNormalHom L σ) :
        𝓞 ↥L ≃ₐ[𝓞 k] 𝓞 ↥L) : 𝓞 ↥L →+* 𝓞 ↥L) ?_ ?_ ?_
    · intro x
      exact (algebraMap_galRestrict_apply (A := 𝓞 k) (K := k) (L := ↥L) (B := 𝓞 ↥L) _ x).symm
    · intro x
      exact htriv' x
    · have : yL ∈ (P.valuation ↥L).valuationSubring := by
        rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
        exact hya
      exact (Valuation.mem_valuationSubring_iff _ _).mp this
  -- Transfer the conclusion to the local ring `A` of the level.
  have heq : A.valuation.IsEquiv (P.valuation ↥L) := by
    rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation]
    exact IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring P
  have hA : A.valuation ((AlgEquiv.restrictNormalHom L σ) yL - yL) < 1 :=
    (Valuation.IsEquiv.lt_one_iff_lt_one heq).mpr hcore
  -- Transfer to the valuation ring `B` of `Ω`.
  have hBv : B.valuation (algebraMap ↥L Ω ((AlgEquiv.restrictNormalHom L σ) yL - yL)) < 1 :=
    (valuation_lt_one_algebraMap_iff B A hspec _).mpr hA
  -- Identify the element with `σ y - y`.
  have hz : algebraMap ↥L Ω ((AlgEquiv.restrictNormalHom L σ) yL - yL) = σ y - y := by
    have h1 : algebraMap ↥L Ω ((AlgEquiv.restrictNormalHom L σ) yL) = σ y :=
      AlgEquiv.restrictNormalHom_apply L σ yL
    have h2 : algebraMap ↥L Ω yL = y := rfl
    rw [map_sub, h1, h2]
  rw [hz] at hBv
  exact hBv

end Work.SSGRoute
