import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.AdjustId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every fractional ideal coprime to `𝔪` is the ideal of an idèle of `U(𝔪)`

The ideal-modulus analogue of `NK.CFTLib.ARL.exists_idealOf_eq_of_mem_Icoprime`: the natural map
`U(𝔪) → I(𝔪)`,
`x ↦ (x)` from the congruence subgroup of the modulus `𝔪` to the group of fractional ideals
coprime to `𝔪`, is surjective.

The idèle is the one with `𝔭`-adic exponent `count K 𝔭 𝔞` (`IdeleClassGroup.ideleOfFun`) and value
`1` at every archimedean place: its exponents vanish at every `𝔭 | 𝔪`, which is exactly the local
congruence condition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NK.GlobalCFT NK.CFTLib.ArtinReciprocityIdeal

/-- **Surjectivity of `U(𝔪) → I(𝔪)`.**  Every fractional ideal `𝔞` coprime to `𝔪 ≠ ⊥` is the ideal
of an idèle of the congruence subgroup `U(𝔪)`. -/
theorem exists_idealOf_eq_of_mem_idealCoprimeGroupId
    {K : Type} [Field K] [NumberField K]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (𝔞 : NK.CFTLib.ArtinReciprocityIdeal.Frac K)
    (h𝔞 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 𝔞) :
    ∃ x : NK.GlobalCFT.Idele K,
      x ∈ NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 ∧
        NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K x = 𝔞 := by
  classical
  set f : HeightOneSpectrum (𝓞 K) → ℤ :=
    fun 𝔭 => FractionalIdeal.count K 𝔭 (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hf_def
  have hf : ∀ᶠ 𝔭 in Filter.cofinite, f 𝔭 = 0 :=
    FractionalIdeal.finite_factors (K := K) (I := (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
  refine ⟨IdeleClassGroup.ideleOfFun K f hf, ?_, ?_⟩
  · rw [mem_congruenceSubgroupId]
    constructor
    · intro 𝔭 h𝔭
      have hf0 : f 𝔭 = 0 := by
        rw [hf_def]
        exact h𝔞 𝔭 ((dvdPrime_iff_one_le_count h𝔪 𝔭).mpr h𝔭)
      have hx1 : IdeleClassGroup.ideleOfFun K f hf (Place.ofFinite 𝔭) = 1 := by
        apply Units.ext
        change ((IdeleClassGroup.unifUnit K 𝔭 ^ (f 𝔭) : (𝔭.adicCompletion K)ˣ) :
          𝔭.adicCompletion K) = 1
        rw [hf0, zpow_zero]
        rfl
      rw [hx1]
      exact congrAtId_one 𝔭 𝔪
    · intro w
      exact NK.CFTLib.Arl.posAtReal_one w
  · refine Units.ext ?_
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0]
    exact IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _) 𝔞.ne_zero
      (fun 𝔭 => by rw [IdeleClassGroup.count_idealOf_ideleOfFun])

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
