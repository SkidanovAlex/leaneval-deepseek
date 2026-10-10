import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.TameStructureDeep.Tame.Kummer
import Submission.NK.TameStructureDeep.Tame.exists_adjoin_primitiveRoot_of_mem_unramifiedClosure
import Submission.NK.TameStructureDeep.Tame.no_pow_root_adjoin_primitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open Polynomial

set_option maxHeartbeats 1000000

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- A uniformiser of the discrete valuation ring `𝒪_κ = 𝔭.adicCompletionIntegers K` exists. -/
theorem exists_isUniformizerAt :
    ∃ π : 𝔭.adicCompletionIntegers K, IsUniformizerAt 𝔭 π := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (𝔭.adicCompletionIntegers K)
  exact ⟨π, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ⟩

/-- **The Kummer input, pointwise, unconditionally.**  For every uniformiser `π` of `𝒪_κ`, every
`n ≥ 2` prime to the residue characteristic and every `α` in the maximal unramified extension,
`α ^ n ≠ π`. -/
theorem noPowRootAt_of_isUniformizerAt {K' : Type*} [Field K']
    [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) :
    NoPowRootAt 𝔭 π K' := by
  refine ⟨hπ, fun n hn hcop α hα => ?_⟩
  -- `α` lies in a single primitive-root layer `κ⟮ζ⟯`, `p ∤ m`
  have hp : (resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨m, ζ, hm, hζ, hαm⟩ :=
    exists_adjoin_primitiveRoot_of_mem_unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
      hp hα
  exact no_pow_root_adjoin_primitiveRoot 𝔭 hπ hn hm hζ ⟨α, hαm⟩

/-- **The Kummer input, unconditionally, at every place.**  For a number field `K`, a finite prime
`𝔭` and a separable closure `K'` of `κ = K_𝔭`, some uniformiser `π` of `𝒪_κ` has no `n`-th root in
the maximal unramified extension `κ^{ur}`, for every `n ≥ 2` prime to the residue characteristic. -/
theorem unramifiedNoPow_adicCompletion {K' : Type*} [Field K']
    [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    UnramifiedNoPow 𝔭 K' := by
  obtain ⟨π, hπ⟩ := exists_isUniformizerAt 𝔭
  exact ⟨π, noPowRootAt_of_isUniformizerAt 𝔭 hπ⟩

/-- **Kummer over `κ^{ur}`, unconditionally.**  For every prime `ℓ` different from the residue
characteristic, the polynomial `X ^ ℓ - C π` is irreducible over `κ^{ur}`: hence
`Gal(κ^{ur}(π^{1/ℓ})/κ^{ur}) ≅ μ_ℓ` with the Kummer pairing, and
`[κ^{ur}(π^{1/ℓ}) : κ^{ur}] = ℓ`. -/
theorem irreducible_X_pow_sub_C_unramifiedClosure' {K' : Type*} [Field K']
    [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ resCharAt 𝔭) :
    Irreducible (X ^ ℓ - C (uniformizerInClosure 𝔭 (K' := K') π)) :=
  irreducible_X_pow_sub_C_unramifiedClosure 𝔭 hℓ hℓp
    (fun α hα => (noPowRootAt_of_isUniformizerAt 𝔭 hπ).2 ℓ hℓ.two_le hcop α hα)
  where
    hcop : ℓ.Coprime (resCharAt 𝔭) := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd (NK.Mine.prime_ringChar_residueField_adicCompletion
        𝔭)).mpr (fun h => hℓp ((hℓ.dvd_iff_eq (NK.Mine.prime_ringChar_residueField_adicCompletion
          𝔭).ne_one).mp h))

end

end NK.TameStructureDeep.Tame
