import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.isProP_le_inertiaSubgroup
import Submission.NK.TameStructureDeep.Tame.WildInertiaAux
import Submission.NK.RamificationAdic.exists_valuationRingData
import Submission.NK.RamificationDeep.UnitMap
import Submission.NK.RamificationDeep.RamificationDeterminesSubfields
import Submission.NK.TameStructureDeep.Tame.pow_class_unramifiedClosure
import Submission.NK.TameStructureDeep.Tame.isProP_fixingSubgroup_of_relIndex_prime_pow
import Submission.NK.TameStructureDeep.Tame.isProPrimeToP_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.relIndex_inf_fixingSubgroup_eq_finrank
import Submission.NK.TameStructureDeep.Tame.tameClosure_inf_finrank_prime_pow

/-!
# Pro-`p`-ness of the corrected wild inertia `V_κ = Gal(K'/κ^{tr})`

Let `K` be a number field, `𝔭` a finite place, `κ = K_𝔭` its `𝔭`-adic completion,
`p = resCharAt 𝔭` the residue characteristic, `K'` a separable closure of `κ`, `π` a uniformizer of
`κ` and `κ^{tr} = tameClosure p π = κ^{ur}(π^{1/n} : p ∤ n)` the maximal tamely ramified extension.
The *corrected wild inertia* is

  `V_κ = correctedWildInertia p π = Gal(K'/κ^{tr}) = (tameClosure p π).fixingSubgroup`,

and this file proves that it is a pro-`p` group (`NK.LocalTame.IsProP p`).

## The route

* `NK.TameStructureDeep.Tame.isProP_fixingSubgroup_of_relIndex_prime_pow` (proved) reduces the
  statement to the finite-level index condition

  `h : ∀ M ≤ K' finite Galois over κ, ∃ k, [V_κ : V_κ ⊓ Gal(K'/M)] = p ^ k`.

* `NK.TameStructureDeep.Tame.relIndex_inf_fixingSubgroup_eq_finrank` (proved) identifies the
  relative index with the degree over the maximal tamely ramified subextension:

  `[V_κ : V_κ ⊓ Gal(K'/M)] = [M : M ⊓ κ^{tr}]`.

  (The companion lemma `relIndex_fixingSubgroup_eq_finrank` below records the same identity for the
  tame closure `T = κ^{tr}` in the field-theoretic form `[T ⊔ M : T]`.)

* `NK.TameStructureDeep.Tame.tameClosure_inf_finrank_prime_pow` (proved) is the arithmetic
  content: **`[M : M ⊓ κ^{tr}]` is a power of `p`** for every finite-dimensional Galois extension
  `M/κ` inside `K'` — the classical statement that the wild inertia of a finite Galois extension of
  local fields is a `p`-group (`M^{G_1} ⊆ κ^{tr}`, together with `#G_1 = p^j`).
-/

open scoped Classical
open IntermediateField

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
  [IsSepClosure (𝔭.adicCompletion K) K']

/-- **The relative index occurring in the finite-level condition is the degree of the compositum.**

For a finite-dimensional Galois extension `M/κ` inside `K'` and the maximal tamely ramified
extension `T = κ^{tr}`,

  `[V_κ : V_κ ⊓ Gal(K'/M)] = [T ⊔ M : T]`,

where `V_κ = Gal(K'/T)`.  This is the Galois bookkeeping of `index_subgroupOf_fixingSubgroup`
together with `(T ⊔ M).fixingSubgroup = T.fixingSubgroup ⊓ M.fixingSubgroup`. -/
theorem relIndex_fixingSubgroup_eq_finrank {π : 𝔭.adicCompletionIntegers K}
    (M : IntermediateField (𝔭.adicCompletion K) K')
    [FiniteDimensional (𝔭.adicCompletion K) M] [IsGalois (𝔭.adicCompletion K) M] :
    ((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup ⊓
        M.fixingSubgroup).relIndex
      (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup
      = Module.finrank
          ↥(NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K))
          (IntermediateField.extendScalars
            (le_sup_left : NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K)
              (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) ≤
              NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
                (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) ⊔ M)) := by
  have h := index_subgroupOf_fixingSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
    (U := NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K))
    (F := NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) ⊔ M) le_sup_left
  have h2 : M.fixingSubgroup.subgroupOf
        (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup
      = (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) ⊔ M).fixingSubgroup.subgroupOf
        (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.inf_subgroupOf_left]
  rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left, h2]
  exact h

theorem isProP_correctedWildInertia_indep {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) :
    NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      ↥(NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup := by
  refine NK.TameStructureDeep.Tame.isProP_fixingSubgroup_of_relIndex_prime_pow 𝔭 hπ ?_
  intro M hfd hgal
  haveI := hfd
  haveI := hgal
  obtain ⟨k, hk⟩ :=
    NK.TameStructureDeep.Tame.tameClosure_inf_finrank_prime_pow 𝔭 hπ M
  refine ⟨k, ?_⟩
  rw [NK.TameStructureDeep.Tame.relIndex_inf_fixingSubgroup_eq_finrank, hk]

end

end NK.TameStructureDeep.Tame
