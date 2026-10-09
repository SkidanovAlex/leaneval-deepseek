import Mathlib
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Work.SSGRoute.levelSub_commutator_and_generator
import Submission.Work.SSGRoute.levelSub_comap_index_eq_inertiaDeg
import Submission.Work.SSGRoute.primeOfLevel_mem_iff_k
import Submission.Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level subgroup is the preimage of the level inertia

Let `k` be a number field, `Ω` an algebraic closure of `k`, `A` a finite place of `Ω` over `k` and
`M ⊆ Ω` a finite normal level.  For `δ` in the decomposition group `D_A = SSGRoute.decomp k A` the
following are equivalent:

* `δ` acts trivially on the level `A ∩ M` modulo the maximal ideal of `A` (`δ ∈ levelSub A M`);
* `δ` acts trivially on the residue field of the prime `P` of `𝓞 M` below `A`
  (`Work.SSGRoute.IsTrivialAtLevel`);
* the restriction of `δ` to `M` lies in the inertia subgroup of `Gal(M/k)` at `P`
  (`Ideal.inertia`).

The passage between the first and the second item is the two-way dictionary between the *valuation*
form of residue-field triviality (the form in which `levelSub` is defined) and the *residue-field*
form used to state `Ideal.inertia`; the passage between the second and the third item is
`Work.SSGRoute.mem_inertia_levelPrime_iff_isTrivialAtLevel`.
-/

namespace Work.SSGRoute

open scoped Pointwise NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **Residue-field triviality from the level subgroup.**

If `δ ∈ D_A` acts trivially on `A ∩ M` modulo the maximal ideal of `A`, then it acts trivially on
the residue field of the prime `P` of `𝓞 M` below `A`: for `x : 𝓞 M` the difference
`galRestrict (res δ) x - x` has `A`-adic value `< 1`, because `𝓞 M ⊆ A ∩ M`
(`ringOfIntegers_mem_of_isFinPlace_k`) and because `< 1` for the `A`-adic valuation is membership
of `P` (`primeOfLevel_mem_iff_k`). -/
theorem isTrivialAtLevel_of_mem_levelSub
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (g : Ω ≃ₐ[k] Ω) (hg : g ∈ Work.SSGRoute.levelSub A M) :
    Work.SSGRoute.IsTrivialAtLevel k Ω A hA M g := by
  haveI hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  intro x
  rw [Work.SSGRoute.primeOfLevel_mem_iff_k k Ω A hA M]
  set z : ↥M := algebraMap (𝓞 ↥M) ↥M x with hz
  have hzA : z ∈ A.comap (algebraMap ↥M Ω) := by
    rw [ValuationSubring.mem_comap, hz]
    exact Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k k Ω A hA M x
  have hval : A.valuation (g (algebraMap ↥M Ω z) - algebraMap ↥M Ω z) < 1 :=
    hg.2 ⟨z, hzA⟩
  have hgoal : algebraMap (𝓞 ↥M) Ω
      (galRestrict (𝓞 k) k ↥M (𝓞 ↥M) (AlgEquiv.restrictNormalHom M g) x - x)
      = algebraMap ↥M Ω ((AlgEquiv.restrictNormalHom M g) z - z) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 ↥M) ↥M Ω, map_sub, ← hz,
      algebraMap_galRestrict_apply]
  have hkey : g (algebraMap ↥M Ω z) - algebraMap ↥M Ω z
      = algebraMap ↥M Ω ((AlgEquiv.restrictNormalHom M g) z - z) := by
    rw [map_sub]
    congr 1
    exact (AlgEquiv.restrictNormalHom_apply M g z).symm
  rw [hgoal, ← hkey]
  exact hval

/-- **The level subgroup from residue-field triviality.**

Conversely, an element of `D_A` acting trivially on the residue field of `P` acts trivially on
`A ∩ M` modulo the maximal ideal: this is `valuation_sub_lt_one_of_isTrivialAtLevel` applied to
the elements of `𝓞 M ⊆ A ∩ M`. -/
theorem mem_levelSub_of_isTrivialAtLevel
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (g : Ω ≃ₐ[k] Ω) (hg : g ∈ SSGRoute.decomp k A)
    (htriv : Work.SSGRoute.IsTrivialAtLevel k Ω A hA M g) :
    g ∈ Work.SSGRoute.levelSub A M := by
  refine ⟨hg, fun x => ?_⟩
  exact Work.SSGRoute.valuation_sub_lt_one_of_isTrivialAtLevel A hA M g hg htriv
    (y := ((x : ↥M) : Ω)) (x : ↥M).2 ((ValuationSubring.mem_comap).mp x.2)

/-- **The level subgroup is the preimage of the level inertia** (the requested lemma): for `δ` in
the decomposition group `D_A` of a finite place `A` of `Ω` over the number field `k` and a finite
normal level `M ⊆ Ω`, `δ` lies in `levelSub A M` exactly when its restriction to `M` lies in the
inertia subgroup of `Gal(M/k)` at the prime `P` of `𝓞 M` below `A`. -/
theorem mem_levelSub_iff_mem_inertia
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (δ : ↥(SSGRoute.decomp k A)) :
    ((δ : Ω ≃ₐ[k] Ω) ∈ Work.SSGRoute.levelSub A M) ↔
      AlgEquiv.restrictNormalHom M (δ : Ω ≃ₐ[k] Ω) ∈
        Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal := by
  rw [Work.SSGRoute.mem_inertia_levelPrime_iff_isTrivialAtLevel A hA M (δ : Ω ≃ₐ[k] Ω)]
  exact ⟨fun h => Work.SSGRoute.isTrivialAtLevel_of_mem_levelSub A hA M (δ : Ω ≃ₐ[k] Ω) h,
    fun h => Work.SSGRoute.mem_levelSub_of_isTrivialAtLevel A hA M (δ : Ω ≃ₐ[k] Ω) δ.2 h⟩

end Work.SSGRoute
