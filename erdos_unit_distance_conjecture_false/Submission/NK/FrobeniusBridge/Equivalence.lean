import Submission.NK.FrobeniusBridge.Main
import Submission.NK.FrobeniusBridge.mem_decompositionGroup_of_isFrobAtPlace
import Submission.NK.FrobeniusBridge.isTrivialOnResidueAtLevel_mul_inv_of_frobAt
import Submission.NK.FrobeniusBridge.isFrobElement_of_isFrobAtPlace
import Submission.NK.FrobeniusBridge.exists_isFrobAtPlace

/-!
# The Frobenius bridge: the two vocabularies agree

This file proves that, given the local–global dictionary `NK.FrobeniusBridge.PlaceLevelBridge`
and its inertia half `NK.FrobeniusBridge.InertiaLevelBridge` at a place `A`, the *infinite-level*
(residue-field, "for every finite normal level") Frobenius predicate
`NK.FrobeniusBridge.IsFrobAtPlace A` and the *local* predicate
`NK.FrobeniusBridge.localFrobAt A` describe the same subset of `Gal(K'/K)` — the Frobenius coset
of the decomposition group `D_A`, modulo the inertia subgroup `I_A`.

Consequently the two natural forms of the hypothesis `hB` of the deliverable — the local one
(`NK.FrobeniusBridge.LocalFrobCorrespondencePlace`) and the "for every finite normal level" one —
are equivalent for an isomorphism `ϕ` of absolute Galois groups
(`NK.FrobeniusBridge.localFrobCorrespondencePlace_iff_allLevels`).
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local Frobenius condition is not vacuous at a place satisfying the dictionary**: the
existence of a place-level Frobenius element (`NK.FrobeniusBridge.exists_isFrobAtPlace`, which is
unconditional) and the local–global dictionary produce an element of `localFrobAt A`. -/
theorem PlaceLevelBridge.exists_localFrob {A : FinitePlaceOf K K'} (hD : PlaceLevelBridge A) :
    ∃ g : Gal(K'/K), localFrobAt A g := by
  obtain ⟨g, hg⟩ := exists_isFrobAtPlace A
  obtain ⟨g₀, -, hloc⟩ := hD.local_of_level (⊥ : IntermediateField K K') g (hg ⊥)
  exact ⟨g₀, hloc⟩

/-- **The two vocabularies agree.**  Given the local–global dictionary and its inertia half at the
place `A`, an element of `Gal(K'/K)` is a Frobenius element at `A` at every finite normal level if
and only if it is a local Frobenius lift at `A`.

The proof of the non-trivial direction: if `g` is a Frobenius element at every level, pick a local
Frobenius lift `u` agreeing with `g` on some level (`local_of_level`); then `g * u⁻¹` is a
Frobenius element at every level (from `local_of_level` for `u`), so `g * u⁻¹` acts trivially on
the residue field of every level, hence (inertia half) lies in the local inertia subgroup; as the
Frobenius lifts form a coset of the inertia subgroup
(`NK.LocalTame.IsFrobeniusFor.mul_mem_inertia`), `g = (g * u⁻¹) * u` is again a local Frobenius
lift. -/
theorem isFrobAtPlace_iff_localFrob {A : FinitePlaceOf K K'} (hD : PlaceLevelBridge A)
    (hI : InertiaLevelBridge A) (g : Gal(K'/K)) :
    IsFrobAtPlace A g ↔ localFrobAt A g := by
  constructor
  · intro h
    have : NumberField ↥(⊥ : IntermediateField K K') :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField _
    -- a local Frobenius lift agreeing with `g` on the bottom level
    obtain ⟨u, -, hloc_u⟩ := hD.local_of_level (⊥ : IntermediateField K K') g (h ⊥)
    -- `g` lies in the decomposition group of `A`
    have hgD : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 :=
      mem_decompositionGroup_of_isFrobAtPlace h
    -- `g * u⁻¹` acts trivially on the residue field of every level
    have htriv : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
        [NumberField ↥L], IsTrivialOnResidueAtLevel A L (g * u⁻¹) := fun L _ _ _ =>
      isTrivialOnResidueAtLevel_mul_inv_of_frobAt A L (h L) (hD.level_of_local L u hloc_u)
    obtain ⟨huD, p, q, hT, hZ, hF_u⟩ := hloc_u
    have hguD : g * u⁻¹ ∈
        Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 :=
      Subgroup.mul_mem _ hgD (Subgroup.inv_mem _ huD)
    -- hence it is a local inertia element
    have hin : localGaloisEquiv A ⟨g * u⁻¹, hguD⟩ ∈
        NK.LocalAnabelian.inertiaSubgroup (κ := localField A) (K' := localClosure A) p :=
      hI.inertia_of_levels (g * u⁻¹) htriv p q hT hguD
    refine ⟨hgD, p, q, hT, hZ, ?_⟩
    -- `g = (g * u⁻¹) * u`, and the Frobenius lifts form a coset of the inertia subgroup
    have hcoset : NK.LocalAnabelian.IsFrobeniusFor p q
        (localGaloisEquiv A ⟨g * u⁻¹, hguD⟩ * localGaloisEquiv A ⟨u, huD⟩) :=
      NK.LocalTame.IsFrobeniusFor.mul_mem_inertia hT hF_u hin
    have hsub : (⟨g * u⁻¹, hguD⟩ : Submission.NeukirchUchida.decompositionGroup
          (K₁ := K) (K₁' := K') A.1) * ⟨u, huD⟩ = ⟨g, hgD⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    have hval : localGaloisEquiv A ⟨g * u⁻¹, hguD⟩ * localGaloisEquiv A ⟨u, huD⟩ =
        localGaloisEquiv A ⟨g, hgD⟩ := by
      rw [← map_mul, hsub]
    rwa [hval] at hcoset
  · intro hloc
    exact localFrobAt.isFrobAtPlace hD hloc

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The two forms of the hypothesis `hB` are equivalent**: given the local–global dictionary and
its inertia half at the places of both fields, the place-level Frobenius correspondence for `ϕ`
stated in the local vocabulary is equivalent to the statement that `ϕ` carries the infinite-level
Frobenius elements at a place to the infinite-level Frobenius elements at the corresponding place. -/
theorem localFrobCorrespondencePlace_iff_allLevels (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hD₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridge A)
    (hI₁ : ∀ A : FinitePlaceOf K₁ K₁', InertiaLevelBridge A)
    (hD₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridge B)
    (hI₂ : ∀ B : FinitePlaceOf K₂ K₂', InertiaLevelBridge B) :
    LocalFrobCorrespondencePlace ϕ hϕ a ↔
      ∀ (A : FinitePlaceOf K₁ K₁') (g : Gal(K₁'/K₁)),
        IsFrobAtPlace A g → IsFrobAtPlace (a.placeMap A) (ϕ g) := by
  constructor
  · intro hB A g hg
    exact localFrobAt.isFrobAtPlace (hD₂ (a.placeMap A))
      (hB A g ((isFrobAtPlace_iff_localFrob (hD₁ A) (hI₁ A) g).mp hg))
  · intro hB A g hg
    exact (isFrobAtPlace_iff_localFrob (hD₂ (a.placeMap A)) (hI₂ (a.placeMap A)) (ϕ g)).mp
      (hB A g ((isFrobAtPlace_iff_localFrob (hD₁ A) (hI₁ A) g).mpr hg))

end NK.FrobeniusBridge
