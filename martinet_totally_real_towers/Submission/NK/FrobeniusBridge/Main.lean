import Submission.NK.FrobeniusBridge.Bridge
import Submission.NK.FrobeniusBridge.LevelAPI

/-!
# The Frobenius bridge: the main theorems

* `NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_bridge` — the place-level Frobenius
  correspondence in the *local* vocabulary (`LocalFrobCorrespondencePlace`) plus the local–global
  dictionary at the places of both fields imply the finite-level correspondence
  `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a` consumed by the Neukirch–Uchida endgame;
* `NK.FrobeniusBridge.frobeniusCorrespondencePlace` — the same, in the bundled form in which the
  endgame states its input `(b)`.
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The "down" half of the dictionary gives the infinite-level predicate**: a local Frobenius
lift restricts to a Frobenius element at every finite normal level. -/
theorem localFrobAt.isFrobAtPlace {A : FinitePlaceOf K K'} (hD : PlaceLevelBridge A)
    {g : Gal(K'/K)} (hg : localFrobAt A g) : IsFrobAtPlace A g :=
  fun L _ _ _ => hD.level_of_local L g hg

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The Frobenius bridge, main theorem.**  The place-level Frobenius correspondence for `ϕ`
(stated in the local vocabulary of `NK.LocalTame`, i.e. through the action on the prime-to-`p`
roots of unity of the local fields) together with the local–global dictionary
`NK.FrobeniusBridge.PlaceLevelBridge` at the places of the two fields implies the finite-level,
σ-free Frobenius correspondence `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a` — input (b)
of the Neukirch–Uchida endgame.

The proof is the "lift and descend" argument: an element which is a Frobenius element at the level
`L` agrees on `L` with a local Frobenius lift `g₀ ∈ D_A` (`PlaceLevelBridge.local_of_level`); the
place-level correspondence carries `g₀` to a local Frobenius lift at `B = a.placeMap A`, which
restricts to a Frobenius element at the level `levelMap ϕ L` (`PlaceLevelBridge.level_of_local`);
and `ϕ g` and `ϕ g₀` have the same restriction to `levelMap ϕ L` because `g g₀⁻¹` fixes `L` and
`ϕ` carries `Gal(K₁'/L)` onto `Gal(K₂'/levelMap ϕ L)`
(`NK.Reconstruct.fixingSubgroup_levelMap`). -/
theorem frobeniusCorrespondencePlace_of_bridge (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hD₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridge A)
    (hD₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridge B)
    (hB : LocalFrobCorrespondencePlace ϕ hϕ a) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a := by
  intro L _ _ _ _ _ A g hg
  -- a local Frobenius lift agreeing with `g` on `L`
  obtain ⟨g₀, hg₀, hloc⟩ := (hD₁ A).local_of_level L g hg
  -- its image is a local Frobenius lift at the corresponding place
  have hloc' : localFrobAt (a.placeMap A) (ϕ g₀) := hB A g₀ hloc
  -- which restricts to a Frobenius element at the corresponding level
  have hfrob : frobAtLevel (a.placeMap A) (NK.Reconstruct.levelMap ϕ L) (ϕ g₀) :=
    (hD₂ (a.placeMap A)).level_of_local (NK.Reconstruct.levelMap ϕ L) (ϕ g₀) hloc'
  -- and `ϕ g` has the same restriction as `ϕ g₀`
  have hcongr : AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g₀) =
      AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) := by
    rw [restrictNormalHom_eq_iff_mem_fixingSubgroup]
    rw [NK.Reconstruct.fixingSubgroup_levelMap hϕ L]
    exact Subgroup.mem_map.mpr
      ⟨g₀ * g⁻¹, (restrictNormalHom_eq_iff_mem_fixingSubgroup g₀ g).mp hg₀, by simp⟩
  exact (frobAtLevel_congr (a.placeMap A) (NK.Reconstruct.levelMap ϕ L) hcongr).mp hfrob

/-- **The Frobenius bridge in the form consumed by the endgame**: input (b) of
`Submission.NeukirchUchida.exists_sigma_of_reconstruction` holds as soon as the bundle
`NK.FrobeniusBridge.PlaceFrobeniusData` of the local–global dictionary at the places of the two
fields and the place-level Frobenius correspondence for `ϕ` is available. -/
theorem frobeniusCorrespondencePlace (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (hB : PlaceFrobeniusData ϕ hϕ a) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  frobeniusCorrespondencePlace_of_bridge ϕ hϕ a hB.bridge₁ hB.bridge₂ hB.correspondence

/-- **The Frobenius bridge with the hypothesis stated at the infinite level**: the same conclusion
as `frobeniusCorrespondencePlace_of_bridge`, but with the place-level correspondence for `ϕ` stated
in the global, σ-free vocabulary of `NK.FrobeniusBridge.IsFrobAtPlace` ("`g` is a Frobenius
element at the place `A` at *every* finite normal level") instead of in the local vocabulary.

The proof uses `PlaceLevelBridge.local_of_level` to replace the element by a *local* Frobenius lift
agreeing with it on the level at hand, and `PlaceLevelBridge.level_of_local` (via
`localFrobAt.isFrobAtPlace`) to pass between the two vocabularies at the level of elements. -/
theorem frobeniusCorrespondencePlace_of_allLevels (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hD₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridge A)
    (hD₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridge B)
    (hB : ∀ (A : FinitePlaceOf K₁ K₁') (g : Gal(K₁'/K₁)),
      IsFrobAtPlace A g → IsFrobAtPlace (a.placeMap A) (ϕ g)) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a := by
  intro L _ _ _ _ _ A g hg
  -- a local Frobenius lift agreeing with `g` on `L`, hence a place-level Frobenius element
  obtain ⟨g₀, hg₀, hloc⟩ := (hD₁ A).local_of_level L g hg
  have hplace : IsFrobAtPlace A g₀ := localFrobAt.isFrobAtPlace (hD₁ A) hloc
  -- its image is a place-level Frobenius element at the corresponding place
  have hplace' : IsFrobAtPlace (a.placeMap A) (ϕ g₀) := hB A g₀ hplace
  -- and so a level-wise Frobenius element at the corresponding level
  have hfrob : frobAtLevel (a.placeMap A) (NK.Reconstruct.levelMap ϕ L) (ϕ g₀) :=
    hplace'.frobAtLevel _
  have hcongr : AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g₀) =
      AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) := by
    rw [restrictNormalHom_eq_iff_mem_fixingSubgroup]
    rw [NK.Reconstruct.fixingSubgroup_levelMap hϕ L]
    exact Subgroup.mem_map.mpr
      ⟨g₀ * g⁻¹, (restrictNormalHom_eq_iff_mem_fixingSubgroup g₀ g).mp hg₀, by simp⟩
  exact (frobAtLevel_congr (a.placeMap A) (NK.Reconstruct.levelMap ϕ L) hcongr).mp hfrob

end NK.FrobeniusBridge
