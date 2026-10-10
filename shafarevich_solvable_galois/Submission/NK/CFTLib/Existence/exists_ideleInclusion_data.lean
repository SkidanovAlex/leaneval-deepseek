import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Existence

theorem exists_ideleInclusion_data
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K ↥L] [NumberField ↥L] :
    ∃ (u₀ : NK.GlobalCFT.Place ↥L → NK.GlobalCFT.Place K)
      (hu₀ : ∀ w, NK.GlobalCFT.Place.LiesOver w (u₀ w))
      (φ₀ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele ↥L)
      (ι : NK.GlobalCFT.IdeleClassGroup K →* NK.GlobalCFT.IdeleClassGroup ↥L)
      (u₂ : NK.GlobalCFT.Place Ω → NK.GlobalCFT.Place ↥L)
      (hu₂ : ∀ w, NK.GlobalCFT.Place.LiesOver w (u₂ w))
      (φ₂ : NK.GlobalCFT.Idele ↥L →* NK.GlobalCFT.Idele Ω)
      (ψ₂ : NK.GlobalCFT.IdeleClassGroup ↥L →* NK.GlobalCFT.IdeleClassGroup Ω)
      (φ₁ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele Ω)
      (ψ₁ : NK.GlobalCFT.IdeleClassGroup K →* NK.GlobalCFT.IdeleClassGroup Ω),
      (∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place ↥L),
        φ₀ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u₀ w) (hu₀ w) (x (u₀ w))) ∧
      (∀ x : NK.GlobalCFT.Idele K,
        ι (NK.GlobalCFT.IdeleClassGroup.mk K x)
          = NK.GlobalCFT.IdeleClassGroup.mk ↥L (φ₀ x)) ∧
      (∀ (x : NK.GlobalCFT.Idele ↥L) (w : NK.GlobalCFT.Place Ω),
        φ₂ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u₂ w) (hu₂ w) (x (u₂ w))) ∧
      (∀ x : NK.GlobalCFT.Idele ↥L,
        ψ₂ (NK.GlobalCFT.IdeleClassGroup.mk ↥L x)
          = NK.GlobalCFT.IdeleClassGroup.mk Ω (φ₂ x)) ∧
      (∀ x : NK.GlobalCFT.Idele K, φ₁ x = φ₂ (φ₀ x)) ∧
(∀ x : NK.GlobalCFT.Idele K,
        ψ₁ (NK.GlobalCFT.IdeleClassGroup.mk K x)
          = NK.GlobalCFT.IdeleClassGroup.mk Ω (φ₁ x)) := by
  classical
  -- `Ω` is finite over the intermediate field `L`
  haveI : FiniteDimensional ↥L Ω := IntermediateField.finiteDimensional_right L
  -- a place of `L` over each place of `K`
  let u₀ : NK.GlobalCFT.Place ↥L → NK.GlobalCFT.Place K := fun w =>
    Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w)
  have hu₀ : ∀ w, NK.GlobalCFT.Place.LiesOver w (u₀ w) := fun w =>
    Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w)
  -- the inclusion of idèles and of idèle class groups `K → L`
  obtain ⟨φ₀, hφ₀⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists u₀ hu₀
  obtain ⟨ι, hι⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u₀ hu₀ φ₀ hφ₀
  -- a place of `Ω` over each place of `L`
  let u₂ : NK.GlobalCFT.Place Ω → NK.GlobalCFT.Place ↥L := fun w =>
    Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := ↥L) (L := Ω) w)
  have hu₂ : ∀ w, NK.GlobalCFT.Place.LiesOver w (u₂ w) := fun w =>
    Classical.choose_spec
      (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := ↥L) (L := Ω) w)
  -- the inclusion of idèles and of idèle class groups `L → Ω`
  obtain ⟨φ₂, hφ₂⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists u₂ hu₂
  obtain ⟨ψ₂, hψ₂⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u₂ hu₂ φ₂ hφ₂
  -- `K → Ω` is the composite, on both idèles and idèle class groups
  exact ⟨u₀, hu₀, φ₀, ι, u₂, hu₂, φ₂, ψ₂, φ₂.comp φ₀, ψ₂.comp ι, hφ₀, hι, hφ₂, hψ₂,
    fun _ => rfl, fun x => by
      simp only [MonoidHom.comp_apply]
      rw [hι x]
      exact hψ₂ (φ₀ x)⟩


end NK.CFTLib.Existence
