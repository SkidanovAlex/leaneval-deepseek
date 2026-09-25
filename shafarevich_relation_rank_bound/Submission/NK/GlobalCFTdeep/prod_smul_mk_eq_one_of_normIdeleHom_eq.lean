import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT

namespace NK.GlobalCFTdeep

/-- If an idèle `y` of `L` has norm the principal idèle of `a ∈ Kˣ`, then the product over
`Gal(L/K)` of the translates of its class in the idèle class group `C_L` is trivial.

Route: choose a place of `L` over each place of `K` and the corresponding inclusion
`φ : 𝕀 K →* 𝕀 L` (`Inclusion.globalCFT_exists_placeUnder`, `Inclusion.globalCFT_ideleInclusion_exists`);
then `∏ σ, σ • mk L y = mk L (∏ σ, σ • y)` (`IdeleClassGroup.smul_mk` and `map_prod`),
`∏ σ, σ • y = φ (normIdeleHom K L y)` (`Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom`),
`φ (principalIdele K a) = principalIdele L a` (`Inclusion.globalCFT_ideleInclusion_principalIdele`)
and `mk L (principalIdele L a) = 1` because the principal idèles lie in the subgroup that is
quotiented out. -/
theorem prod_smul_mk_eq_one_of_normIdeleHom_eq {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (y : NK.GlobalCFT.Idele L) (a : Kˣ)
    (h : NK.GlobalCFT.Idele.normIdeleHom K L y = NK.GlobalCFT.Idele.principalIdele K a) :
    (∏ σ : L ≃ₐ[K] L, σ • NK.GlobalCFT.IdeleClassGroup.mk L y) = 1 := by
  classical
  -- a compatible choice of a place of `L` over each place of `K`
  obtain ⟨u, hu⟩ : ∃ u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K,
      ∀ w, NK.GlobalCFT.Place.LiesOver w (u w) :=
    ⟨fun w => Classical.choose
        (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w),
     fun w => Classical.choose_spec
        (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)⟩
  -- the idèle inclusion `φ : 𝕀 K →* 𝕀 L` attached to it
  obtain ⟨φ, hφ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := L) u hu
  -- move `mk L` out of the product, using that it is a monoid homomorphism
  rw [Finset.prod_congr rfl (fun σ _ => NK.GlobalCFT.IdeleClassGroup.smul_mk σ y)]
  rw [← map_prod]
  -- rewrite the product of the conjugates of `y` as the image of the norm of `y`
  rw [NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom u hu φ hφ y, h,
    NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele u hu φ hφ a]
  -- the principal idèles are exactly the subgroup that has been quotiented out
  show (NK.GlobalCFT.Idele.principalIdele L (Units.map (algebraMap K L) a) :
      NK.GlobalCFT.Idele L ⧸ NK.GlobalCFT.Idele.principalSubgroup L) = 1
  exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩

end NK.GlobalCFTdeep
