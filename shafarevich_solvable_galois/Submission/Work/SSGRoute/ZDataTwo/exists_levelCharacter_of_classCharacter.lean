import Mathlib
import Submission.Work.SSGRoute.N2v2.orthogonality_hsplit_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

theorem exists_levelCharacter_of_classCharacter
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F]
    [NumberField ↥F] [IsMulCommutative (↥F ≃ₐ[↥K] ↥F)]
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥F ≃ₐ[↥K] ↥F))
    (hker : Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥F ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) Q →
      Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥F) Q)
    (χ : NK.GlobalCFT.IdeleClassGroup ↥K →* Multiplicative (ZMod 2))
    (hχ : NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥F ≤ χ.ker) :
    ∃ χE : (↥F ≃ₐ[↥K] ↥F) →* Multiplicative (ZMod 2),
      ∀ y : NK.GlobalCFT.Idele ↥K,
        χE (Φ y) = χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K y) := by
  classical
  -- The Artin map `Φ` is surjective, because it is normalised by the Frobenius elements.
  have hcomm : ∀ a b : (↥F ≃ₐ[↥K] ↥F), a * b = b * a := fun a b => mul_comm' a b
  have hsurj : Function.Surjective Φ :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified hcomm Φ hfrob
  -- `χ ∘ mk` kills the kernel of `Φ`: it kills the principal idèles (definition of `χ` on `C_K`)
  -- and the idèlic norms (`hχ`).
  have hker_le : Φ.ker ≤ (χ.comp (NK.GlobalCFT.IdeleClassGroup.mk ↥K)).ker := by
    intro x hx
    have hxsup : x ∈ NK.GlobalCFT.Idele.normImage ↥K ↥F ⊔
        NK.GlobalCFT.Idele.principalSubgroup ↥K := by
      rw [← hker]; exact hx
    rw [Subgroup.mem_sup] at hxsup
    obtain ⟨a, ha, b, hb, hab⟩ := hxsup
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hab, map_mul]
    have ha' : χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K a) = 1 :=
      MonoidHom.mem_ker.mp (hχ (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
    have hb' : NK.GlobalCFT.IdeleClassGroup.mk ↥K b = 1 := by
      rw [NK.GlobalCFT.IdeleClassGroup.mk_apply, QuotientGroup.eq_one_iff]; exact hb
    rw [map_mul, ha', hb', map_one, one_mul]
  -- On idèles with the same `Φ`-image, `χ ∘ mk` takes the same value.
  have hcongr : ∀ a b : NK.GlobalCFT.Idele ↥K, Φ a = Φ b →
      χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K a) =
        χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K b) := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ Φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : ((χ.comp (NK.GlobalCFT.IdeleClassGroup.mk ↥K)) a)⁻¹ *
        ((χ.comp (NK.GlobalCFT.IdeleClassGroup.mk ↥K)) b) = 1 := by
      have h3 := MonoidHom.mem_ker.mp (hker_le h1)
      rwa [map_mul, map_inv] at h3
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h2
    exact inv_mul_eq_one.mp h2
  -- Descend `χ ∘ mk` along the surjection `Φ`.
  refine ⟨{ toFun := fun g =>
              χ (NK.GlobalCFT.IdeleClassGroup.mk ↥K (Classical.choose (hsurj g))),
            map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · have h1 : Classical.choose (hsurj 1) ∈ Φ.ker := by
      rw [MonoidHom.mem_ker]; exact Classical.choose_spec (hsurj 1)
    have h2 := MonoidHom.mem_ker.mp (hker_le h1)
    simpa using h2
  · intro g g'
    have hgcd : Φ (Classical.choose (hsurj (g * g'))) =
        Φ (Classical.choose (hsurj g) * Classical.choose (hsurj g')) := by
      rw [map_mul, Classical.choose_spec (hsurj g), Classical.choose_spec (hsurj g'),
        Classical.choose_spec (hsurj (g * g'))]
    rw [hcongr _ _ hgcd, map_mul, map_mul]
  · intro y
    exact hcongr _ _ (Classical.choose_spec (hsurj (Φ y)))

end Work.SSGRoute.ZDataTwo
