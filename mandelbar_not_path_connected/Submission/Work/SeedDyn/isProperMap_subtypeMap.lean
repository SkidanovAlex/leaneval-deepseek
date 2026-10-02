import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

/-- The map induced on subtypes by a map which is continuous on `U` and whose preimages of
compact subsets of `V` (intersected with `U`) are compact, is a proper map. -/
theorem isProperMap_subtypeMap {U V : Set ℂ} {f : ℂ → ℂ} (hm : ∀ z ∈ U, f z ∈ V)
    (hcont : ContinuousOn f U)
    (hcpt : ∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, w ∈ V) → IsCompact (U ∩ f ⁻¹' K)) :
    IsProperMap (Subtype.map f (fun z hz => hm z hz)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨?_, ?_⟩
  · exact hcont.mapsToRestrict hm
  · intro K hK
    -- `K` is compact in `↥V`; push it forward to a compact set of `ℂ` contained in `V`.
    have hK' : IsCompact ((Subtype.val '' K : Set ℂ)) := hK.image continuous_subtype_val
    have hV' : ∀ w ∈ (Subtype.val '' K : Set ℂ), w ∈ V := by
      rintro w ⟨k, -, rfl⟩
      exact k.2
    have hcomp : IsCompact (U ∩ f ⁻¹' (Subtype.val '' K : Set ℂ)) := hcpt _ hK' hV'
    -- Compactness in the subtype `↥U` is compactness of the coerced subset.
    rw [Subtype.isCompact_iff]
    have hset : (Subtype.val '' ((Subtype.map f (fun z hz => hm z hz)) ⁻¹' K) : Set ℂ)
        = U ∩ f ⁻¹' (Subtype.val '' K : Set ℂ) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, ⟨Subtype.map f (fun z hz => hm z hz) x, hx, rfl⟩⟩
      · rintro ⟨hzU, k, hkK, hkf⟩
        refine ⟨⟨z, hzU⟩, ?_, rfl⟩
        have hgk : Subtype.map f (fun z hz => hm z hz) ⟨z, hzU⟩ = k := by
          apply Subtype.ext
          simpa using hkf.symm
        simpa [hgk] using hkK
    rw [hset]
    exact hcomp

end Work.SeedDyn
