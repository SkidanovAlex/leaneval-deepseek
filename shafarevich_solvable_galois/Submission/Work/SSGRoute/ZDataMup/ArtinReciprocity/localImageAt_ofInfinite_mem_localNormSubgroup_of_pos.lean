import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

/-- **The archimedean local norm condition at an infinite place, from positivity.**

Let `L / K` be a finite Galois extension of number fields, `v` an infinite place of `K` and `x : Kˣ`
an element which is *positive* at every real place of `K` (measured with the canonical identification
`K_w ≅ ℝ`).  Then the image of `x` in `K_vˣ` lies in the archimedean local norm subgroup
`N_{L/K}(𝕀_L)_v`.

At an infinite place the norm subgroup is the `iSup` of the local norm images `N_{L_{w'}/K_v}` over
the places `w' | v`, and the archimedean local norm has one of three shapes:

* `K_v = ℂ`: `N_{ℂ/ℂ}` (or `BbbC / ℝ` with a real place above) is onto, so the subgroup is `⊤`;
* `K_v = ℝ` with a real place `w'` of `L` above it: `N_{ℝ/ℝ}` is the identity, so the subgroup is
  `⊤` again;
* `K_v = ℝ` with every `w' | v` complex: `N_{ℂ/ℝ}(z) = z z̄ = |z|²`, so the subgroup is the group of
  *positive* reals — here the hypothesis `hpos` is exactly what is needed.

This is the local input (`localImageAt` is the component `(principalIdele K x) v`) used to discharge
the archimedean conditions of the `p = 2` clause of the product-form reciprocity. -/
theorem localImageAt_ofInfinite_mem_localNormSubgroup_of_pos {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (x : Kˣ) (v : NumberField.InfinitePlace K) (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal), 0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion ((x : K)))) : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite v) x ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (NK.GlobalCFT.Place.ofInfinite v) := by
  -- Pick a place `w₀` of `L` above `v`; `L_{w₀}` is one of the local fields `K_v = ℂ` or `ℝ`.
  obtain ⟨w₀, hw₀⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) v
  haveI : w₀.LiesOver v := hw₀
  by_cases hvc : v.IsComplex
  · -- `K_v = ℂ`: the local norm `N_{L_{w₀}/ℂ}` is onto, so the norm subgroup is everything.
    rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (K := K) (L := L) (w₀ := w₀)
      (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex hvc
        (NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w₀ hvc))]
    exact Subgroup.mem_top _
  · have hvR : v.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hvc
    by_cases hre : ∃ w' : NumberField.InfinitePlace L, w'.LiesOver v ∧ w'.IsReal
    · -- `K_v = ℝ` with a real place of `L` above it: the local norm `N_{ℝ/ℝ}` is the identity.
      obtain ⟨w₁, hw₁, hw₁R⟩ := hre
      haveI : w₁.LiesOver v := hw₁
      rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (K := K) (L := L) (w₀ := w₁)
        (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real hvR hw₁R)]
      exact Subgroup.mem_top _
    · -- `K_v = ℝ` with every place of `L` above it complex: the norm subgroup is the positive
      -- reals, and `hpos` says that the image of `x` is positive.
      have hwc : w₀.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
        (fun hR => hre ⟨w₀, hw₀, hR⟩)
      rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap (K := K) (L := L) hw₀ hvR hwc,
        Subgroup.mem_comap, Units.mem_posSubgroup]
      show 0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
        (algebraMap K v.Completion (x : K))
      exact hpos v hvR

end Work.SSGRoute.ZDataMup.ArtinReciprocity
