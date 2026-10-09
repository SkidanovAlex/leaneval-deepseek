import Submission.Work.SSGRoute.eb_arch_imports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `hγ` step of the archimedean case of `brauer_single_place` (E8', piece P4)

The localisation of the cyclic class `γ = cycClassOf_{M/k}(b)` vanishes at every place of `M`
outside the orbit of the infinite place `w₀`: the inflation–locality dictionary
`NK.HR2.locUnits_inflation_eq_zero_iff` reduces it to the vanishing of the localisation of
`inf_E a = inf_E γ` at a place of `E` above it, which is the archimedean/finite place argument
`NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero` applied at the place of `L` below.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.SSGRoute

/-- **Local triviality of the cyclic class at the places of `M` outside the orbit of `w₀`.** -/
theorem eb_arch_gamma_local {k L M E : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra k L] [Algebra k M] [Algebra k E]
    [Algebra L E] [Algebra M E] [IsScalarTower k L E] [IsScalarTower k M E]
    [FiniteDimensional k L] [FiniteDimensional k M] [FiniteDimensional k E]
    [IsGalois k L] [IsGalois k M] [IsGalois k E] [FiniteDimensional M E] [IsGalois M E]
    (w₀ : NumberField.InfinitePlace L) (a : groupCohomology (NK.HassePrinciple.unitsRep k L) 2)
    (h : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofInfinite w₀ ≠ w) →
        (NK.HassePrinciple.locUnits k L w).hom a = 0)
    (gM : M ≃ₐ[k] M) (hgM : ∀ σ : M ≃ₐ[k] M, σ ∈ Subgroup.zpowers gM) (b : kˣ)
    (hb : (NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a
        = (NK.NUV2.ARL.HR.inflation (K := k) (L := M) (E := E)).hom
            (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := k) (F := M) gM hgM b))
    (W : NK.GlobalCFT.Place M)
    (hW : ¬ NK.GlobalCFT.Place.LiesOver W
        (NK.GlobalCFT.Place.ofInfinite (w₀.comap (algebraMap k L)))) :
    (NK.HassePrinciple.locUnits k M W).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := k) (F := M) gM hgM b) = 0 := by
  haveI hfdLE : FiniteDimensional L E := Module.Finite.of_restrictScalars_finite k L E
  haveI hgalLE : IsGalois L E := IsGalois.tower_top_of_isGalois k L E
  -- a place of `E` above `W`
  obtain ⟨Ŵ, hŴ⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := M) (L := E) W
  -- the corresponding place of `L`
  obtain ⟨s, hs⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := L) (L := E) Ŵ
  -- `s` is outside the orbit of `w₀`
  have hnot : ∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofInfinite w₀ ≠ s := by
    rw [Work.SSGRoute.not_liesOver_iff_not_mem_orbit k L
      (NK.GlobalCFT.Place.ofInfinite w₀)
      (NK.GlobalCFT.Place.ofInfinite (w₀.comap (algebraMap k L)))
      (NK.GlobalCFT.Place.liesOver_ofInfinite
        (NK.GlobalCFT.Norm.liesOver_comap_self w₀))]
    intro hlies
    -- the place of `k` below `W` agrees with the place of `k` below `s`
    obtain ⟨t, ht⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := M) W
    have h1 : NK.GlobalCFT.Place.LiesOver Ŵ
        (NK.GlobalCFT.Place.ofInfinite (w₀.comap (algebraMap k L))) :=
      Work.SSGRoute.place_liesOver_trans hs hlies
    have h2 : NK.GlobalCFT.Place.LiesOver Ŵ t :=
      Work.SSGRoute.place_liesOver_trans hŴ ht
    have h3 : t = NK.GlobalCFT.Place.ofInfinite (w₀.comap (algebraMap k L)) :=
      NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (K := k) (L := E) h2 h1
    exact hW (h3 ▸ ht)
  have hsa : (NK.HassePrinciple.locUnits k L s).hom a = 0 := h s hnot
  -- the localisation of the inflation at `Ŵ` vanishes
  have hE : (NK.HassePrinciple.locUnits k E Ŵ).hom
      ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a) = 0 :=
    NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero (K := k) (L := L) (E := E) a s Ŵ hs hsa
  -- transfer back through the inflation–locality dictionary
  rw [← (NK.HR2.locUnits_inflation_eq_zero_iff (K := k) (M := M) (E := E)
    (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := k) (F := M) gM hgM b) W Ŵ hŴ)]
  rw [← hb]
  exact hE

end Work.SSGRoute
