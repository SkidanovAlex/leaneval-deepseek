import Mathlib
import Submission.Work.SphereJordan.plane_crux
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.JordanSeparation.simplyConnectedSpace_onePoint_complex

/-!
# The sphere statement from the plane crux

Given the plane crux (`IsSimplyConnected U` for an open preconnected `U ⊆ ℂ` whose complement in
the Riemann sphere is preconnected), every open preconnected `D ⊆ S²` whose complement is
preconnected is simply connected.

The reduction moves a point `x₀` of `Dᶜ` to `∞` by a Möbius homeomorphism `ψ`; then `ψ '' D` misses
`∞`, hence is a subset of `ℂ`, and its complement in `ℂ`, together with `∞`, is the preconnected
set `ψ '' Dᶜ`.
-/

namespace Work.SphereJordan

open Set

noncomputable section

/-- Every point of the Riemann sphere is carried to `∞` by a self-homeomorphism. -/
theorem exists_homeomorph_maps_to_infty (x₀ : OnePoint ℂ) :
    ∃ ψ : OnePoint ℂ ≃ₜ OnePoint ℂ, ψ x₀ = OnePoint.infty := by
  by_cases h : x₀ = OnePoint.infty
  · exact ⟨Homeomorph.refl _, h⟩
  · obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp h
    obtain ⟨Φ, hΦ, -, -⟩ := Work.Smooth.SphereJordan.mobiusAddInv a
    refine ⟨Φ.symm, ?_⟩
    rw [← ha, ← hΦ, Homeomorph.symm_apply_apply]

/-- **The sphere statement from the plane crux.** -/
theorem domain_compl_simplyConnected_of_plane_crux
    (hplane : ∀ {U : Set ℂ}, IsOpen U → U.Nonempty → IsPreconnected U →
      IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}) → IsSimplyConnected U)
    {D : Set (OnePoint ℂ)} (hDopen : IsOpen D) (hDne : D.Nonempty) (hDpre : IsPreconnected D)
    (hDcompl : IsPreconnected Dᶜ) : IsSimplyConnected D := by
  rcases eq_empty_or_nonempty (Dᶜ) with hempty | hne
  · have hDuniv : D = univ := by
      rw [← compl_compl D, hempty, compl_empty]
    rw [hDuniv]
    haveI : SimplyConnectedSpace (OnePoint ℂ) :=
      Work.Smooth.JordanSeparation.simplyConnectedSpace_onePoint_complex
    exact (Homeomorph.toHomotopyEquiv (Homeomorph.Set.univ (OnePoint ℂ))).simplyConnectedSpace
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨ψ, hψ⟩ := exists_homeomorph_maps_to_infty x₀
    set D' : Set (OnePoint ℂ) := ψ '' D with hD'def
    have hD'open : IsOpen D' := ψ.isOpenMap D hDopen
    have hD'pre : IsPreconnected D' := hDpre.image ψ ψ.continuous.continuousOn
    have hD'ne : D'.Nonempty := hDne.image ψ
    have hinfty : (OnePoint.infty : OnePoint ℂ) ∉ D' := by
      rintro ⟨y, hy, hyeq⟩
      have hyx : y = x₀ := ψ.injective (by rw [hyeq, hψ])
      exact hx₀ (hyx ▸ hy)
    have hcomplD' : D'ᶜ = ψ '' Dᶜ := by
      ext y
      constructor
      · intro hy
        refine ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩
        intro hmem
        exact hy (by rw [hD'def]; exact ⟨ψ.symm y, hmem, ψ.apply_symm_apply y⟩)
      · rintro ⟨x, hx, rfl⟩ hy
        rw [hD'def] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        exact hx (ψ.injective hzy ▸ hz)
    -- the ℂ-part `U` of `D'`
    set U : Set ℂ := {z : ℂ | (z : OnePoint ℂ) ∈ D'} with hUdef
    have hUim : ((↑) : ℂ → OnePoint ℂ) '' U = D' := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy
        obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinfty (h ▸ hy))
        exact ⟨z, hy, rfl⟩
    have hUopen : IsOpen U := hD'open.preimage OnePoint.continuous_coe
    have hUne : U.Nonempty := by
      obtain ⟨y, hy⟩ := hD'ne
      obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinfty (h ▸ hy))
      exact ⟨z, hy⟩
    have hUpre : IsPreconnected U :=
      hD'pre.preimage_of_isOpenMap OnePoint.coe_injective OnePoint.isOpenMap_coe
        (fun y hy => OnePoint.ne_infty_iff_exists.mp (fun h => hinfty (h ▸ hy)))
    -- the complement statement
    have hcoeCompl : ((↑) : ℂ → OnePoint ℂ) '' Uᶜ = D'ᶜ \ {OnePoint.infty} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨?_, OnePoint.coe_ne_infty z⟩
        intro hy
        exact hz (by rw [hUdef, Set.mem_ofPred_eq]; exact hy)
      · rintro ⟨hy, hyinf⟩
        obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hyinf
        subst hz
        refine ⟨z, ?_, rfl⟩
        simpa [hUdef] using hy
    have hcomplpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}) := by
      have hEq : (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}) = D'ᶜ := by
        rw [hcoeCompl]
        ext y
        constructor
        · rintro (h | h)
          · exact h.1
          · rw [Set.mem_singleton_iff] at h
            rw [h]
            exact hinfty
        · intro hy
          by_cases hyinf : y = OnePoint.infty
          · exact Or.inr hyinf
          · exact Or.inl ⟨hy, hyinf⟩
      rw [hEq, hcomplD']
      exact hDcompl.image ψ ψ.continuous.continuousOn
    have hSU : IsSimplyConnected U := hplane hUopen hUne hUpre hcomplpre
    have hSU' : IsSimplyConnected (((↑) : ℂ → OnePoint ℂ) '' U) :=
      (Topology.IsEmbedding.isSimplyConnected_image
        (OnePoint.isOpenEmbedding_coe (X := ℂ)).toIsEmbedding (s := U)).mpr hSU
    rw [hUim] at hSU'
    exact (Homeomorph.isSimplyConnected_image ψ).mp hSU'

end

end Work.SphereJordan
