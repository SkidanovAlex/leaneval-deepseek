import Mathlib
import Submission.Work.Projective.PieceCohomology
import Submission.Work.Projective.cp2V_cohomology
import Submission.Work.Projective.cp2UV_cohomology
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.homology_biprod_iso

/-!
# The cohomology of `ℂP²` computed by Mayer–Vietoris

The affine charts of `ℂP²` are contractible (`Work.Projective.contractibleSpace_chartSet`), and the
cover `ℂP² = U ∪ V` with `U = cp2U = chartSet 0` (contractible) and `V = cp2V = chartSet 1 ∪
chartSet 2` (homotopy equivalent to `ℂP¹ ≅ S²`, `Work.Projective.cp2V_cohomology`) has
`U ∩ V` homotopy equivalent to `S³` (`Work.Projective.cp2UV_cohomology`).  The Mayer–Vietoris
long exact sequence of the workspace's cochain model
(`Work.Cohomology.mvCochainSES`, `mvCohδ`, `cohSmallIso`) therefore computes

  `H⁰(ℂP²;ℤ) = ℤ`,  `H²(ℂP²;ℤ) = ℤ`,  `H⁴(ℂP²;ℤ) = ℤ`,  `H¹ = H³ = 0`

(the degrees needed for the generator side of the dimension-`4` Hirzebruch theorem):
`H²(ℂP²) ≅ H²(V)` because `H²(U) = H²(U ∩ V) = 0`, and `H⁴(ℂP²) ≅ H³(U ∩ V)` because
`H³(U) = H³(V) = H⁴(U) = H⁴(V) = 0`, so the connecting map `mvCohδ` is an isomorphism.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

noncomputable section

/-! ## Reading off vanishings from the pieces -/

/-- An isomorphism to a free module on `Fin k → ℤ` with `k = 0` exhibits the source as a zero
object. -/
theorem isZero_of_iso_fin_zero {M : ModuleCat ℤ} {k : ℕ} (hk : k = 0)
    (e : M ≅ ModuleCat.of ℤ (Fin k → ℤ)) : IsZero M := by
  subst hk
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) e

/-- **The vanishing of the cohomology of `V = ℂP² ∖ {[1:0:0]}` away from degrees `0` and `2`.** -/
theorem isZero_cochainV_cp2 {n : ℕ} (h0 : n ≠ 0) (h2 : n ≠ 2) :
    IsZero ((cochainV cp2U cp2V).homology n) := by
  obtain ⟨e⟩ := cp2V_cohomology n
  have hk : (if n = 0 then 1 else 0) + (if n = 2 then 1 else 0) = 0 := by
    rw [if_neg h0, if_neg h2]
  exact isZero_of_iso_fin_zero hk e

/-- **The vanishing of the cohomology of `U ∩ V` away from degrees `0` and `3`.** -/
theorem isZero_cochainUV_cp2 {n : ℕ} (h0 : n ≠ 0) (h3 : n ≠ 3) :
    IsZero ((cochainUV cp2U cp2V).homology n) := by
  obtain ⟨e⟩ := cp2UV_cohomology n
  have hk : (if n = 0 then 1 else 0) + (if n = 3 then 1 else 0) = 0 := by
    rw [if_neg h0, if_neg h3]
  exact isZero_of_iso_fin_zero hk e

/-! ## The Mayer–Vietoris assembly in degree `2` -/

/-- Exactness of the Mayer–Vietoris sequence at `H²(U) ⊞ H²(V)`. -/
theorem range_mvCochainF_two_eq_ker_mvCochainG_two :
    LinearMap.range (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mvCochainG cp2U cp2V) 2).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker ((mvCochainSES cp2U cp2V).homology_exact₂ 2)

/-- Exactness of the Mayer–Vietoris sequence at `H²(C^{U,V})`. -/
theorem range_mvCohδ_one_eq_ker_mvCochainF_two :
    LinearMap.range (mvCohδ cp2U cp2V 1).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker (mvCoh_H_exact₁ cp2U cp2V 1)

/-- The middle map of the Mayer–Vietoris sequence in degree `2`,
`H²(C^{U,V}) ⟶ H²(U) ⊕ H²(V)`, is an isomorphism: it is injective because `H¹(U ∩ V) = 0` and
surjective because `H²(U ∩ V) = 0`. -/
theorem isIso_mvCochainF_two :
    IsIso (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2) := by
  have hUV1 : IsZero ((cochainUV cp2U cp2V).homology 1) :=
    isZero_cochainUV_cp2 (by norm_num) (by norm_num)
  have hUV2 : IsZero ((cochainUV cp2U cp2V).homology 2) :=
    isZero_cochainUV_cp2 (by norm_num) (by norm_num)
  have hδ : mvCohδ cp2U cp2V 1 = 0 := IsZero.eq_zero_of_src hUV1 _
  have hG : HomologicalComplex.homologyMap (mvCochainG cp2U cp2V) 2 = 0 :=
    IsZero.eq_zero_of_tgt hUV2 _
  have hker : LinearMap.ker (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2).hom
      = ⊥ := by
    rw [← range_mvCohδ_one_eq_ker_mvCochainF_two, hδ]
    exact LinearMap.range_zero
  have hrange : LinearMap.range (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2).hom
      = ⊤ := by
    rw [range_mvCochainF_two_eq_ker_mvCochainG_two, hG]
    exact LinearMap.ker_zero
  haveI : Mono (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2) :=
    (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hker)
  haveI : Epi (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2) :=
    (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range_eq_top.mp hrange)
  exact isIso_of_mono_of_epi _

/-- **`H²(ℂP²;ℤ) ≅ ℤ`.** -/
theorem singularCohomology_two_cp2 :
    Nonempty (Work.Cohomology.singularCohomology ℤ 2 (CPSpace 2) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨eSmall⟩ := cohSmallIso cp2U cp2V isOpen_cp2U isOpen_cp2V cp2U_union_cp2V 2
  obtain ⟨eBip⟩ := homology_biprod_iso (cochainU cp2U cp2V) (cochainV cp2U cp2V) 2
  have hU2 : IsZero ((cochainU cp2U cp2V).homology 2) := isZero_cochainU_cp2 1
  obtain ⟨eV⟩ := cp2V_cohomology 2
  have hk : (if (2 : ℕ) = 0 then 1 else 0) + (if (2 : ℕ) = 2 then 1 else 0) = 1 := by norm_num
  haveI := isIso_mvCochainF_two
  refine ⟨eSmall ≪≫ asIso (HomologicalComplex.homologyMap (mvCochainF cp2U cp2V) 2) ≪≫ eBip ≪≫
    (CategoryTheory.Limits.isoZeroBiprod hU2).symm ≪≫ eV ≪≫ ?_⟩
  rw [hk]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-! ## The Mayer–Vietoris assembly in degree `4` -/

/-- The connecting map `mvCohδ` in degree `3`, `H³(U ∩ V) ⟶ H⁴(C^{U,V})`, is an isomorphism: the
intermediate terms `H³(U) ⊕ H³(V)` and `H⁴(U) ⊕ H⁴(V)` vanish. -/
theorem isIso_mvCohδ_three : IsIso (mvCohδ cp2U cp2V 3) := by
  have hU3 : IsZero ((cochainU cp2U cp2V).homology 3) := isZero_cochainU_cp2 2
  have hV3 : IsZero ((cochainV cp2U cp2V).homology 3) :=
    isZero_cochainV_cp2 (by norm_num) (by norm_num)
  have hU4 : IsZero ((cochainU cp2U cp2V).homology 4) := isZero_cochainU_cp2 3
  have hV4 : IsZero ((cochainV cp2U cp2V).homology 4) :=
    isZero_cochainV_cp2 (by norm_num) (by norm_num)
  have hL3 : IsZero ((cochainU cp2U cp2V ⊞ cochainV cp2U cp2V).homology 3) :=
    isZero_coh_homology_biprod _ _ 3 hU3 hV3
  have hL4 : IsZero ((cochainU cp2U cp2V ⊞ cochainV cp2U cp2V).homology 4) :=
    isZero_coh_homology_biprod _ _ 4 hU4 hV4
  exact mvCohδ_isIso cp2U cp2V 3 hL3 hL4

/-- **`H⁴(ℂP²;ℤ) ≅ ℤ`.** -/
theorem singularCohomology_four_cp2 :
    Nonempty (Work.Cohomology.singularCohomology ℤ 4 (CPSpace 2) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨eSmall⟩ := cohSmallIso cp2U cp2V isOpen_cp2U isOpen_cp2V cp2U_union_cp2V 4
  haveI := isIso_mvCohδ_three
  obtain ⟨eUV⟩ := cp2UV_cohomology 3
  have hk : (if (3 : ℕ) = 0 then 1 else 0) + (if (3 : ℕ) = 3 then 1 else 0) = 1 := by norm_num
  refine ⟨eSmall ≪≫ (asIso (mvCohδ cp2U cp2V 3)).symm ≪≫ eUV ≪≫ ?_⟩
  rw [hk]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

end

end Work.Projective
