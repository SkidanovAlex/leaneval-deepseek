import Mathlib
import Submission.Work.Projective.CP2Cohomology
import Submission.Work.Projective.HomologyPieces
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.isZero_homology_biprod

/-!
# The homology of `ℂP²` computed by Mayer–Vietoris (degree `4`)

The homology counterpart of `Submission/Work/Projective/CP2Cohomology.lean`: the Mayer–Vietoris
long exact sequence in homology (`Work.Cohomology.mvShort`, `mvδ`, `mv_H_exact₁/₃`,
`smallIso`) for the cover `ℂP² = U ∪ V` with `U = chartSet 0` (contractible) and
`V = chartSet 1 ∪ chartSet 2` (`≃ S²`), whose intersection is `≃ S³`, gives

  `H₄(ℂP²;ℤ) ≅ H₃(U ∩ V;ℤ) ≅ ℤ`

because `H₃(U) = H₃(V) = H₄(U) = H₄(V) = 0`, so the connecting map `mvδ` in degree `3` is an
isomorphism.  This produces the **fundamental class** of `ℂP²` in the workspace's cochain model
(`Submission/Work/SignatureBordism`), the input needed to state the signature of `ℂP²`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

noncomputable section

/-- Exactness of the homology Mayer–Vietoris sequence at `H₃(U ∩ V)`. -/
theorem range_mvδ_three_eq_ker_mvLeft :
    LinearMap.range (mvδ cp2U cp2V 3).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mvLeft cp2U cp2V) 3).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker (mv_H_exact₁ cp2U cp2V 3)

/-- Exactness of the homology Mayer–Vietoris sequence at `H₄(C^{U,V})`. -/
theorem range_mvRight_four_eq_ker_mvδ_three :
    LinearMap.range (HomologicalComplex.homologyMap (mvRight cp2U cp2V) 4).hom =
      LinearMap.ker (mvδ cp2U cp2V 3).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker (mv_H_exact₃ cp2U cp2V 3)

/-- The connecting map `mvδ` of the homology Mayer–Vietoris sequence for the cover of `ℂP²` by
`U = chartSet 0` and `V = chartSet 1 ∪ chartSet 2`, in degree `3`, is an isomorphism: the
intermediate terms `H₃(U) ⊞ H₃(V)` and `H₄(U) ⊞ H₄(V)` vanish. -/
theorem isIso_mvδ_three : IsIso (mvδ cp2U cp2V 3) := by
  have hU3 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2U)).homology 3) := by
    haveI : ContractibleSpace ↥cp2U := contractibleSpace_chartSet 2 0
    exact homologyContractible 3 (by norm_num)
  have hU4 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2U)).homology 4) := by
    haveI : ContractibleSpace ↥cp2U := contractibleSpace_chartSet 2 0
    exact homologyContractible 4 (by norm_num)
  have hV3 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2V)).homology 3) :=
    isZero_cochainV_homology_cp2 (by norm_num) (by norm_num)
  have hV4 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2V)).homology 4) :=
    isZero_cochainV_homology_cp2 (by norm_num) (by norm_num)
  have hL3 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2U) ⊞
      Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2V)).homology 3) :=
    isZero_homology_biprod 3 hU3 hV3
  have hL4 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2U) ⊞
      Work.Cohomology.singularChains ℤ (TopCat.of ↥cp2V)).homology 4) :=
    isZero_homology_biprod 4 hU4 hV4
  have hmvLeft : HomologicalComplex.homologyMap (mvLeft cp2U cp2V) 3 = 0 :=
    IsZero.eq_zero_of_tgt hL3 _
  have hmvRight : HomologicalComplex.homologyMap (mvRight cp2U cp2V) 4 = 0 :=
    IsZero.eq_zero_of_src hL4 _
  have hker : LinearMap.ker (mvδ cp2U cp2V 3).hom = ⊥ := by
    rw [← range_mvRight_four_eq_ker_mvδ_three, hmvRight]
    exact LinearMap.range_zero
  have hrange : LinearMap.range (mvδ cp2U cp2V 3).hom = ⊤ := by
    rw [range_mvδ_three_eq_ker_mvLeft, hmvLeft]
    exact LinearMap.ker_zero
  haveI : Mono (mvδ cp2U cp2V 3) :=
    (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hker)
  haveI : Epi (mvδ cp2U cp2V 3) :=
    (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range_eq_top.mp hrange)
  exact isIso_of_mono_of_epi _

/-- **`H₄(ℂP²;ℤ) ≅ ℤ`**: the homology of `ℂP²` in the middle degree, i.e. the fundamental class. -/
theorem singularHomology_four_cp2 :
    Nonempty ((Work.Cohomology.singularChains ℤ (CPSpace 2)).homology 4 ≅ ModuleCat.of ℤ ℤ) := by
  haveI := isIso_mvδ_three
  obtain ⟨eUV⟩ := cp2UV_homology 3 (by norm_num)
  have hk : (if (3 : ℕ) = 3 then 1 else 0) = 1 := by norm_num
  refine ⟨(smallIso cp2U cp2V isOpen_cp2U isOpen_cp2V cp2U_union_cp2V 4).symm ≪≫
    asIso (mvδ cp2U cp2V 3) ≪≫ eUV ≪≫ ?_⟩
  rw [hk]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

end

end Work.Projective
