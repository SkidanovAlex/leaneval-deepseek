import Mathlib
import Submission.Work.Milnor.cohomology_capped

/-!
# The cohomology of the capped space, for a capping datum of the disc bundle

The closed `8`-manifold `X = cappedSpace D` attached to a gluing datum `D` on the pair
`(Vk (-2), ℝ⁸)` is the union of the open piece `A = D.ιX '' Vk (-2)` (homotopy equivalent to
`S⁴`) and the open piece `B = D.ιY '' ℝ⁸` (contractible, because `D.ιY` is an open embedding of
the contractible space `ℝ⁸`), with intersection `A ∩ B ≃ D.U`.  When `D.U = collar (-2)` the
intersection is homotopy equivalent to `S⁷`, and the Mayer–Vietoris long exact sequence gives

`Hⁿ(X) ≅ ℤ` for `n ∈ {0, 4, 8}` and `Hⁿ(X) = 0` otherwise.

Nothing here uses the particular shape of `D.V`: only that `D.ιY` is an open embedding of the
contractible space `ℝ⁸`.  This is the statement of `Work.Milnor.cohomology_capped` with its (unused)
hypothesis `D.V = {z | 1/2 < ‖z‖}` removed.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

theorem cohomology_capped_compact (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of (Work.Milnor.cappedSpace D)) ≅ ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) + (if n = 8 then 1 else 0)) → ℤ)) := by
  obtain ⟨eSmall⟩ := Cohomology.cohSmallIso (Work.Milnor.glueU D) (Work.Milnor.glueV D)
    (Work.Milnor.isOpen_glueU D) (Work.Milnor.isOpen_glueV D) (Work.Milnor.glueU_union_glueV D) n
  by_cases h0 : n = 0
  · subst h0
    have hk : (if (0:ℕ) = 0 then 1 else 0) + (if (0:ℕ) = 4 then 1 else 0) +
        (if (0:ℕ) = 8 then 1 else 0) = 1 := by norm_num
    rw [hk]
    haveI : PathConnectedSpace (Work.Milnor.cappedSpace D) := Work.Milnor.capped_pathConnected D hU
    obtain ⟨e0⟩ := Cohomology.singularCohomology_zero ℤ (TopCat.of (Work.Milnor.cappedSpace D))
    exact ⟨e0 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · by_cases h4 : n = 4
    · subst h4
      have hk : (if (4:ℕ) = 0 then 1 else 0) + (if (4:ℕ) = 4 then 1 else 0) +
          (if (4:ℕ) = 8 then 1 else 0) = 1 := by norm_num
      rw [hk]
      have hCU3 : IsZero ((Cohomology.cochainUV (Work.Milnor.glueU D) (Work.Milnor.glueV D)).homology 3) :=
        Work.Milnor.isZero_cochainUV D hU 3 (by norm_num) (by norm_num)
      have hCU4 : IsZero ((Cohomology.cochainUV (Work.Milnor.glueU D) (Work.Milnor.glueV D)).homology 4) :=
        Work.Milnor.isZero_cochainUV D hU 4 (by norm_num) (by norm_num)
      haveI hmono : Mono (HomologicalComplex.homologyMap
          (Cohomology.mvCochainF (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4) :=
        Work.Milnor.mvCohF_mono (Work.Milnor.glueU D) (Work.Milnor.glueV D) 3 hCU3
      haveI hepi : Epi (HomologicalComplex.homologyMap
          (Cohomology.mvCochainF (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4) :=
        Work.Milnor.mvCohF_epi (Work.Milnor.glueU D) (Work.Milnor.glueV D) 4 hCU4
      haveI hF4 : IsIso (HomologicalComplex.homologyMap
          (Cohomology.mvCochainF (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4) := isIso_of_mono_of_epi _
      have hZ4 : IsZero ((Cohomology.cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)).homology 4) :=
        Work.Milnor.isZero_cochainV D 4 (by norm_num)
      haveI hinl : IsIso (HomologicalComplex.homologyMap
          (biprod.inl : Cohomology.cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D) ⟶
            Cohomology.cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D) ⊞
              Cohomology.cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4) :=
        Work.Milnor.isIso_homologyMap_biprod_inl _ _ 4 hZ4
      obtain ⟨eU4⟩ := Work.Milnor.glueU_cohomology_four D
      exact ⟨eSmall ≪≫
        asIso (HomologicalComplex.homologyMap
          (Cohomology.mvCochainF (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4) ≪≫
        (asIso (HomologicalComplex.homologyMap
          (biprod.inl : Cohomology.cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D) ⟶
            Cohomology.cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D) ⊞
              Cohomology.cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4)).symm ≪≫
        eU4 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
    · by_cases h8 : n = 8
      · subst h8
        have hk : (if (8:ℕ) = 0 then 1 else 0) + (if (8:ℕ) = 4 then 1 else 0) +
            (if (8:ℕ) = 8 then 1 else 0) = 1 := by norm_num
        rw [hk]
        have hZ8 : IsZero ((Cohomology.cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D) ⊞
            Cohomology.cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)).homology 8) :=
          Cohomology.isZero_coh_homology_biprod _ _ 8
            (Work.Milnor.isZero_cochainU D 8 (by norm_num) (by norm_num))
            (Work.Milnor.isZero_cochainV D 8 (by norm_num))
        have hZ7 : IsZero ((Cohomology.cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D) ⊞
            Cohomology.cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)).homology 7) :=
          Cohomology.isZero_coh_homology_biprod _ _ 7
            (Work.Milnor.isZero_cochainU D 7 (by norm_num) (by norm_num))
            (Work.Milnor.isZero_cochainV D 7 (by norm_num))
        haveI hepi : Epi (Cohomology.mvCohδ (Work.Milnor.glueU D) (Work.Milnor.glueV D) 7) :=
          Work.Milnor.mvCohδ_epi (Work.Milnor.glueU D) (Work.Milnor.glueV D) 7 (by simpa using hZ8)
        haveI hmono : Mono (Cohomology.mvCohδ (Work.Milnor.glueU D) (Work.Milnor.glueV D) 7) :=
          Work.Milnor.mvCohδ_mono (Work.Milnor.glueU D) (Work.Milnor.glueV D) 7 hZ7
        haveI hiso : IsIso (Cohomology.mvCohδ (Work.Milnor.glueU D) (Work.Milnor.glueV D) 7) :=
          isIso_of_mono_of_epi _
        obtain ⟨eUV7⟩ := Work.Milnor.glueUV_cohomology_seven D hU
        exact ⟨eSmall ≪≫
          (asIso (Cohomology.mvCohδ (Work.Milnor.glueU D) (Work.Milnor.glueV D) 7)).symm ≪≫
          eUV7 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
      · have hk : (if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) +
            (if n = 8 then 1 else 0) = 0 := by
          rw [if_neg h0, if_neg h4, if_neg h8]
        rw [hk]
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
        by_cases hn1' : n = 1
        · subst hn1'
          haveI : PathConnectedSpace ↥(Work.Milnor.glueU D ∩ Work.Milnor.glueV D) :=
            Work.Milnor.capped_pathConnected_inter D hU
          have hz := Work.Milnor.mvCoh_one_isZero (Work.Milnor.glueU D) (Work.Milnor.glueV D)
            (Work.Milnor.isZero_cochainU D 1 (by norm_num) (by norm_num))
            (Work.Milnor.isZero_cochainV D 1 (by norm_num))
          exact ⟨eSmall ≪≫ IsZero.iso hz
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩
        · have hz := Work.Milnor.mvCoh_isZero (Work.Milnor.glueU D) (Work.Milnor.glueV D) n hn1
            (Work.Milnor.isZero_cochainU D n h0 h4)
            (Work.Milnor.isZero_cochainV D n h0)
            (Work.Milnor.isZero_cochainUV D hU (n-1) (by omega) (by omega))
          exact ⟨eSmall ≪≫ IsZero.iso hz
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩

end

end Work.Cohomology
