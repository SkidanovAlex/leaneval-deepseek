import Mathlib
import Submission.Work.Milnor.cohomology_capped
import Submission.Work.Milnor.homology_Vk
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.homologyMV
import Submission.Work.Cohomology.mvLeft_zero_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The homology of the capped space `X = D(ξ) ∪_F D⁸`

The closed `8`-manifold `X = cappedSpace D` of `Submission/Work/Milnor/Model8.lean` is the union
of the open disc bundle `A = ιX '' (Vk (-2))` (homotopy equivalent to `S⁴`) and the image `B` of
`ℝ⁸` (contractible), with intersection `A ∩ B ≃ D.U`; when `D.U = collar (-2)` the intersection is
homotopy equivalent to `S⁷`.

Its singular homology with `ℤ` coefficients is therefore `ℤ` in degrees `0`, `4` and `8` and zero
in every other degree.  This is the homological counterpart of
`Work.Milnor.cohomology_capped_compact`, and the proof has the same shape: the Mayer–Vietoris
long exact sequence for the open cover `{A, B}` (`Work.Cohomology.mv_H_exact₁/₂/₃`) has

* `Hₙ(A) = ℤ` for `n ∈ {0, 4}` (`Work.Milnor.homology_Vk` transported along `A ≅ Vk (-2)`),
* `Hₙ(B) = ℤ` for `n = 0` (contractibility, `Work.Cohomology.homologyContractible`),
* `Hₙ(A ∩ B) = ℤ` for `n ∈ {0, 7}` (`Work.Cohomology.sphereHomologyTop` /
  `Work.Cohomology.sphereHomologyZero` transported along `A ∩ B ≃ S⁷`),

so that
* `H₄(X) ≅ H₄(A)` (the `B`-summand and the `A ∩ B`-terms adjacent to degree `4` vanish),
* `H₈(X) ≅ H₇(A ∩ B)` (the connecting map `δ₇` is an isomorphism),
* `H₁(X) = 0` (the difference map `H₀(A) ⊕ H₀(B) → H₀(A ∩ B)` is onto, so `δ₀ = 0`),
* `Hₙ(X) = 0` for all other `n ∉ {0, 4, 8}` (both neighbours in the sequence vanish).
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Milnor

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-- The inclusion of the first factor of a biproduct of chain complexes induces an isomorphism in
homology when the second factor is acyclic in that degree. -/
lemma isIso_homologyMap_biprod_inl_chain (K L : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : IsZero (L.homology k)) :
    IsIso (HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) k) := by
  refine IsIso.mk ⟨HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) k, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst, HomologicalComplex.homologyMap_id]
  · have htot := Work.Cohomology.homologyMap_total K L k
    rw [IsZero.eq_zero_of_tgt h
      (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) k)] at htot
    simpa using htot

/-! ## The homology of the two pieces and of their intersection -/

/-- The `Vk (-2)`-piece `A = ιX '' (Vk (-2))` has the homology of `Vk (-2)`, i.e. `ℤ` in degrees
`0` and `4` and zero otherwise. -/
lemma homology_glueU (D : CapData) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D))).homology n ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0)) → ℤ)) := by
  obtain ⟨e⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
    ((D.isOpenEmbedding_ιX.isEmbedding).toHomeomorph.toHomotopyEquiv) n
  obtain ⟨e2⟩ := homology_Vk (-2) n
  exact ⟨e.symm ≪≫ e2⟩

/-- `Hₙ` of the `Vk (-2)`-piece vanishes for `n ∉ {0, 4}`. -/
lemma isZero_homology_glueU (D : CapData) (n : ℕ) (hn0 : n ≠ 0) (hn4 : n ≠ 4) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D))).homology n) := by
  obtain ⟨e⟩ := homology_glueU D n
  have hfin : ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0)) = 0 := by
    rw [if_neg hn0, if_neg hn4]
  rw [hfin] at e
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) e

/-- The `ℝ⁸`-piece `B = ιY '' ℝ⁸` is contractible, so `Hₙ(B) = 0` for `n ≥ 1`. -/
lemma isZero_homology_glueV (D : CapData) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueV D))).homology n) := by
  haveI : ContractibleSpace ↥(glueV D) :=
    ((D.isOpenEmbedding_ιY.isEmbedding).toHomeomorph).symm.contractibleSpace
  exact Work.Cohomology.homologyContractible n (Nat.pos_of_ne_zero hn)

/-- The intersection `A ∩ B ≃ S⁷` has vanishing homology in degrees `n ∉ {0, 7}`. -/
lemma isZero_homology_inter (D : CapData) (hU : D.U = collar (-2)) (n : ℕ)
    (hn0 : n ≠ 0) (hn7 : n ≠ 7) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D ∩ glueV D))).homology n) := by
  obtain ⟨e⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv (intHomotopyEquiv D hU) n
  exact IsZero.of_iso (Work.Cohomology.sphereHomologyZero 7 n (by norm_num) hn0 hn7) e

/-- The top homology of the intersection: `H₇(A ∩ B) ≅ ℤ`. -/
lemma homology_inter_seven (D : CapData) (hU : D.U = collar (-2)) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D ∩ glueV D))).homology 7
      ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) := by
  obtain ⟨e⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv (intHomotopyEquiv D hU) 7
  obtain ⟨e2⟩ := Work.Cohomology.sphereHomologyTop 7 (by norm_num)
  exact ⟨e ≪≫ e2 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩

/-! ## The main computation -/

theorem homology_capped_compact (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Milnor.cappedSpace D))).homology n ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) + (if n = 8 then 1 else 0)) → ℤ)) := by
  have hUopen : IsOpen (glueU D) := isOpen_glueU D
  have hVopen : IsOpen (glueV D) := isOpen_glueV D
  have hcov : glueU D ∪ glueV D = Set.univ := glueU_union_glueV D
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`: `H₀(X) = ℤ` since `X` is path connected
    have hk : (if (0 : ℕ) = 0 then 1 else 0) + (if (0 : ℕ) = 4 then 1 else 0) +
        (if (0 : ℕ) = 8 then 1 else 0) = 1 := by norm_num
    rw [hk]
    haveI : PathConnectedSpace (cappedSpace D) := capped_pathConnected D hU
    haveI hε : IsIso ((TopCat.of (cappedSpace D)).singularHomology₀ε (ModuleCat.of ℤ ℤ)) :=
      inferInstance
    exact ⟨@asIso _ _ _ _ ((TopCat.of (cappedSpace D)).singularHomology₀ε (ModuleCat.of ℤ ℤ)) hε
      ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · rcases eq_or_ne n 4 with rfl | hn4
    · -- degree `4`: `H₄(X) ≅ H₄(A) ≅ ℤ`
      have hk : (if (4 : ℕ) = 0 then 1 else 0) + (if (4 : ℕ) = 4 then 1 else 0) +
          (if (4 : ℕ) = 8 then 1 else 0) = 1 := by norm_num
      rw [hk]
      have hInt3 : IsZero (Work.Cohomology.HInter (glueU D) (glueV D) 3) :=
        isZero_homology_inter D hU 3 (by norm_num) (by norm_num)
      have hInt4 : IsZero (Work.Cohomology.HInter (glueU D) (glueV D) 4) :=
        isZero_homology_inter D hU 4 (by norm_num) (by norm_num)
      haveI hmono : Mono (HomologicalComplex.homologyMap
          (Work.Cohomology.mvRight (glueU D) (glueV D)) 4) :=
        Work.Cohomology.mvH_right_mono _ _ 4 hInt4
      haveI hepi : Epi (HomologicalComplex.homologyMap
          (Work.Cohomology.mvRight (glueU D) (glueV D)) 4) :=
        Work.Cohomology.mvH_right_epi _ _ 3 hInt3
      haveI : IsIso (HomologicalComplex.homologyMap
          (Work.Cohomology.mvRight (glueU D) (glueV D)) 4) := isIso_of_mono_of_epi _
      have hV4 : IsZero ((Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(glueV D))).homology 4) := isZero_homology_glueV D 4 (by norm_num)
      haveI hinl : IsIso (HomologicalComplex.homologyMap
          (biprod.inl : Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D)) ⟶
            Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D)) ⊞
              Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueV D))) 4) :=
        isIso_homologyMap_biprod_inl_chain _ _ 4 hV4
      obtain ⟨eU4⟩ := homology_glueU D 4
      have hfin : ((if (4 : ℕ) = 0 then 1 else 0) + (if (4 : ℕ) = 4 then 1 else 0)) = 1 := by
        norm_num
      rw [hfin] at eU4
      exact ⟨(Work.Cohomology.smallIso (glueU D) (glueV D) hUopen hVopen hcov 4).symm ≪≫
        (asIso (HomologicalComplex.homologyMap
          (Work.Cohomology.mvRight (glueU D) (glueV D)) 4)).symm ≪≫
        (asIso (HomologicalComplex.homologyMap
          (biprod.inl : Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D)) ⟶
            Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueU D)) ⊞
              Work.Cohomology.singularChains ℤ (TopCat.of ↥(glueV D))) 4)).symm ≪≫ eU4⟩
    · rcases eq_or_ne n 8 with rfl | hn8
      · -- degree `8`: `H₈(X) ≅ H₇(A ∩ B) ≅ ℤ`
        have hk : (if (8 : ℕ) = 0 then 1 else 0) + (if (8 : ℕ) = 4 then 1 else 0) +
            (if (8 : ℕ) = 8 then 1 else 0) = 1 := by norm_num
        rw [hk]
        have hB7 : IsZero (Work.Cohomology.HBiprod (glueU D) (glueV D) 7) :=
          Work.Cohomology.isZero_homology_biprod _ _ 7
            (isZero_homology_glueU D 7 (by norm_num) (by norm_num))
            (isZero_homology_glueV D 7 (by norm_num))
        have hB8 : IsZero (Work.Cohomology.HBiprod (glueU D) (glueV D) 8) :=
          Work.Cohomology.isZero_homology_biprod _ _ 8
            (isZero_homology_glueU D 8 (by norm_num) (by norm_num))
            (isZero_homology_glueV D 8 (by norm_num))
        haveI hmono : Mono (Work.Cohomology.mvδ (glueU D) (glueV D) 7) :=
          Work.Cohomology.mvH_delta_mono _ _ 7 hB8
        haveI hepi : Epi (Work.Cohomology.mvδ (glueU D) (glueV D) 7) :=
          Work.Cohomology.mvH_delta_epi _ _ 7 hB7
        haveI : IsIso (Work.Cohomology.mvδ (glueU D) (glueV D) 7) := isIso_of_mono_of_epi _
        obtain ⟨e7⟩ := homology_inter_seven D hU
        exact ⟨(Work.Cohomology.smallIso (glueU D) (glueV D) hUopen hVopen hcov 8).symm ≪≫
          asIso (Work.Cohomology.mvδ (glueU D) (glueV D) 7) ≪≫ e7⟩
      · -- all other degrees
        have hk : (if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) +
            (if n = 8 then 1 else 0) = 0 := by
          rw [if_neg hn0, if_neg hn4, if_neg hn8]
        rw [hk]
        by_cases hn1 : n = 1
        · -- degree `1`: `H₁(X) = 0`
          subst hn1
          have hB1 : IsZero (Work.Cohomology.HBiprod (glueU D) (glueV D) 1) :=
            Work.Cohomology.isZero_homology_biprod _ _ 1
              (isZero_homology_glueU D 1 (by norm_num) (by norm_num))
              (isZero_homology_glueV D 1 (by norm_num))
          haveI : PathConnectedSpace ↥(glueU D ∩ glueV D) := capped_pathConnected_inter D hU
          have hl : Mono (HomologicalComplex.homologyMap
              (Work.Cohomology.mvLeft (glueU D) (glueV D)) 0) :=
            (ModuleCat.mono_iff_injective _).mpr (Work.Cohomology.mvLeft_zero_injective _ _)
          have hz : IsZero (Work.Cohomology.HSmall (glueU D) (glueV D) 1) :=
            Work.Cohomology.mvH_one_isZero _ _ hB1 hl
          have hzX : IsZero ((Work.Cohomology.singularChains ℤ
              (TopCat.of (cappedSpace D))).homology 1) :=
            IsZero.of_iso hz
              (Work.Cohomology.smallIso (glueU D) (glueV D) hUopen hVopen hcov 1).symm
          exact ⟨IsZero.iso hzX (ModuleCat.isZero_of_subsingleton _)⟩
        · -- degrees `n ≥ 2`, `n ∉ {4, 8}`
          have hn2 : 2 ≤ n := by omega
          have hB : IsZero (Work.Cohomology.HBiprod (glueU D) (glueV D) n) :=
            Work.Cohomology.isZero_homology_biprod _ _ n
              (isZero_homology_glueU D n hn0 hn4)
              (isZero_homology_glueV D n hn0)
          have hA : IsZero (Work.Cohomology.HInter (glueU D) (glueV D) (n - 1)) :=
            isZero_homology_inter D hU (n - 1) (by omega) (by omega)
          have hz : IsZero (Work.Cohomology.HSmall (glueU D) (glueV D) n) :=
            Work.Cohomology.mvH_isZero _ _ n (by omega) hB hA
          have hzX : IsZero ((Work.Cohomology.singularChains ℤ
              (TopCat.of (cappedSpace D))).homology n) :=
            IsZero.of_iso hz
              (Work.Cohomology.smallIso (glueU D) (glueV D) hUopen hVopen hcov n).symm
          exact ⟨IsZero.iso hzX (ModuleCat.isZero_of_subsingleton _)⟩

end

end Work.Milnor
