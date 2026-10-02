import Mathlib
import Submission.Work.Milnor.Model8
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.collar_homotopyEquiv_Mk
import Submission.Work.Milnor.Homeo7
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Milnor.cohomology_Vk
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomology of the capped space `X = D(ξ) ∪_F D⁸`

The closed `8`-manifold `X = cappedSpace D` of `Submission/Work/Milnor/Model8.lean` is the union
of the open disc bundle `A = ιX '' (Vk (-2))` (homotopy equivalent to `S⁴`) and the image `B` of
`ℝ⁸` (contractible), with intersection `A ∩ B ≃ S⁷` (the collar, `Work.Milnor.collar (-2)`).

Its singular cohomology with `ℤ` coefficients is therefore `ℤ` in degrees `0`, `4` and `8` and
zero in every other degree: the Mayer–Vietoris long exact sequence for the cover `{A, B}` has
`Hⁿ(A) = ℤ` for `n ∈ {0,4}`, `Hⁿ(B) = ℤ` for `n = 0`, `Hⁿ(A∩B) = ℤ` for `n ∈ {0,7}`, and all
other terms vanish, so that
* `H⁴(X) ≅ H⁴(A)` (the `B`-summand and the `A ∩ B`-terms adjacent to degree `4` vanish),
* `H⁸(X) ≅ H⁷(A ∩ B)` (the connecting map `δ₇` is an isomorphism),
* `H¹(X) = 0` (the difference map `H⁰(A) ⊕ H⁰(B) → H⁰(A ∩ B)` is onto, so `δ₀ = 0`),
* `Hⁿ(X) = 0` for all other `n ∉ {0,4,8}` (both neighbours in the sequence vanish).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Milnor

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Submission.Milnor

/-! ## Extraction from the Mayer–Vietoris long exact sequence -/

/-- The exactness of the Mayer–Vietoris sequence at the middle term `Hⁿ(X)`. -/
theorem mvCoh_H_exact₂ {X : TopCat} (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (Cohomology.mvCochainF U V) n)
      (HomologicalComplex.homologyMap (Cohomology.mvCochainG U V) n)
      (by rw [← HomologicalComplex.homologyMap_comp, Cohomology.mvCochainComp,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (Cohomology.mvCochainSES U V).homology_exact₂ n

/-- If `Hⁿ(U ∩ V) = 0` then `Hⁿ⁺¹(X) → Hⁿ⁺¹(U) ⊕ Hⁿ⁺¹(V)` is injective. -/
theorem mvCohF_mono {X : TopCat} (U V : Set X) (n : ℕ)
    (h : IsZero ((Cohomology.cochainUV U V).homology n)) :
    Mono (HomologicalComplex.homologyMap (Cohomology.mvCochainF U V) (n + 1)) := by
  have hδ : Cohomology.mvCohδ U V n = 0 := IsZero.eq_zero_of_src h _
  exact (ShortComplex.exact_iff_mono _ hδ).mp (Cohomology.mvCoh_H_exact₁ U V n)

/-- If `Hⁿ(U ∩ V) = 0` then `Hⁿ(X) → Hⁿ(U) ⊕ Hⁿ(V)` is surjective. -/
theorem mvCohF_epi {X : TopCat} (U V : Set X) (n : ℕ)
    (h : IsZero ((Cohomology.cochainUV U V).homology n)) :
    Epi (HomologicalComplex.homologyMap (Cohomology.mvCochainF U V) n) := by
  have hG : HomologicalComplex.homologyMap (Cohomology.mvCochainG U V) n = 0 :=
    IsZero.eq_zero_of_tgt h _
  exact (ShortComplex.exact_iff_epi _ hG).mp (mvCoh_H_exact₂ U V n)

/-- If `Hⁿ(U) ⊕ Hⁿ(V) = 0` then `Hⁿ(U ∩ V) → Hⁿ⁺¹(X)` is injective. -/
theorem mvCohδ_mono {X : TopCat} (U V : Set X) (n : ℕ)
    (h : IsZero ((Cohomology.cochainU U V ⊞ Cohomology.cochainV U V).homology n)) :
    Mono (Cohomology.mvCohδ U V n) := by
  have hG : HomologicalComplex.homologyMap (Cohomology.mvCochainG U V) n = 0 :=
    IsZero.eq_zero_of_src h _
  exact (ShortComplex.exact_iff_mono _ hG).mp (Cohomology.mvCoh_H_exact₃ U V n)

/-- If `Hⁿ⁺¹(U) ⊕ Hⁿ⁺¹(V) = 0` then `Hⁿ(U ∩ V) → Hⁿ⁺¹(X)` is surjective. -/
theorem mvCohδ_epi {X : TopCat} (U V : Set X) (n : ℕ)
    (h : IsZero ((Cohomology.cochainU U V ⊞ Cohomology.cochainV U V).homology (n+1))) :
    Epi (Cohomology.mvCohδ U V n) := by
  have hF : HomologicalComplex.homologyMap (Cohomology.mvCochainF U V) (n+1) = 0 :=
    IsZero.eq_zero_of_tgt h _
  exact (ShortComplex.exact_iff_epi _ hF).mp (Cohomology.mvCoh_H_exact₁ U V n)

/-- If `Hⁿ(U)`, `Hⁿ(V)` and `Hⁿ⁻¹(U ∩ V)` all vanish then so does `Hⁿ(X)` (`n ≥ 1`). -/
theorem mvCoh_isZero {X : TopCat} (U V : Set X) (n : ℕ) (hn : 1 ≤ n)
    (hU : IsZero ((Cohomology.cochainU U V).homology n))
    (hV : IsZero ((Cohomology.cochainV U V).homology n))
    (hUV : IsZero ((Cohomology.cochainUV U V).homology (n - 1))) :
    IsZero ((Cohomology.dualComplex ℤ (Cohomology.smallChains U V)).homology n) := by
  haveI hF : Mono (HomologicalComplex.homologyMap (Cohomology.mvCochainF U V) n) := by
    have h := mvCohF_mono U V (n-1) hUV
    rwa [Nat.sub_add_cancel hn] at h
  exact IsZero.of_mono (HomologicalComplex.homologyMap (Cohomology.mvCochainF U V) n)
    (Cohomology.isZero_coh_homology_biprod (Cohomology.cochainU U V)
      (Cohomology.cochainV U V) n hU hV)

/-- `H¹(X) = 0` when `U ∩ V` is path connected and `H¹(U) = H¹(V) = 0`. -/
theorem mvCoh_one_isZero {X : TopCat} (U V : Set X) [PathConnectedSpace ↥(U ∩ V)]
    (hU : IsZero ((Cohomology.cochainU U V).homology 1))
    (hV : IsZero ((Cohomology.cochainV U V).homology 1)) :
    IsZero ((Cohomology.dualComplex ℤ (Cohomology.smallChains U V)).homology 1) := by
  have hbij : IsZero ((Cohomology.cochainU U V ⊞ Cohomology.cochainV U V).homology 1) :=
    Cohomology.isZero_coh_homology_biprod (Cohomology.cochainU U V)
      (Cohomology.cochainV U V) 1 hU hV
  have hexact := Cohomology.mvCoh_H_exact₃ U V 0
  have hrange := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hexact
  haveI hGepi : Epi (HomologicalComplex.homologyMap (Cohomology.mvCochainG U V) 0) :=
    Cohomology.epi_homologyMap_mvCochainG_zero U V
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (Cohomology.mvCochainG U V) 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp hGepi
  have htop : LinearMap.ker (Cohomology.mvCohδ U V 0).hom = ⊤ := by
    rw [← hrange, LinearMap.range_eq_top.mpr hsurj]
  have hδ0 : Cohomology.mvCohδ U V 0 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Submodule.eq_top_iff'.mp htop x
  have hF1 : HomologicalComplex.homologyMap (Cohomology.mvCochainF U V) (0+1) = 0 :=
    IsZero.eq_zero_of_tgt hbij _
  exact (Cohomology.mvCoh_H_exact₁ U V 0).isZero_X₂ hδ0 hF1

/-- The homology of a biproduct of cochain complexes with a vanishing second factor is the
homology of the first factor. -/
lemma isIso_homologyMap_biprod_inl (K L : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : IsZero (L.homology k)) :
    IsIso (HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) k) := by
  refine IsIso.mk ⟨HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) k, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst, HomologicalComplex.homologyMap_id]
  · have htot := Cohomology.coh_homologyMap_total K L k
    rw [IsZero.eq_zero_of_tgt h
      (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) k)] at htot
    simpa using htot

/-! ## The two pieces of the capped space and their intersection -/

/-- `cappedSpace D` as a `TopCat`. -/
abbrev glueX (D : CapData) : TopCat := TopCat.of (cappedSpace D)

/-- The `Vk (-2)`-piece of the capped space. -/
def glueU (D : CapData) : Set (glueX D) := Set.range D.ιX

/-- The `ℝ⁸`-piece of the capped space. -/
def glueV (D : CapData) : Set (glueX D) := Set.range D.ιY

lemma isOpen_glueU (D : CapData) : IsOpen (glueU D) := D.isOpenMap_ιX.isOpen_range
lemma isOpen_glueV (D : CapData) : IsOpen (glueV D) := D.isOpenMap_ιY.isOpen_range
lemma glueU_union_glueV (D : CapData) : glueU D ∪ glueV D = Set.univ :=
  D.range_ιX_union_range_ιY

/-- The intersection of the two pieces is the image of the glued open subset. -/
lemma cappedImage_U (D : CapData) : D.ιX '' D.U = glueU D ∩ glueV D := by
  ext z; constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨D.φ x, (D.ιX_eq_ιY_iff.mpr ⟨hx, rfl⟩).symm⟩⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    exact ⟨x, D.mem_U_of_ιX_eq_ιY hy.symm, rfl⟩

/-- The intersection of the two pieces is homeomorphic to the collar. -/
def homeoIntCollar (D : CapData) (hU : D.U = collar (-2)) :
    ↥(glueU D ∩ glueV D) ≃ₜ ↥(collar (-2)) :=
  ((D.isOpenEmbedding_ιX.isEmbedding.homeomorphImage D.U).trans
    (Homeomorph.setCongr (cappedImage_U D))).symm.trans
    (Homeomorph.setCongr hU)

/-- The intersection of the two pieces is homotopy equivalent to `S⁷`. -/
def intHomotopyEquiv (D : CapData) (hU : D.U = collar (-2)) :
    ContinuousMap.HomotopyEquiv ↥(glueU D ∩ glueV D)
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) :=
  (homeoIntCollar D hU).toHomotopyEquiv.trans
    ((collar_homotopyEquiv_Mk (-2)).some.trans
      (mk_minus_two_homeo.some).toHomotopyEquiv)

/-- A point of the collar. -/
lemma collarPoint_mem :
    ((vData (-2)).ιX (((0 : EuclideanSpace ℝ (Fin 4)), (1 : Quaternion ℝ)) : MSpace8))
      ∈ collar (-2) := by
  rw [mem_collar, fibreNormFun_ιX, norm_one]; norm_num

/-- The intersection of the two pieces is path connected. -/
lemma capped_pathConnected_inter (D : CapData) (hU : D.U = collar (-2)) :
    PathConnectedSpace ↥(glueU D ∩ glueV D) := by
  have hS7 : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 (by norm_num)
    rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin 8)) = (8 : Cardinal) from by
      have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin 8) ℝ).toLinearEquiv
      rw [h2]; exact rank_fin_fun 8]
    norm_num
  exact Cohomology.pathConnectedSpace_of_homotopyEquiv (intHomotopyEquiv D hU) hS7

/-- The capped space is path connected. -/
lemma capped_pathConnected (D : CapData) (hU : D.U = collar (-2)) :
    PathConnectedSpace (cappedSpace D) := by
  haveI hA : PathConnectedSpace ↥(glueU D) :=
    Cohomology.pathConnectedSpace_of_homotopyEquiv
      (D.isOpenEmbedding_ιX.isEmbedding.toHomeomorph.toHomotopyEquiv).symm
      (pathConnectedSpace_Vk (-2))
  haveI hB : PathConnectedSpace ↥(glueV D) :=
    Cohomology.pathConnectedSpace_of_homotopyEquiv
      (D.isOpenEmbedding_ιY.isEmbedding.toHomeomorph.toHomotopyEquiv).symm inferInstance
  have hne : (glueU D ∩ glueV D).Nonempty :=
    ⟨D.ιX ((vData (-2)).ιX (((0 : EuclideanSpace ℝ (Fin 4)), (1 : Quaternion ℝ)) : MSpace8)),
      ⟨⟨_, rfl⟩, ⟨D.φ _, (D.ιX_eq_ιY_iff.mpr ⟨by rw [hU]; exact collarPoint_mem, rfl⟩).symm⟩⟩⟩
  have hU' : IsPathConnected (glueU D) := isPathConnected_iff_pathConnectedSpace.mpr hA
  have hV' : IsPathConnected (glueV D) := isPathConnected_iff_pathConnectedSpace.mpr hB
  rw [pathConnectedSpace_iff_univ, ← D.range_ιX_union_range_ιY]
  exact hU'.union hV' hne

/-! ## The cohomology of the individual pieces -/

lemma isZero_cochainU (D : CapData) (n : ℕ) (hn0 : n ≠ 0) (hn4 : n ≠ 4) :
    IsZero ((Cohomology.cochainU (glueU D) (glueV D)).homology n) := by
  obtain ⟨e⟩ := Cohomology.cohomologyIso_of_homotopyEquiv
    (D.isOpenEmbedding_ιX.isEmbedding.toHomeomorph.toHomotopyEquiv) n
  obtain ⟨e2⟩ := cohomology_Vk (-2) n
  have hfin : (if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) = 0 := by
    rw [if_neg hn0, if_neg hn4]
  rw [hfin] at e2
  have hz : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso (IsZero.of_iso hz e2) e.symm

lemma isZero_cochainV (D : CapData) (n : ℕ) (hn0 : n ≠ 0) :
    IsZero ((Cohomology.cochainV (glueU D) (glueV D)).homology n) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  haveI : ContractibleSpace ↥(glueV D) :=
    (D.isOpenEmbedding_ιY.isEmbedding.toHomeomorph).symm.contractibleSpace
  have h := Cohomology.contractible ℤ (TopCat.of ↥(glueV D)) (n-1)
  rwa [Nat.sub_add_cancel hn] at h

lemma isZero_cochainUV (D : CapData) (hU : D.U = collar (-2)) (n : ℕ)
    (hn0 : n ≠ 0) (hn7 : n ≠ 7) :
    IsZero ((Cohomology.cochainUV (glueU D) (glueV D)).homology n) := by
  obtain ⟨e⟩ := Cohomology.cohomologyIso_of_homotopyEquiv (intHomotopyEquiv D hU) n
  exact IsZero.of_iso (Cohomology.sphereCohomologyZero 7 n (by norm_num) hn0 hn7) e

lemma glueU_cohomology_four (D : CapData) :
    Nonempty ((Cohomology.cochainU (glueU D) (glueV D)).homology 4 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := Cohomology.cohomologyIso_of_homotopyEquiv
    (D.isOpenEmbedding_ιX.isEmbedding.toHomeomorph.toHomotopyEquiv) 4
  obtain ⟨e2⟩ := cohomology_Vk (-2) 4
  have hfin : (if (4:ℕ) = 0 then 1 else 0) + (if (4:ℕ) = 4 then 1 else 0) = 1 := by norm_num
  rw [hfin] at e2
  exact ⟨e.symm ≪≫ e2 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso⟩

lemma glueUV_cohomology_seven (D : CapData) (hU : D.U = collar (-2)) :
    Nonempty ((Cohomology.cochainUV (glueU D) (glueV D)).homology 7 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := Cohomology.cohomologyIso_of_homotopyEquiv (intHomotopyEquiv D hU) 7
  obtain ⟨e2⟩ := Cohomology.sphereCohomologyTop 7 (by norm_num)
  exact ⟨e ≪≫ e2⟩

/-! ## The main computation -/

theorem cohomology_capped (D : Work.Milnor.CapData)
    (hU : D.U = Work.Milnor.collar (-2))
    (hV : D.V = {z : EuclideanSpace ℝ (Fin 8) | 1 / 2 < ‖z‖}) (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of (Work.Milnor.cappedSpace D)) ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) +
        (if n = 8 then 1 else 0)) → ℤ)) := by
  obtain ⟨eSmall⟩ := Cohomology.cohSmallIso (glueU D) (glueV D)
    (isOpen_glueU D) (isOpen_glueV D) (glueU_union_glueV D) n
  by_cases h0 : n = 0
  · subst h0
    have hk : (if (0:ℕ) = 0 then 1 else 0) + (if (0:ℕ) = 4 then 1 else 0) +
        (if (0:ℕ) = 8 then 1 else 0) = 1 := by norm_num
    rw [hk]
    haveI : PathConnectedSpace (cappedSpace D) := capped_pathConnected D hU
    obtain ⟨e0⟩ := Cohomology.singularCohomology_zero ℤ (TopCat.of (cappedSpace D))
    exact ⟨e0 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · by_cases h4 : n = 4
    · subst h4
      have hk : (if (4:ℕ) = 0 then 1 else 0) + (if (4:ℕ) = 4 then 1 else 0) +
          (if (4:ℕ) = 8 then 1 else 0) = 1 := by norm_num
      rw [hk]
      have hCU3 : IsZero ((Cohomology.cochainUV (glueU D) (glueV D)).homology 3) :=
        isZero_cochainUV D hU 3 (by norm_num) (by norm_num)
      have hCU4 : IsZero ((Cohomology.cochainUV (glueU D) (glueV D)).homology 4) :=
        isZero_cochainUV D hU 4 (by norm_num) (by norm_num)
      haveI hmono : Mono (HomologicalComplex.homologyMap
          (Cohomology.mvCochainF (glueU D) (glueV D)) 4) := mvCohF_mono (glueU D) (glueV D) 3 hCU3
      haveI hepi : Epi (HomologicalComplex.homologyMap
          (Cohomology.mvCochainF (glueU D) (glueV D)) 4) := mvCohF_epi (glueU D) (glueV D) 4 hCU4
      haveI hF4 : IsIso (HomologicalComplex.homologyMap
          (Cohomology.mvCochainF (glueU D) (glueV D)) 4) := isIso_of_mono_of_epi _
      have hZ4 : IsZero ((Cohomology.cochainV (glueU D) (glueV D)).homology 4) :=
        isZero_cochainV D 4 (by norm_num)
      haveI hinl : IsIso (HomologicalComplex.homologyMap
          (biprod.inl : Cohomology.cochainU (glueU D) (glueV D) ⟶
            Cohomology.cochainU (glueU D) (glueV D) ⊞ Cohomology.cochainV (glueU D) (glueV D)) 4) :=
        isIso_homologyMap_biprod_inl _ _ 4 hZ4
      obtain ⟨eU4⟩ := glueU_cohomology_four D
      exact ⟨eSmall ≪≫
        asIso (HomologicalComplex.homologyMap (Cohomology.mvCochainF (glueU D) (glueV D)) 4) ≪≫
        (asIso (HomologicalComplex.homologyMap
          (biprod.inl : Cohomology.cochainU (glueU D) (glueV D) ⟶
            Cohomology.cochainU (glueU D) (glueV D) ⊞
              Cohomology.cochainV (glueU D) (glueV D)) 4)).symm ≪≫
        eU4 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
    · by_cases h8 : n = 8
      · subst h8
        have hk : (if (8:ℕ) = 0 then 1 else 0) + (if (8:ℕ) = 4 then 1 else 0) +
            (if (8:ℕ) = 8 then 1 else 0) = 1 := by norm_num
        rw [hk]
        have hZ8 : IsZero ((Cohomology.cochainU (glueU D) (glueV D) ⊞
            Cohomology.cochainV (glueU D) (glueV D)).homology 8) :=
          Cohomology.isZero_coh_homology_biprod _ _ 8
            (isZero_cochainU D 8 (by norm_num) (by norm_num)) (isZero_cochainV D 8 (by norm_num))
        have hZ7 : IsZero ((Cohomology.cochainU (glueU D) (glueV D) ⊞
            Cohomology.cochainV (glueU D) (glueV D)).homology 7) :=
          Cohomology.isZero_coh_homology_biprod _ _ 7
            (isZero_cochainU D 7 (by norm_num) (by norm_num)) (isZero_cochainV D 7 (by norm_num))
        haveI hepi : Epi (Cohomology.mvCohδ (glueU D) (glueV D) 7) :=
          mvCohδ_epi (glueU D) (glueV D) 7 (by simpa using hZ8)
        haveI hmono : Mono (Cohomology.mvCohδ (glueU D) (glueV D) 7) :=
          mvCohδ_mono (glueU D) (glueV D) 7 hZ7
        haveI hiso : IsIso (Cohomology.mvCohδ (glueU D) (glueV D) 7) := isIso_of_mono_of_epi _
        obtain ⟨eUV7⟩ := glueUV_cohomology_seven D hU
        exact ⟨eSmall ≪≫ (asIso (Cohomology.mvCohδ (glueU D) (glueV D) 7)).symm ≪≫
          eUV7 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
      · have hk : (if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) +
            (if n = 8 then 1 else 0) = 0 := by
          rw [if_neg h0, if_neg h4, if_neg h8]
        rw [hk]
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
        by_cases hn1' : n = 1
        · subst hn1'
          haveI : PathConnectedSpace ↥(glueU D ∩ glueV D) := capped_pathConnected_inter D hU
          have hz := mvCoh_one_isZero (glueU D) (glueV D)
            (isZero_cochainU D 1 (by norm_num) (by norm_num))
            (isZero_cochainV D 1 (by norm_num))
          exact ⟨eSmall ≪≫ IsZero.iso hz
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩
        · have hz := mvCoh_isZero (glueU D) (glueV D) n hn1
            (isZero_cochainU D n h0 h4) (isZero_cochainV D n h0)
            (isZero_cochainUV D hU (n-1) (by omega) (by omega))
          exact ⟨eSmall ≪≫ IsZero.iso hz
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩

end

end Work.Milnor
