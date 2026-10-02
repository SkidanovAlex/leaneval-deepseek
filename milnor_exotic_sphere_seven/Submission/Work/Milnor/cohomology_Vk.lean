import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomology of the total space `Vk k` of Milnor's bundle `ξ`

`Submission.Milnor.Vk k = (vData k).Glued` is the total space of the rank-`4` real vector bundle
`ξ` over `S⁴` (the open disc bundle), realised as two copies of `MSpace8 = ℝ⁴ × ℍ` glued along
`{x ≠ 0} × ℍ` by the clutching map `(x, y) ↦ (x/‖x‖², û^{-k} y û⁻¹)` (`Submission.Work.Milnor.VBundle`).

Since `ξ` is a vector bundle over `S⁴`, `Vk k` is homotopy equivalent to `S⁴`, so

  `H⁰(Vk k; ℤ) ≅ ℤ`,  `H⁴(Vk k; ℤ) ≅ ℤ`,  and `Hⁿ(Vk k; ℤ) = 0` otherwise.

This is proved here by Mayer–Vietoris for the open cover of `Vk k` by the two chart images
`ιX '' MSpace8` and `ιY '' MSpace8`: both are contractible (they are homeomorphic to `MSpace8`),
they cover `Vk k`, and their intersection is the gluing region `{x ≠ 0} × ℍ`, which
deformation-retracts onto the equator `S³ × {0} ≅ S³`.  Hence the Mayer–Vietoris connecting map
gives `Hⁿ(Vk k) ≅ Hⁿ⁻¹(S³)` for `n ≥ 2`, while `H⁰ = ℤ` (path connectedness) and `H¹ = 0`
(the two contractible pieces kill the positive-degree cohomology of the difference cochain
complex).  The cohomology of `S³` is `Work.Cohomology.sphereCohomologyTop` /
`Work.Cohomology.sphereCohomologyZero`.

The result is stated in the shape requested by the dimension-`8` signature-theorem route to the
exoticness of `Mk (-2)` (`Submission/NOTES.md`, sessions 3 and 8):
`Hⁿ(Vk k; ℤ) ≅ ℤ^((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0))`.
-/

open CategoryTheory AlgebraicTopology Limits
open scoped Topology unitInterval

namespace Work.Milnor

noncomputable section

/-! ## Toolkit -/

/-- Points joined by a homotopy of continuous maps are joined by a path. -/
lemma homotopy_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) : Joined (f x) (g x) :=
  ⟨⟨fun t => H.toContinuousMap (t, x),
    H.continuous.comp (continuous_id.prodMk continuous_const)⟩, H.map_zero_left x, H.map_one_left x⟩

/-! ## The gluing region `{x ≠ 0} × ℍ` deformation-retracts onto the equator `S³` -/

/-- The unit sphere `S³ ⊆ ℝ⁴`. -/
abbrev Sph3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

theorem rank_euclidean4 : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

lemma isPathConnected_Sph3 : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  isPathConnected_sphere rank_euclidean4 0 (by norm_num)

instance instPathConnectedSpaceSph3 : PathConnectedSpace Sph3 :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_Sph3

/-- The base coordinate of a point of the gluing region. -/
def fstCoord (q : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    EuclideanSpace ℝ (Fin 4) := (q : Submission.Milnor.MSpace8).1

/-- The fibre coordinate of a point of the gluing region. -/
def sndCoord (q : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    Quaternion ℝ := (q : Submission.Milnor.MSpace8).2

lemma continuous_fstCoord : Continuous fstCoord := continuous_subtype_val.fst

lemma continuous_sndCoord : Continuous sndCoord := continuous_subtype_val.snd

lemma fstCoord_ne_zero (q : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    fstCoord q ≠ 0 := Submission.Milnor.mem_vOpens.mp q.2

lemma continuous_invNorm_fstCoord :
    Continuous fun q : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} =>
      (‖fstCoord q‖ : ℝ)⁻¹ :=
  (continuous_fstCoord.norm.inv₀ (fun q => norm_ne_zero_iff.mpr (fstCoord_ne_zero q)))

lemma continuous_normInvSmul :
    Continuous fun q : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} =>
      (‖fstCoord q‖ : ℝ)⁻¹ • fstCoord q :=
  continuous_invNorm_fstCoord.smul continuous_fstCoord

lemma normInvSmul_mem (q : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    (‖fstCoord q‖ : ℝ)⁻¹ • fstCoord q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
    Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (fstCoord_ne_zero q)

/-- Normalising the base coordinate: the gluing region retracts to `S³`. -/
def vSphProj : C({p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}, Sph3) where
  toFun q := ⟨(‖fstCoord q‖ : ℝ)⁻¹ • fstCoord q, normInvSmul_mem q⟩
  continuous_toFun := Continuous.subtype_mk continuous_normInvSmul normInvSmul_mem

lemma vSphIncl_mem (z : Sph3) :
    (((z : EuclideanSpace ℝ (Fin 4)), 0) : Submission.Milnor.MSpace8) ∈
      Submission.Milnor.vOpens := by
  rw [Submission.Milnor.mem_vOpens]
  refine norm_ne_zero_iff.mp ?_
  rw [show ‖(z : EuclideanSpace ℝ (Fin 4))‖ = 1 from ?_]
  norm_num
  rw [← dist_zero_right, Metric.mem_sphere.mp z.2]

/-- The equatorial inclusion `S³ → {p ∈ MSpace8 // p.1 ≠ 0}`, `z ↦ (z, 0)`. -/
def vSphIncl : C(Sph3, {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) where
  toFun z := ⟨((z : EuclideanSpace ℝ (Fin 4)), 0), vSphIncl_mem z⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const) vSphIncl_mem

lemma vSphProj_vSphIncl : vSphProj.comp vSphIncl = ContinuousMap.id Sph3 := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  have hz : ‖(z : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
    rw [← dist_zero_right, Metric.mem_sphere.mp z.2]
  change (‖(z : EuclideanSpace ℝ (Fin 4))‖ : ℝ)⁻¹ • (z : EuclideanSpace ℝ (Fin 4)) =
    (z : EuclideanSpace ℝ (Fin 4))
  rw [hz, inv_one, one_smul]

/-- The straight-line homotopy collapsing the fibre and normalising the base coordinate. -/
def vHomotopyVal (p : I × {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    Submission.Milnor.MSpace8 :=
  (((1 - (p.1 : ℝ)) * (‖fstCoord p.2‖ : ℝ)⁻¹ + (p.1 : ℝ)) • fstCoord p.2,
    (p.1 : ℝ) • sndCoord p.2)

lemma vHomotopyVal_mem (p : I × {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    vHomotopyVal p ∈ Submission.Milnor.vOpens := by
  rw [Submission.Milnor.mem_vOpens]
  exact smul_ne_zero (ne_of_gt (by
    have hpos : 0 < (‖fstCoord p.2‖ : ℝ)⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr (fstCoord_ne_zero p.2))
    have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; norm_num
    · have h1 : 0 < 1 - (p.1 : ℝ) := by linarith
      have := mul_pos h1 hpos
      linarith)) (fstCoord_ne_zero p.2)

lemma continuous_vHomotopyVal : Continuous vHomotopyVal := by
  have ht : Continuous fun p : I × {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} =>
      (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun p : I × {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} =>
      fstCoord p.2 := continuous_fstCoord.comp continuous_snd
  have hy : Continuous fun p : I × {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} =>
      sndCoord p.2 := continuous_sndCoord.comp continuous_snd
  have hn : Continuous fun p : I × {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} =>
      (‖fstCoord p.2‖ : ℝ)⁻¹ :=
    hx.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (fstCoord_ne_zero p.2))
  exact (((continuous_const.sub ht).mul hn).add ht).smul hx |>.prodMk (ht.smul hy)

lemma vHomotopy_val_zero (p : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    vHomotopyVal (0, p) = (vSphIncl (vSphProj p)).1 := by
  simp only [vHomotopyVal, vSphIncl, vSphProj, fstCoord, sndCoord]
  simp

lemma vHomotopy_val_one (p : {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :
    vHomotopyVal (1, p) = p.1 := by
  simp only [vHomotopyVal, fstCoord, sndCoord]
  simp

/-- The deformation retraction of the gluing region onto the equator. -/
def vHomotopy : ContinuousMap.Homotopy (vSphIncl.comp vSphProj)
    (ContinuousMap.id {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p => ⟨vHomotopyVal p, vHomotopyVal_mem p⟩,
      Continuous.subtype_mk continuous_vHomotopyVal vHomotopyVal_mem⟩
    (fun p => by apply Subtype.ext; exact vHomotopy_val_zero p)
    (fun p => by apply Subtype.ext; exact vHomotopy_val_one p)

/-- **The gluing region is homotopy equivalent to `S³`.** -/
theorem vOpens_homotopyEquiv_sphere :
    Nonempty (ContinuousMap.HomotopyEquiv
      {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} Sph3) :=
  ⟨ContinuousMap.HomotopyEquiv.mk vSphProj vSphIncl ⟨vHomotopy⟩
    (by rw [vSphProj_vSphIncl])⟩

/-! ## The two chart images of `Vk k` -/

/-- The overlap of the two charts is the image of the gluing region. -/
theorem image_U_eq_inter_range (k : ℤ) :
    (Submission.Milnor.vData k).ιX '' (Submission.Milnor.vData k).U =
      Set.range (Submission.Milnor.vData k).ιX ∩ Set.range (Submission.Milnor.vData k).ιY := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨(Submission.Milnor.vData k).φ x,
      ((Submission.Milnor.vData k).ιX_eq_ιY_iff.mpr ⟨hx, rfl⟩).symm⟩⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    exact ⟨x, (Submission.Milnor.vData k).mem_U_of_ιX_eq_ιY hy.symm, rfl⟩

/-- The intersection of the two chart images is homeomorphic to the gluing region. -/
theorem vk_inter_homeomorph_vOpens (k : ℤ) :
    Nonempty ({z : Submission.Milnor.Vk k //
        z ∈ Set.range (Submission.Milnor.vData k).ιX ∧
          z ∈ Set.range (Submission.Milnor.vData k).ιY} ≃ₜ
      {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens}) :=
  ⟨(((Submission.Milnor.vData k).isOpenEmbedding_ιX.isEmbedding.homeomorphImage
      (Submission.Milnor.vData k).U).trans
    (Homeomorph.setCongr (image_U_eq_inter_range k))).symm⟩

/-- **The intersection of the two chart images is homotopy equivalent to `S³`.** -/
theorem homotopyEquiv_inter_sphere (k : ℤ) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {z : Submission.Milnor.Vk k //
        z ∈ Set.range (Submission.Milnor.vData k).ιX ∧
          z ∈ Set.range (Submission.Milnor.vData k).ιY} Sph3) := by
  obtain ⟨e1⟩ := vk_inter_homeomorph_vOpens k
  obtain ⟨e2⟩ := vOpens_homotopyEquiv_sphere
  exact ⟨e1.toHomotopyEquiv.trans e2⟩

/-- Each chart image is contractible (it is homeomorphic to `MSpace8`). -/
theorem contractibleSpace_range_ιX (k : ℤ) :
    ContractibleSpace ↥(Set.range (Submission.Milnor.vData k).ιX) :=
  ((Submission.Milnor.vData k).isOpenEmbedding_ιX.isEmbedding.toHomeomorph).symm.contractibleSpace

theorem contractibleSpace_range_ιY (k : ℤ) :
    ContractibleSpace ↥(Set.range (Submission.Milnor.vData k).ιY) :=
  ((Submission.Milnor.vData k).isOpenEmbedding_ιY.isEmbedding.toHomeomorph).symm.contractibleSpace

/-! ## Connectivity of `Vk k` -/

lemma exists_nonzero_euclidean4 : ∃ z : EuclideanSpace ℝ (Fin 4), z ≠ 0 := by
  obtain ⟨z, hz⟩ := isPathConnected_Sph3.nonempty
  exact ⟨z, fun h => by
    have h1 := Metric.mem_sphere.mp hz
    rw [h, dist_self] at h1
    norm_num at h1⟩

lemma vOpens_nonempty : Nonempty {p : Submission.Milnor.MSpace8 // p ∈ Submission.Milnor.vOpens} := by
  obtain ⟨z, hz⟩ := exists_nonzero_euclidean4
  exact ⟨((z, 0) : Submission.Milnor.MSpace8), by rw [Submission.Milnor.mem_vOpens]; exact hz⟩

/-- **`Vk k` is path connected.** -/
theorem pathConnectedSpace_Vk (k : ℤ) : PathConnectedSpace (Submission.Milnor.Vk k) := by
  haveI hUc := contractibleSpace_range_ιX k
  haveI hVc := contractibleSpace_range_ιY k
  have hU : IsPathConnected (Set.range (Submission.Milnor.vData k).ιX) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hV : IsPathConnected (Set.range (Submission.Milnor.vData k).ιY) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hne : (Set.range (Submission.Milnor.vData k).ιX ∩
      Set.range (Submission.Milnor.vData k).ιY).Nonempty := by
    obtain ⟨p, hp⟩ := vOpens_nonempty
    refine ⟨(Submission.Milnor.vData k).ιX p, ⟨⟨p, rfl⟩, ?_⟩⟩
    exact ⟨(Submission.Milnor.vData k).φ p,
      ((Submission.Milnor.vData k).ιX_eq_ιY_iff.mpr ⟨hp, rfl⟩).symm⟩
  rw [pathConnectedSpace_iff_univ, ← (Submission.Milnor.vData k).range_ιX_union_range_ιY]
  exact hU.union hV hne

/-- **The intersection of the two chart images is path connected.** -/
theorem pathConnectedSpace_inter_Vk (k : ℤ) :
    PathConnectedSpace ↥(Set.range (Submission.Milnor.vData k).ιX ∩
      Set.range (Submission.Milnor.vData k).ιY) :=
  Work.Cohomology.pathConnectedSpace_of_homotopyEquiv (homotopyEquiv_inter_sphere k).some
    instPathConnectedSpaceSph3

end

end Work.Milnor

namespace Work.Cohomology

noncomputable section

/-- **`H¹` of a space covered by two contractible open sets with path connected intersection
vanishes.**  This is the degree-`0` companion of `mvCohIso`: `U` and `V` contractible kill
`H¹(U) ⊞ H¹(V)`, so the connecting map `δ : H⁰(U ∩ V) → H¹(X)` is epi, while `U ∩ V` path
connected makes `H⁰(U) ⊞ H⁰(V) → H⁰(U ∩ V)` epi; `G ≫ δ = 0` then forces `δ = 0`. -/
theorem cohomology_one_of_contractible_cover {X : TopCat} (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) [ContractibleSpace ↥U] [ContractibleSpace ↥V]
    [PathConnectedSpace ↥(U ∩ V)] :
    CategoryTheory.Limits.IsZero (Work.Cohomology.singularCohomology ℤ 1 X) := by
  have hbU : IsZero ((cochainU U V).homology 1) :=
    contractible ℤ (TopCat.of ↥U) 0
  have hbV : IsZero ((cochainV U V).homology 1) :=
    contractible ℤ (TopCat.of ↥V) 0
  haveI hb : IsZero ((cochainU U V ⊞ cochainV U V).homology 1) :=
    isZero_coh_homology_biprod _ _ 1 hbU hbV
  haveI hE : Epi (mvCohδ U V 0) := by
    have h := mvCoh_H_exact₁ U V 0
    have hg : (ShortComplex.mk (mvCohδ U V 0)
        (HomologicalComplex.homologyMap (mvCochainF U V) (0 + 1))
        (by
          show mvCohδ U V 0 ≫ HomologicalComplex.homologyMap (mvCochainF U V) (0 + 1) = 0
          exact (mvCochainSES U V).δ_comp 0 1 (by simp [ComplexShape.up]))).g = 0 :=
      IsZero.eq_zero_of_tgt hb _
    exact (ShortComplex.exact_iff_epi _ hg).1 h
  have h0epi : Epi (HomologicalComplex.homologyMap (mvCochainG U V) 0) :=
    epi_homologyMap_mvCochainG_zero U V
  haveI := h0epi
  have hδ0 : mvCohδ U V 0 = 0 := by
    have hcomp : HomologicalComplex.homologyMap (mvCochainG U V) 0 ≫ mvCohδ U V 0 = 0 :=
      (mvCochainSES U V).comp_δ 0 1 (by simp [ComplexShape.up])
    exact (cancel_epi _).mp (hcomp.trans (comp_zero).symm)
  have hz : IsZero ((dualComplex ℤ (smallChains U V)).homology 1) := by
    rw [IsZero.iff_id_eq_zero]
    refine (cancel_epi (mvCohδ U V 0)).mp ?_
    rw [hδ0]; simp
  obtain ⟨e⟩ := cohSmallIso (X := X) U V hU hV hcov 1
  exact IsZero.of_iso hz e

end

end Work.Cohomology

namespace Work.Milnor

noncomputable section

/-- **The cohomology of `Vk k`.**  `Vk k` is the total space of a rank-`4` real vector bundle
over `S⁴`, hence homotopy equivalent to `S⁴`: its cohomology with `ℤ` coefficients is `ℤ` in
degrees `0` and `4` and vanishes in every other degree. -/
theorem cohomology_Vk (k : ℤ) (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of (Submission.Milnor.Vk k)) ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0)) → ℤ)) := by
  haveI : PathConnectedSpace (Submission.Milnor.Vk k) := pathConnectedSpace_Vk k
  haveI : PathConnectedSpace ↥(Set.range (Submission.Milnor.vData k).ιX ∩
      Set.range (Submission.Milnor.vData k).ιY) := pathConnectedSpace_inter_Vk k
  haveI : ContractibleSpace ↥(Set.range (Submission.Milnor.vData k).ιX) :=
    contractibleSpace_range_ιX k
  haveI : ContractibleSpace ↥(Set.range (Submission.Milnor.vData k).ιY) :=
    contractibleSpace_range_ιY k
  have hU : IsOpen (Set.range (Submission.Milnor.vData k).ιX) :=
    (Submission.Milnor.vData k).isOpenMap_ιX.isOpen_range
  have hV : IsOpen (Set.range (Submission.Milnor.vData k).ιY) :=
    (Submission.Milnor.vData k).isOpenMap_ιY.isOpen_range
  have hcov : Set.range (Submission.Milnor.vData k).ιX ∪
      Set.range (Submission.Milnor.vData k).ιY = Set.univ :=
    (Submission.Milnor.vData k).range_ιX_union_range_ιY
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`: `H⁰ = ℤ` since `Vk k` is path connected
    have hfin : (if (0 : ℕ) = 0 then 1 else 0) + (if (0 : ℕ) = 4 then 1 else 0) = 1 := by
      norm_num
    rw [hfin]
    obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero ℤ
      (TopCat.of (Submission.Milnor.Vk k))
    exact ⟨e ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · rcases eq_or_ne n 1 with rfl | hn1
    · -- degree `1`: `H¹ = 0` for a cover by two contractible open sets
      have hfin : (if (1 : ℕ) = 0 then 1 else 0) + (if (1 : ℕ) = 4 then 1 else 0) = 0 := by
        norm_num
      rw [hfin]
      exact ⟨IsZero.iso (Work.Cohomology.cohomology_one_of_contractible_cover
        (X := TopCat.of (Submission.Milnor.Vk k))
        (Set.range (Submission.Milnor.vData k).ιX)
        (Set.range (Submission.Milnor.vData k).ιY) hU hV hcov)
        (ModuleCat.isZero_of_subsingleton _)⟩
    · rcases eq_or_ne n 4 with rfl | hn4
      · -- degree `4`: Mayer–Vietoris and `H³(S³) ≅ ℤ`
        have hfin : (if (4 : ℕ) = 0 then 1 else 0) + (if (4 : ℕ) = 4 then 1 else 0) = 1 := by
          norm_num
        rw [hfin]
        obtain ⟨e1⟩ := Work.Cohomology.mvCohIso (X := TopCat.of (Submission.Milnor.Vk k))
          (Set.range (Submission.Milnor.vData k).ιX)
          (Set.range (Submission.Milnor.vData k).ιY) hU hV hcov 3 (by norm_num)
        obtain ⟨e2⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
          (homotopyEquiv_inter_sphere k).some 3
        obtain ⟨e3⟩ := Work.Cohomology.sphereCohomologyTop 3 (by norm_num)
        exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
      · -- all other degrees `n ≥ 2`, `n ≠ 4`: `Hⁿ ≅ Hⁿ⁻¹(S³) = 0`
        have hn2 : 2 ≤ n := by omega
        have hfin : (if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) = 0 := by
          rw [if_neg hn0, if_neg hn4, add_zero]
        rw [hfin]
        obtain ⟨e1⟩ := Work.Cohomology.mvCohIso (X := TopCat.of (Submission.Milnor.Vk k))
          (Set.range (Submission.Milnor.vData k).ιX)
          (Set.range (Submission.Milnor.vData k).ιY) hU hV hcov (n - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at e1
        obtain ⟨e2⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
          (homotopyEquiv_inter_sphere k).some (n - 1)
        have hz : IsZero (Work.Cohomology.singularCohomology ℤ (n - 1) (TopCat.of Sph3)) :=
          Work.Cohomology.sphereCohomologyZero 3 (n - 1) (by norm_num) (by omega) (by omega)
        exact ⟨e1 ≪≫ e2 ≪≫ IsZero.iso hz (ModuleCat.isZero_of_subsingleton _)⟩

end

end Work.Milnor
