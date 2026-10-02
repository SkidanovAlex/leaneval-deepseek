import Mathlib
import Submission.Work.ThomBordism.Grassmann.CxGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-!
# Assembly of the isomorphism `zStd ⊗_ℝ ℂ ≅ O(1) ⊕ O(-1)`

This module checks the eight hypotheses of `Work.Thom.nonempty_bundleIso_of_gauge` for the gauge
family `Phi`, `Phiinv` of `Submission/Work/ThomBordism/Grassmann/CxModel.lean`, proving
`Work.ThomBordism.Grassmann.nonempty_complexificationCore_zStd_lineC`.
-/

open Work.TangentClasses Work.Thom

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- The Whitney sum `O(1) ⊕ O(-1)` over `ℂP²`. -/
abbrev W' : VectorBundleCore ℂ (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 3 × Fin 3) :=
  Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2)

lemma baseSet_complexificationCore_zStd (i : Fin 3) :
    (complexificationCore zStd).baseSet i = Work.Projective.chartSet i := by
  rw [Work.Thom.complexificationCore_baseSet, zStd, RealBundle.mapFibre_baseSet,
    Work.Thom.realification_baseSet, Work.Gen.tautDual_baseSet]

lemma baseSet_whitneySum (t : Fin 3 × Fin 3) :
    W'.baseSet t = Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2 := by
  rw [W', Work.Whitney.whitneySum_baseSet, Work.Gen.tautDual_baseSet,
    Work.Gen.tautLine_baseSet]

/-! ## Pointwise forms of the fibre identities -/

lemma GmInv_apply_Gm (x : EuclideanSpace ℂ (Fin 2)) : GmInv (Gm x) = x := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F x)
    GmInv_comp_Gm
  simpa using h

lemma Gm_apply_GmInv (x : EuclideanSpace ℂ (Fin 2)) : Gm (GmInv x) = x := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F x)
    Gm_comp_GmInv
  simpa using h

lemma gaugeDiag_apply_gaugeDiagInv (i : Fin 3) (b : Work.Projective.CP 2)
    (x : EuclideanSpace ℂ (Fin 2)) : gaugeDiag i b (gaugeDiagInv i b x) = x := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F x)
    (gaugeDiag_comp_gaugeDiagInv i b)
  simpa using h

lemma gaugeDiagInv_apply_gaugeDiag (i : Fin 3) (b : Work.Projective.CP 2)
    (x : EuclideanSpace ℂ (Fin 2)) : gaugeDiagInv i b (gaugeDiag i b x) = x := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F x)
    (gaugeDiagInv_comp_gaugeDiag i b)
  simpa using h

/-- The transition function of `complexificationCore zStd`, pointwise. -/
lemma complexificationCore_coordChange_apply (i j : Fin 3) (b : Work.Projective.CP 2)
    (x : EuclideanSpace ℂ (Fin 2)) :
    ((complexificationCore zStd).coordChange i j b) x
      = Gm ((cMat (Work.Gen.homCoord 2 j i b)) (GmInv x)) := by
  rw [show (complexificationCore zStd).coordChange i j b = cxTrans (zStd.coordChange i j b) from rfl,
    cxTrans_zStd_coordChange i j b]
  rfl

/-- The diagonal gauge identity, pointwise. -/
lemma gaugeDiag_cMat_apply (i i' : Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) (hb' : b ∈ Work.Projective.chartSet i')
    (x : EuclideanSpace ℂ (Fin 2)) :
    gaugeDiag i b ((cMat (Work.Gen.homCoord 2 i i' b)) x)
      = (diagP (Work.Gen.homCoord 2 i i' b) ((Work.Gen.homCoord 2 i i' b)⁻¹))
          (gaugeDiag i' b x) := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F x)
    (gaugeDiag_cMat i i' hb hb')
  simpa only [ContinuousLinearMap.comp_apply] using h

/-- The diagonal transition function of `O(1) ⊕ O(-1)`, pointwise. -/
lemma whitneySum_diag_coordChange_apply (i i' : Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) (hb' : b ∈ Work.Projective.chartSet i')
    (x : EuclideanSpace ℂ (Fin 2)) :
    (W'.coordChange (i', i') (i, i) b) x
      = (diagP (Work.Gen.homCoord 2 i i' b) ((Work.Gen.homCoord 2 i i' b)⁻¹)) x := by
  rw [whitneySum_diag_coordChange i i' hb hb']

/-- The cocycle identity of the transition functions of a bundle, pointwise. -/
lemma coordChange_comp_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*}
    [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type*}
    (Z : VectorBundleCore 𝕜 B F ι) (p q r : ι) {b : B}
    (hb : b ∈ Z.baseSet p) (hb' : b ∈ Z.baseSet q) (hbr : b ∈ Z.baseSet r)
    (x : F) : (Z.coordChange q r b) ((Z.coordChange p q b) x) = (Z.coordChange p r b) x :=
  Z.coordChange_comp p q r b ⟨⟨hb, hb'⟩, hbr⟩ x

lemma whitneySum_coordChange_comp_apply (p q r : Fin 3 × Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ W'.baseSet p) (hb' : b ∈ W'.baseSet q) (hbr : b ∈ W'.baseSet r)
    (x : EuclideanSpace ℂ (Fin 2)) :
    (W'.coordChange q r b) ((W'.coordChange p q b) x) = (W'.coordChange p r b) x :=
  coordChange_comp_apply W' p q r hb hb' hbr x

/-! ## The eight conditions -/

lemma mem_chartSet_of_mem_baseSet {i : Fin 3} {b : Work.Projective.CP 2}
    (hb : b ∈ (complexificationCore zStd).baseSet i) : b ∈ Work.Projective.chartSet i := by
  rwa [baseSet_complexificationCore_zStd] at hb

lemma mem_baseSet_W'_of {i : Fin 3} {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) : b ∈ W'.baseSet (i, i) := by
  rw [baseSet_whitneySum]
  exact ⟨hb, hb⟩

lemma coordChange_self_W' (i : Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) (x : EuclideanSpace ℂ (Fin 2)) :
    (W'.coordChange (i, i) (i, i) b) x = x :=
  W'.coordChange_self (i, i) b (mem_baseSet_W'_of hb) x

lemma complexificationCore_coordChange_eq (i j : Fin 3) (b : Work.Projective.CP 2) :
    (complexificationCore zStd).coordChange i j b
      = Gm.comp ((cMat (Work.Gen.homCoord 2 j i b)).comp GmInv) := by
  rw [show (complexificationCore zStd).coordChange i j b = cxTrans (zStd.coordChange i j b) from rfl,
    cxTrans_zStd_coordChange i j b]

lemma continuousOn_W'_coordChange_diag (i : Fin 3) (t : Fin 3 × Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 => W'.coordChange (i, i) t b)
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) := by
  have h := W'.continuousOn_coordChange (i, i) t
  rw [baseSet_whitneySum (i, i), baseSet_whitneySum t] at h
  refine h.mono ?_
  intro b hb
  exact ⟨⟨hb.1, hb.1⟩, hb.2⟩

lemma continuousOn_W'_coordChange_diag_inv (i : Fin 3) (t : Fin 3 × Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 => W'.coordChange t (i, i) b)
      ((Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2) ∩
        Work.Projective.chartSet i) := by
  have h := W'.continuousOn_coordChange t (i, i)
  rw [baseSet_whitneySum t, baseSet_whitneySum (i, i)] at h
  refine h.mono ?_
  intro b hb
  exact ⟨hb.1, ⟨hb.2, hb.2⟩⟩

theorem Phi_hcont (i : Fin 3) (t : Fin 3 × Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 => Phi i t b)
      ((complexificationCore zStd).baseSet i ∩ W'.baseSet t) := by
  have hA : ContinuousOn (fun b : Work.Projective.CP 2 => (gaugeDiag i b).comp GmInv)
      (Work.Projective.chartSet i) :=
    ContinuousOn.clm_comp (continuousOn_gaugeDiag i) continuousOn_const
  have hcoord := continuousOn_W'_coordChange_diag i t
  have hmain : ContinuousOn
      (fun b : Work.Projective.CP 2 =>
        (W'.coordChange (i, i) t b).comp ((gaugeDiag i b).comp GmInv))
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) :=
    ContinuousOn.clm_comp hcoord (hA.mono Set.inter_subset_left)
  have hfun : (fun b : Work.Projective.CP 2 => Phi i t b) = fun b =>
      (W'.coordChange (i, i) t b).comp ((gaugeDiag i b).comp GmInv) := by
    funext b; rw [Phi]
  rw [hfun]
  refine hmain.mono ?_
  intro b hb
  rw [baseSet_complexificationCore_zStd, baseSet_whitneySum] at hb
  exact hb

theorem Phiinv_hcont (i : Fin 3) (t : Fin 3 × Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 => Phiinv i t b)
      ((complexificationCore zStd).baseSet i ∩ W'.baseSet t) := by
  have hA : ContinuousOn (fun b : Work.Projective.CP 2 => Gm.comp (gaugeDiagInv i b))
      (Work.Projective.chartSet i) :=
    ContinuousOn.clm_comp continuousOn_const (continuousOn_gaugeDiagInv i)
  have hcoord := continuousOn_W'_coordChange_diag_inv i t
  have hcoord' : ContinuousOn (fun b : Work.Projective.CP 2 => W'.coordChange t (i, i) b)
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) :=
    hcoord.mono (fun b hb => ⟨hb.2, hb.1⟩)
  have hA' := hA.mono (Set.inter_subset_left :
    Work.Projective.chartSet i ∩
      (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2) ⊆
      Work.Projective.chartSet i)
  have hmain : ContinuousOn
      (fun b : Work.Projective.CP 2 =>
        (Gm.comp (gaugeDiagInv i b)).comp (W'.coordChange t (i, i) b))
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) :=
    ContinuousOn.clm_comp hA' hcoord'
  have hfun : (fun b : Work.Projective.CP 2 => Phiinv i t b) = fun b =>
      (Gm.comp (gaugeDiagInv i b)).comp (W'.coordChange t (i, i) b) := by
    funext b; rw [Phiinv]
  rw [hfun]
  refine hmain.mono ?_
  intro b hb
  rw [baseSet_complexificationCore_zStd, baseSet_whitneySum] at hb
  exact hb

theorem Phi_htgt (i : Fin 3) (t t' : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (hb : b ∈ (complexificationCore zStd).baseSet i) (ht : b ∈ W'.baseSet t)
    (ht' : b ∈ W'.baseSet t') :
    (W'.coordChange t t' b).comp (Phi i t b) = Phi i t' b := by
  have hbi : b ∈ Work.Projective.chartSet i := mem_chartSet_of_mem_baseSet hb
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, Phi]
  exact whitneySum_coordChange_comp_apply (i, i) t t' (mem_baseSet_W'_of hbi) ht ht'
    ((gaugeDiag i b) (GmInv x))

theorem Phi_hsrc (i : Fin 3) (t : Fin 3 × Fin 3) (i' : Fin 3) (b : Work.Projective.CP 2)
    (hb : b ∈ (complexificationCore zStd).baseSet i)
    (hb' : b ∈ (complexificationCore zStd).baseSet i') (ht : b ∈ W'.baseSet t) :
    (Phi i t b).comp ((complexificationCore zStd).coordChange i' i b) = Phi i' t b := by
  have hbi : b ∈ Work.Projective.chartSet i := mem_chartSet_of_mem_baseSet hb
  have hbi' : b ∈ Work.Projective.chartSet i' := mem_chartSet_of_mem_baseSet hb'
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, Phi]
  rw [complexificationCore_coordChange_eq i' i b]
  simp only [ContinuousLinearMap.comp_apply]
  rw [GmInv_apply_Gm, gaugeDiag_cMat_apply i i' hbi hbi' (GmInv x),
    ← whitneySum_diag_coordChange_apply i i' hbi hbi' (gaugeDiag i' b (GmInv x))]
  exact whitneySum_coordChange_comp_apply (i', i') (i, i) t (mem_baseSet_W'_of hbi')
    (mem_baseSet_W'_of hbi) ht ((gaugeDiag i' b) (GmInv x))

theorem Phi_hleft (i : Fin 3) (i' : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (x : EuclideanSpace ℂ (Fin 2))
    (hb : b ∈ (complexificationCore zStd).baseSet i ∩ W'.baseSet i') :
    Phiinv i i' b (Phi i i' b x) = x := by
  have hbi : b ∈ Work.Projective.chartSet i := mem_chartSet_of_mem_baseSet hb.1
  simp only [Phi, Phiinv, ContinuousLinearMap.comp_apply]
  rw [whitneySum_coordChange_comp_apply (i, i) i' (i, i) (mem_baseSet_W'_of hbi) hb.2
    (mem_baseSet_W'_of hbi) ((gaugeDiag i b) (GmInv x))]
  rw [coordChange_self_W' i hbi, gaugeDiagInv_apply_gaugeDiag, Gm_apply_GmInv]

theorem Phi_hright (i : Fin 3) (i' : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (y : EuclideanSpace ℂ (Fin 2))
    (hb : b ∈ (complexificationCore zStd).baseSet i ∩ W'.baseSet i') :
    Phi i i' b (Phiinv i i' b y) = y := by
  have hbi : b ∈ Work.Projective.chartSet i := mem_chartSet_of_mem_baseSet hb.1
  simp only [Phi, Phiinv, ContinuousLinearMap.comp_apply]
  rw [GmInv_apply_Gm, gaugeDiag_apply_gaugeDiagInv,
    whitneySum_coordChange_comp_apply i' (i, i) i' hb.2 (mem_baseSet_W'_of hbi) hb.2 y,
    W'.coordChange_self i' b hb.2 y]

theorem Phi_htgtinv (i : Fin 3) (t t' : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (hb : b ∈ (complexificationCore zStd).baseSet i) (ht : b ∈ W'.baseSet t)
    (ht' : b ∈ W'.baseSet t') :
    (Phiinv i t b).comp (W'.coordChange t' t b) = Phiinv i t' b := by
  have hbi : b ∈ Work.Projective.chartSet i := mem_chartSet_of_mem_baseSet hb
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, Phiinv]
  rw [whitneySum_coordChange_comp_apply t' t (i, i) ht' ht (mem_baseSet_W'_of hbi) x]

theorem Phi_hsrcinv (i : Fin 3) (t : Fin 3 × Fin 3) (i' : Fin 3) (b : Work.Projective.CP 2)
    (hb : b ∈ (complexificationCore zStd).baseSet i)
    (hb' : b ∈ (complexificationCore zStd).baseSet i') (ht : b ∈ W'.baseSet t) :
    ((complexificationCore zStd).coordChange i i' b).comp (Phiinv i t b) = Phiinv i' t b := by
  have hC : ∀ y : EuclideanSpace ℂ (Fin 2),
      (Phi i' t b) y = (Phi i t b) (((complexificationCore zStd).coordChange i' i b) y) := by
    intro y
    have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F y)
      (Phi_hsrc i t i' b hb hb' ht)
    simpa only [ContinuousLinearMap.comp_apply] using h.symm
  have hcyc : ∀ z : EuclideanSpace ℂ (Fin 2),
      ((complexificationCore zStd).coordChange i' i b)
        (((complexificationCore zStd).coordChange i i' b) z) = z := by
    intro z
    rw [coordChange_comp_apply (complexificationCore zStd) i i' i hb hb' hb z,
      (complexificationCore zStd).coordChange_self i b hb z]
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  calc ((complexificationCore zStd).coordChange i i' b) ((Phiinv i t b) x)
      = (Phiinv i' t b) ((Phi i' t b)
          (((complexificationCore zStd).coordChange i i' b) ((Phiinv i t b) x))) := by
        rw [Phi_hleft i' t b _ ⟨hb', ht⟩]
    _ = (Phiinv i' t b) ((Phi i t b)
          (((complexificationCore zStd).coordChange i' i b)
            (((complexificationCore zStd).coordChange i i' b) ((Phiinv i t b) x)))) := by
        rw [hC]
    _ = (Phiinv i' t b) ((Phi i t b) ((Phiinv i t b) x)) := by
        rw [hcyc]
    _ = (Phiinv i' t b) x := by
        rw [Phi_hright i t b _ ⟨hb, ht⟩]

/-- **The isomorphism `zStd ⊗_ℝ ℂ ≅ O(1) ⊕ O(-1)`.** -/
theorem nonempty_complexificationCore_zStd_lineC :
    Nonempty (BundleIso (complexificationCore zStd) (W')) :=
  Work.Thom.nonempty_bundleIso_of_gauge (complexificationCore zStd) W' Phi Phiinv
    Phi_hcont Phiinv_hcont Phi_htgt Phi_hsrc Phi_htgtinv Phi_hsrcinv Phi_hleft Phi_hright

end

end Work.ThomBordism.Grassmann
