import Mathlib
import Submission.Work.ThomBordism._gtd.P4
import Submission.Work.ThomBordism.gtdFrameProj_padEuc
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.PTGeometric.PadAmb
import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.Tubular.Gauss
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.tautTotalMap
import Submission.Work.ThomBordism.onePointExtensionTaut

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-! ## Helper lemmas for the (plane, vector) model -/

/-- The inverse of the Euclidean normal homeomorphism is the "read the vector in the frame of the
base point" map, which is its definition. -/
theorem gtdEucNormalHomeomorph_symm_apply {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (z : Work.Tubular.NormalTotal E) :
    (Work.Tubular.eucNormalHomeomorph E ND).symm z = Work.Tubular.normalToBundle E ND z := by
  have hz : (Work.Tubular.eucNormalHomeomorph E ND) (Work.Tubular.normalToBundle E ND z) = z := by
    rw [Work.Tubular.eucNormalHomeomorph_apply]
    exact Work.Tubular.bundleToNormal_normalToBundle E ND z
  calc (Work.Tubular.eucNormalHomeomorph E ND).symm z
      = (Work.Tubular.eucNormalHomeomorph E ND).symm
          ((Work.Tubular.eucNormalHomeomorph E ND) (Work.Tubular.normalToBundle E ND z)) := by
        rw [hz]
    _ = Work.Tubular.normalToBundle E ND z :=
        (Work.Tubular.eucNormalHomeomorph E ND).symm_apply_apply _

/-- The evaluation of a point of the tautological bundle vanishes as soon as its fibre coordinate
does. -/
theorem gtdEvalVec_eq_zero_of_snd_eq_zero {k m : ℕ}
    (p : (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace)
    (h : (show Work.ThomBordism.Grassmann.Amb k from p.2) = 0) :
    Work.ThomBordism.Grassmann.evalVec p = 0 := by
  set S := (Work.ThomBordism.Grassmann.tautologicalBundle k m).indexAt p.1 with hS
  have hpS : p.1 ∈ (Work.ThomBordism.Grassmann.tautologicalBundle k m).baseSet S :=
    (Work.ThomBordism.Grassmann.tautologicalBundle k m).mem_baseSet_at p.1
  rw [Work.ThomBordism.Grassmann.evalVec_apply_chart p S hpS, VectorBundleCore.localTriv_apply]
  have h2 : (Work.ThomBordism.Grassmann.tautologicalBundle k m).coordChange
      ((Work.ThomBordism.Grassmann.tautologicalBundle k m).indexAt p.1) S p.1
      (show Work.ThomBordism.Grassmann.Amb k from p.2) = 0 := by
    rw [h]
    exact map_zero _
  rw [h2, Work.ThomBordism.Grassmann.peEvalChartO_zero]

/-- **The padded normal vector is a vector of the padded Gauss plane.**  With the padded Gauss map
`padGaussFun E ND` of the normal data, the `padEuc`-image of the inserted normal vector of a point of
the Euclidean normal bundle lies in the plane `padGaussFun E ND p.1`. -/
theorem gtdMemPlane_padGaussEval {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (p : (Work.Tubular.normalBundle E ND).TotalSpace) :
    Work.ThomBordism.Grassmann.memPlane (Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (Work.PTGeometric.padEuc k 10 (by norm_num)
        (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))) := by
  rw [← Work.PTGeometric.projOfPlane_fixed_iff]
  rw [Work.ThomBordism.Grassmann.projOfPlane_padGauss, Work.PTGeometric.padEndEuc_apply_padEuc]
  have hv : Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p) ∈
      Work.Tubular.normalSpace E p.1 := (Work.Tubular.bundleToNormal E ND p).2
  have hfix : (((Work.Tubular.normalSpace E p.1).subtypeL).comp
        ((Work.Tubular.normalSpace E p.1).orthogonalProjectionOnto))
      (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))
      = Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p) := by
    have h := congrArg (Work.Tubular.normalSpace E p.1).subtypeL
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
        (K := Work.Tubular.normalSpace E p.1)
        (v := (⟨Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p), hv⟩ :
          Work.Tubular.normalSpace E p.1)))
    rw [ContinuousLinearMap.comp_apply]
    exact h
  rw [hfix]

/-- The Gauss/classifying map of the normal bundle, in the (plane, vector) model: there is a
continuous map of the normal bundle into the tautological bundle over `G̃r_k(ℝ^{k+10})` whose plane
is the padded Gauss plane and whose vector is the padded normal coordinate, and whose one-point
extension satisfies the coordinate (fibrewise) condition of the Pontryagin–Thom construction. -/
theorem gtdGaussCandidate {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    {ε : ℝ} (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε)
    (q : Work.Tubular.NormalSphSub E ε) (hU : IsCompact C.U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) :
    ∃ G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace),
      (∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1) ∧
      (∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))) ∧
      (∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement
            (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) ∧
      (∃ (J : C(OnePoint (Work.Tubular.normalBundle E ND).TotalSpace,
            OnePoint (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
          (hJ : ∀ p, J (OnePoint.some p) = OnePoint.some (G p))
          (hJinf : J OnePoint.infty = OnePoint.infty),
        ∀ y ∈ C.openTube, ∃ p : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace,
          (J.comp ↑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
              (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = OnePoint.some p ∧
          Work.PTGeometric.projOfPlane k 10
              ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p)
            = Work.PTGeometric.padEndEuc k 10 (by norm_num)
                (Work.PTGeometric.tubeNormalProj E C y) ∧
          Work.ThomBordism.Grassmann.evalVec p = Work.PTGeometric.padEuc k 10 (by norm_num)
            ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2)) := by
  classical
  -- the plane field and the vector field on the total space of the Euclidean normal bundle
  let P : C((Work.Tubular.normalBundle E ND).TotalSpace, Work.ThomBordism.Grassmann.OG k 10) :=
    ⟨fun p => Work.ThomBordism.Grassmann.padGaussFun E ND p.1,
      (Work.ThomBordism.Grassmann.continuous_padGaussFun E ND).comp
        (Work.TangentClasses.RealBundle.continuous_proj (Work.Tubular.normalBundle E ND))⟩
  let W : C((Work.Tubular.normalBundle E ND).TotalSpace,
      Work.ThomBordism.Grassmann.Amb (k + 10)) :=
    ⟨fun p => Work.PTGeometric.padEuc k 10 (by norm_num)
        (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)),
      (Work.PTGeometric.padEuc k 10 (by norm_num)).continuous.comp
        ((Work.Tubular.NormalTotal.continuous_vec E).comp
          (Work.Tubular.continuous_bundleToNormal E ND))⟩
  obtain ⟨G, hGproj, hGeval⟩ :=
    Work.ThomBordism.Grassmann.tautTotalMap P W (fun p => gtdMemPlane_padGaussEval E ND p)
  have hproj : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1 := fun p => hGproj p
  have heval : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)) := fun p => hGeval p
  have hzero : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10) := by
    intro p hp
    rw [Work.Thom.mem_zeroComplement] at hp ⊢
    intro h0
    have h1 : Work.ThomBordism.Grassmann.evalVec (G p) = 0 :=
      gtdEvalVec_eq_zero_of_snd_eq_zero (G p) h0
    rw [heval p] at h1
    have h2 : Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p) = 0 := by
      refine Work.PTGeometric.padEuc_injective k 10 (by norm_num) ?_
      rw [map_zero]
      exact h1
    have h3 : Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND) p = 0 := by
      rw [Work.Tubular.fibreNorm_eq_normalNorm]
      show ‖Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)‖ = 0
      rw [h2, norm_zero]
    exact hp (norm_eq_zero.mp (by simpa [Work.Thom.fibreNorm] using h3))
  obtain ⟨J, hJ, hJinf⟩ := Work.ThomBordism.onePointExtensionTaut E ND G heval
  refine ⟨G, hproj, heval, hzero, J, hJ, hJinf, ?_⟩
  intro y hy
  refine ⟨G (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y))),
    ?_, ?_, ?_⟩
  · change J ((⇑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
        (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))))
      = OnePoint.some (G (Work.Tubular.normalToBundle E ND
          (Work.Tubular.normalBlowUp E ε (C.inv y))))
    rw [Homeomorph.onePointCongr_symm_apply, OnePoint.map_some,
      gtdEucNormalHomeomorph_symm_apply E ND, hJ]
  · rw [hproj]
    exact Work.ThomBordism.Grassmann.projOfPlane_padGauss E ND (Work.PTGeometric.tubeFoot E C y)
  · rw [heval, Work.Tubular.bundleToNormal_normalToBundle]
    rfl


end Work.ThomBordism
