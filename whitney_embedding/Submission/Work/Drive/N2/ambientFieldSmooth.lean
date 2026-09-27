import Mathlib
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.ambientFieldAux

/-!
# Smoothness of the ambient model field

`modelField A φ β s₁ s₂` is smooth on the open set where the chart source is met, the retraction is
smooth, and the Gram determinant does not vanish.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- The chart coordinate is smooth at every point of `U` lying over the chart source. -/
lemma contDiffAt_uCoord_of_mem (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    {z : EuclideanSpace ℝ (Fin 5)} (hzU : z ∈ A.U) (hz : A.π z ∈ φ.source) (j : Fin 2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uCoord A φ j) z := by
  have hπ : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) A.π z :=
    A.hπ.contMDiffAt (A.hU.mem_nhds hzU)
  have hφz : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) (A.π z) :=
    hφ.contMDiffAt (φ.open_source.mem_nhds hz)
  have hcomp : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => φ (A.π w)) z := hφz.comp z hπ
  have h2 : ContMDiffAt (𝓡 5) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => φ (A.π w) j) z :=
    ((coordProj j).contMDiffAt.comp z hcomp)
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => φ (A.π w) j) z :=
    (contMDiffAt_iff_contDiffAt).mp h2
  show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => φ (A.π w) j) z
  exact h3

/-- The chart-coordinate vector `φ ∘ π` is smooth at every point of `U` over the chart source. -/
lemma contDiffAt_uVec_of_mem (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    {z : EuclideanSpace ℝ (Fin 5)} (hzU : z ∈ A.U) (hz : A.π z ∈ φ.source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => φ (A.π w)) z := by
  have hπ : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) A.π z :=
    A.hπ.contMDiffAt (A.hU.mem_nhds hzU)
  have hφz : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) (A.π z) :=
    hφ.contMDiffAt (φ.open_source.mem_nhds hz)
  have hcomp : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => φ (A.π w)) z := hφz.comp z hπ
  exact (contMDiffAt_iff_contDiffAt).mp hcomp

/-- The ambient gradient of a chart coordinate is smooth. -/
lemma contDiffAt_uGrad_of_mem (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    {z : EuclideanSpace ℝ (Fin 5)} (hzU : z ∈ A.U) (hz : A.π z ∈ φ.source) (j : Fin 2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uGrad A φ j) z := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => fderiv ℝ (uCoord A φ j) w) z :=
    (contDiffAt_uCoord_of_mem A φ hφ hzU hz j).fderiv_right (by simp)
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 5))).symm
        (fderiv ℝ (uCoord A φ j) w)) z :=
    (ContinuousLinearMap.contDiff
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 5))).symm.toContinuousLinearEquiv.toContinuousLinearMap)).contDiffAt.comp z h1
  exact h2

/-- The Gram determinant is smooth wherever the chart coordinates are. -/
lemma contDiffAt_gramDet_of_mem (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    {z : EuclideanSpace ℝ (Fin 5)} (hzU : z ∈ A.U) (hz : A.π z ∈ φ.source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gramDet A φ) z := by
  have h0 := contDiffAt_uGrad_of_mem A φ hφ hzU hz 0
  have h1 := contDiffAt_uGrad_of_mem A φ hφ hzU hz 1
  have h00 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ‖uGrad A φ 0 w‖ ^ 2) z := by
    have h := h0.inner ℝ h0
    simpa only [real_inner_self_eq_norm_sq] using h
  have h11 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ‖uGrad A φ 1 w‖ ^ 2) z := by
    have h := h1.inner ℝ h1
    simpa only [real_inner_self_eq_norm_sq] using h
  have h01 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => inner ℝ (uGrad A φ 0 w) (uGrad A φ 1 w)) z := h0.inner ℝ h1
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (inner ℝ (uGrad A φ 0 w) (uGrad A φ 1 w)) ^ 2) z := h01.pow 2
  show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z => ‖uGrad A φ 0 z‖ ^ 2 * ‖uGrad A φ 1 z‖ ^ 2
      - (inner ℝ (uGrad A φ 0 z) (uGrad A φ 1 z)) ^ 2) z
  exact h00.mul h11 |>.sub h2

/-- The raw least-squares field is smooth wherever the Gram determinant does not vanish. -/
lemma contDiffAt_modelRaw_of_mem (A : AmbSetup M)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (s₁ s₂ : ℝ)
    {z : EuclideanSpace ℝ (Fin 5)} (hzU : z ∈ A.U) (hz : A.π z ∈ φ.source)
    (hzdet : gramDet A φ z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modelRaw A φ β s₁ s₂) z := by
  have hdet := contDiffAt_gramDet_of_mem A φ hφ hzU hz
  have hinv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (gramDet A φ w)⁻¹) z :=
    hdet.inv hzdet
  have huvec := contDiffAt_uVec_of_mem A φ hφ hzU hz
  have hvel : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => chartVel β s₁ s₂ (φ (A.π w))) z :=
    (contDiff_chartVel hβ s₁ s₂).contDiffAt.comp z huvec
  have hg0 := contDiffAt_uGrad_of_mem A φ hφ hzU hz 0
  have hg1 := contDiffAt_uGrad_of_mem A φ hφ hzU hz 1
  show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (gramDet A φ z)⁻¹ •
    (((‖uGrad A φ 1 z‖ ^ 2 * chartVel β s₁ s₂ (φ (A.π z)) 0
        - inner ℝ (uGrad A φ 0 z) (uGrad A φ 1 z) * chartVel β s₁ s₂ (φ (A.π z)) 1) •
          uGrad A φ 0 z)
      + ((‖uGrad A φ 0 z‖ ^ 2 * chartVel β s₁ s₂ (φ (A.π z)) 1
        - inner ℝ (uGrad A φ 0 z) (uGrad A φ 1 z) * chartVel β s₁ s₂ (φ (A.π z)) 0) •
          uGrad A φ 1 z))) z
  have h01 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => inner ℝ (uGrad A φ 0 w) (uGrad A φ 1 w)) z :=
    (contDiffAt_uGrad_of_mem A φ hφ hzU hz 0).inner ℝ (contDiffAt_uGrad_of_mem A φ hφ hzU hz 1)
  have h00n : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ‖uGrad A φ 0 w‖ ^ 2) z := by
    have h := (contDiffAt_uGrad_of_mem A φ hφ hzU hz 0).inner ℝ
      (contDiffAt_uGrad_of_mem A φ hφ hzU hz 0)
    simpa only [real_inner_self_eq_norm_sq] using h
  have h11n : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ‖uGrad A φ 1 w‖ ^ 2) z := by
    have h := (contDiffAt_uGrad_of_mem A φ hφ hzU hz 1).inner ℝ
      (contDiffAt_uGrad_of_mem A φ hφ hzU hz 1)
    simpa only [real_inner_self_eq_norm_sq] using h
  have hvel0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => chartVel β s₁ s₂ (φ (A.π w)) 0) z :=
    ((coordProj 0).contDiff.contDiffAt).comp z hvel
  have hvel1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => chartVel β s₁ s₂ (φ (A.π w)) 1) z :=
    ((coordProj 1).contDiff.contDiffAt).comp z hvel
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ‖uGrad A φ 1 w‖ ^ 2 * chartVel β s₁ s₂ (φ (A.π w)) 0
        - inner ℝ (uGrad A φ 0 w) (uGrad A φ 1 w) * chartVel β s₁ s₂ (φ (A.π w)) 1) z :=
    (h11n.mul hvel0).sub (h01.mul hvel1)
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ‖uGrad A φ 0 w‖ ^ 2 * chartVel β s₁ s₂ (φ (A.π w)) 1
        - inner ℝ (uGrad A φ 0 w) (uGrad A φ 1 w) * chartVel β s₁ s₂ (φ (A.π w)) 0) z :=
    (h00n.mul hvel1).sub (h01.mul hvel0)
  exact hinv.smul ((hA.smul hg0).add (hB.smul hg1))

/-- The model field is smooth on the set where the chart source is met, the retraction is smooth
and the Gram determinant does not vanish. -/
theorem contDiffOn_modelField {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (A : AmbSetup M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat)
      (fun y => φ y) φ.source)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) β) (s₁ s₂ : ℝ) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (modelField A φ β s₁ s₂)
      (A.U ∩ {z : EuclideanSpace ℝ (Fin 5) | A.π z ∈ φ.source}
        ∩ {z : EuclideanSpace ℝ (Fin 5) | gramDet A φ z ≠ 0}) := by
  intro z hz
  obtain ⟨⟨hzU, hzsrc⟩, hzdet⟩ := hz
  have hE : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A.e (A.π w)) z := by
    have hπ : ContMDiffAt (𝓡 5) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) A.π z :=
      A.hπ.contMDiffAt (A.hU.mem_nhds hzU)
    have he : ContMDiffAt (𝓡 2) (𝓡 5) ((⊤ : ℕ∞) : WithTop ℕ∞) A.e (A.π z) := A.he.contMDiffAt
    exact (contMDiffAt_iff_contDiffAt).mp (he.comp z hπ)
  have hfd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => fderiv ℝ (fun w => A.e (A.π w)) w) z :=
    hE.fderiv_right (by simp)
  have hraw := contDiffAt_modelRaw_of_mem A φ hφ β hβ s₁ s₂ hzU hzsrc hzdet
  have hres : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (fderiv ℝ (fun w => A.e (A.π w)) z) (modelRaw A φ β s₁ s₂ z)) z :=
    hfd.clm_apply hraw
  exact hres.contDiffWithinAt

/-- The damped ambient maps are smooth. -/
theorem contDiff_damped_E_G {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (A : AmbSetup M)
    (χd : EuclideanSpace ℝ (Fin 5) → ℝ) (hχd : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) χd)
    (hχd_supp : tsupport χd ⊆ A.U)
    (f : M → ℝ) (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z => χd z • A.e (A.π z)) ∧
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z => χd z • f (A.π z)) := by
  have hE_U : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.e (A.π z)) A.U := by
    have h1 : ContMDiffOn (𝓡 5) (𝓡 5) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => A.e (A.π z)) A.U :=
      (A.he.contMDiffOn (s := Set.univ)).comp A.hπ (fun z _ => Set.mem_univ _)
    exact (contMDiffOn_iff_contDiffOn).mp h1
  have hG_U : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f (A.π z)) A.U := by
    have h1 : ContMDiffOn (𝓡 5) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => f (A.π z)) A.U :=
      (hf.contMDiffOn (s := Set.univ)).comp A.hπ (fun z _ => Set.mem_univ _)
    exact (contMDiffOn_iff_contDiffOn).mp h1
  exact ⟨contDiff_smul_of_contDiffOn_aux A.hU hχd hE_U hχd_supp,
    contDiff_smul_of_contDiffOn_aux A.hU hχd hG_U hχd_supp⟩

end Work.Drive.N2
