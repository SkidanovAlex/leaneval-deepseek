import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.Grassmann.eOfOriented

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The coframing `ellOf i` is positively oriented for the frame `ogFrameCLM (Γ y)`

On the member `cfGoodSet Γ i` of the coframing cover, the frame `ogFrameCLM (Γ y)` of the oriented
plane `Γ y` (the `Classical.choice` representative `Quotient.out (Γ y)`) has `S`-matrix
`frameMatrix S (Quotient.out (Γ y))` whose determinant has sign `cfSignOf i.2`
(`frameSign_eq_of_mem_goodSet`, `frameMatrix_det_eq_sign`).  Consequently the sign-corrected
coordinate reading `ellOf i ∘ ogFrameCLM (Γ y)` — the fixed left inverse `ellOf i` of the
sign-corrected parametrisation, composed with the frame — has matrix
`cfSignMat (cfSignOf i.2) * frameMatrix S (Quotient.out (Γ y))`, whose determinant is
`cfSignOf i.2 · det (frameMatrix S ·) = |det (frameMatrix S ·)| > 0`.

This is the positivity half of the coframing dictionary: `eOfOriented` proves the same statement for
the *inverse* product `(frameMatrix S f)⁻¹ * cfSignMat ε` (the matrix of the coframing `eOf Γ i y`
in the frame `f`); here we prove it for the product that actually computes
`ellOf i ∘ ogFrameCLM`.
-/

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

/-- The frame map of an oriented plane is the linear expansion in the representative frame. -/
theorem det_aux_ogFrameCLM_apply {k m : ℕ} (Γ : OG k m) (v : Amb k) :
    LeadChapter.ogFrameCLM Γ v = ∑ a : Fin k, v a • (Quotient.out Γ).1 a := by
  rw [LeadChapter.ogFrameCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

/-- **Reading the frame `ogFrameCLM Γ` in the coordinates of the chart `S`** gives exactly the
matrix `frameMatrix S (Quotient.out Γ)`. -/
theorem det_aux_coordProjCLM_ogFrameCLM {k m : ℕ} (S : ChartIdx k m) (Γ : OG k m) (v : Amb k) :
    coordProjCLM S (LeadChapter.ogFrameCLM Γ v)
      = matLin (frameMatrix S (Quotient.out Γ).1) v := by
  have hsingle : ∀ a : Fin k, coordProjCLM S ((Quotient.out Γ).1 a)
      = matLin (frameMatrix S (Quotient.out Γ).1) (EuclideanSpace.single a 1) := by
    intro a
    rw [coordProjCLM_apply, coordProj_frame, matLin_apply, PiLp.ofLp_single]
  rw [det_aux_ogFrameCLM_apply, map_sum]
  simp only [map_smul]
  have hx : v = ∑ a : Fin k, v a • EuclideanSpace.single a 1 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr v]
    exact Finset.sum_congr rfl (fun a _ => by
      rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply])
  conv_rhs => rw [hx]
  rw [map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl (fun a _ => by rw [hsingle a])

/-- **The matrix of the composed map `ellOf i ∘ ogFrameCLM Γ`** is the sign-corrected frame matrix
`cfSignMat (cfSignOf i.2) * frameMatrix i.1 (Quotient.out Γ)`. -/
theorem det_aux_ellOf_comp_ogFrameCLM {k m : ℕ} (i : ChartIdx k m × Bool) (Γ : OG k m) :
    (ellOf i).comp (LeadChapter.ogFrameCLM Γ)
      = matLin (cfSignMat (cfSignOf i.2) * frameMatrix i.1 (Quotient.out Γ).1) := by
  rw [ellOf, ContinuousLinearMap.comp_assoc]
  ext v : 1
  show signCLM (cfSignOf i.2) (coordProjCLM i.1 (LeadChapter.ogFrameCLM Γ v))
    = (matLin (cfSignMat (cfSignOf i.2) * frameMatrix i.1 (Quotient.out Γ).1)) v
  rw [det_aux_coordProjCLM_ogFrameCLM i.1 Γ v, signCLM_apply, matLin_mul]
  rfl

theorem det_ellOf_ogFrameCLM_pos {k m : ℕ} {M : Type} [TopologicalSpace M]
    {Γ : M → Work.ThomBordism.Grassmann.OG k m}
    {i : Work.ThomBordism.Grassmann.ChartIdx k m × Bool} {y : M}
    (hy : y ∈ Work.ThomBordism.Grassmann.cfGoodSet Γ i) :
    0 < LinearMap.det ((Work.ThomBordism.Grassmann.ellOf i).comp
      (Work.ThomBordism.LeadChapter.ogFrameCLM (Γ y))).toLinearMap := by
  have hmk : Quotient.mk'' (Quotient.out (Γ y)) = Γ y := Quotient.out_eq (Γ y)
  have hbase : Quotient.mk'' (Quotient.out (Γ y)) ∈ baseSet i.1 := by
    rw [hmk]; exact hy.1
  have hfS : Quotient.out (Γ y) ∈ chartSet i.1 :=
    (mem_baseSet_iff i.1 (Quotient.out (Γ y))).mp hbase
  have hdet : (frameMatrix i.1 (Quotient.out (Γ y)).1).det
      = cfSignOf i.2 * |(frameMatrix i.1 (Quotient.out (Γ y)).1).det| := by
    have h := frameMatrix_det_eq_sign i.1 (Quotient.out (Γ y)) hfS
    rw [hmk, frameSign_eq_of_mem_goodSet hy] at h
    exact h
  rw [det_aux_ellOf_comp_ogFrameCLM i (Γ y), det_matLin, Matrix.det_mul,
    signMat_eq_orientMat (S := i.1) (x := Γ y) (ε := cfSignOf i.2)
      (frameSign_eq_of_mem_goodSet hy),
    orientMat_det, frameSign_eq_of_mem_goodSet hy, hdet, ← mul_assoc, signOf_mul_self, one_mul]
  exact abs_pos.mpr ((mem_chartSet i.1 (Quotient.out (Γ y))).mp hfS)

end

end Work.ThomBordism
