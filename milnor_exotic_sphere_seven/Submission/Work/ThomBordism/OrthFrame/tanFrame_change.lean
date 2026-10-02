import Mathlib
import Submission.Work.ThomBordism.OrthFrame.FrameAlgebra
import Submission.Work.ThomBordism.PontryaginThom.FramesRange

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The change of the chart tangent frame between two charts

`Work.ThomBordism.tanFrame E i x` is the chart tangent frame of the embedding `E` in the chart
`coverChart i` at `x` (the columns of the derivative of the chart representative `E.e ∘ (i).symm`
at the chart coordinates of `x`, `Work.ThomBordism.PontryaginThom.frame`).  On the overlap of the
base sets of two indices `i`, `j`, the two frames are related by the matrix `C` of the derivative
of the **chart change** `y ↦ (coverChart j) (coverChart i).symm y` in the standard basis, and the
determinant of that matrix is the determinant of that linear map.

This is the chain rule `fderiv_chartRep_eq` of `FramesRange.lean`, read in the standard basis
`stdBasis8` of `Euc 8`, together with the invertibility of the chart change (its reverse chart
change is a left inverse, so the derivative is injective, hence — in finite dimension — the
determinant does not vanish).
-/

namespace Work.ThomBordism.OrthFrame

open Work.ThomBordism Work.ThomBordism.PontryaginThom
open scoped Manifold ContDiff BigOperators
open Filter

noncomputable section

/-- The standard orthonormal basis of `Euc 8`, as a `Module.Basis`. -/
abbrev stdBasis8 : Module.Basis (Fin 8) ℝ (Euc 8) := (EuclideanSpace.basisFun (Fin 8) ℝ).toBasis

/-- The standard basis vector `stdBasis8 i` is `EuclideanSpace.single i 1`. -/
@[simp] theorem stdBasis8_apply (i : Fin 8) : stdBasis8 i = EuclideanSpace.single i 1 := by
  simp only [stdBasis8, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

/-- **The expansion of a continuous linear map of `Euc 8` in the standard basis**: the matrix of
`L` in the standard basis expands `L (single a 1)` in the standard basis. -/
theorem clm_expand_basis (L : Euc 8 →L[ℝ] Euc 8) (a : Fin 8) :
    L (EuclideanSpace.single a 1)
      = ∑ a', (LinearMap.toMatrix stdBasis8 stdBasis8 (ContinuousLinearMap.toLinearMap L)) a' a
          • EuclideanSpace.single a' 1 := by
  rw [← Module.Basis.sum_repr stdBasis8 (L (EuclideanSpace.single a 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.toMatrix_apply, stdBasis8_apply, stdBasis8_apply]
  rfl

/-- **The change of the chart tangent frame between two charts** of the normal data of an embedding
`E : V ↪ ℝ^{8+k}`: on the overlap of the base sets of the indices `i`, `j`, the frame of `i` is
obtained from the frame of `j` by the matrix `C` of the derivative of the chart change
`y ↦ (coverChart j) (coverChart i).symm y` in the standard basis of `Euc 8`, whose determinant is
`LinearMap.det` of that derivative and is nonzero (the chart change is a diffeomorphism). -/
theorem tanFrame_change {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i j : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hi : x ∈ ND.D.baseSet i) (hj : x ∈ ND.D.baseSet j) :
    ∃ C : Matrix (Fin 8) (Fin 8) ℝ,
      (∀ a : Fin 8, Work.ThomBordism.tanFrame E i x a =
        ∑ a', C a' a • Work.ThomBordism.tanFrame E j x a') ∧
      (C.det ≠ 0) ∧
      (C.det = LinearMap.det (ContinuousLinearMap.toLinearMap (fderiv ℝ
        (fun y => (Work.ThomBordism.PontryaginThom.coverChart j).1
          ((Work.ThomBordism.PontryaginThom.coverChart i).1.symm y))
        ((Work.ThomBordism.PontryaginThom.coverChart i).1 x)))) := by
  classical
  have hi_src : x ∈ (coverChart i).1.source := ND.baseSet_sub i.1 i.2 x hi
  have hj_src : x ∈ (coverChart j).1.source := ND.baseSet_sub j.1 j.2 x hj
  have hdiffφ : DifferentiableAt ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
      ((coverChart i).1 x) := differentiableAt_chartChange (coverChart i) (coverChart j) hi_src hj_src
  have hdiffψ : DifferentiableAt ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y))
      ((coverChart j).1 x) := differentiableAt_chartChange (coverChart j) (coverChart i) hj_src hi_src
  have hφei : (fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x)
      = (coverChart j).1 x := by
    show (coverChart j).1 ((coverChart i).1.symm ((coverChart i).1 x)) = (coverChart j).1 x
    rw [(coverChart i).1.left_inv hi_src]
  -- the reverse chart change is a left inverse of the chart change near `(coverChart i) x`
  have heq : (fun y => (coverChart i).1 ((coverChart j).1.symm y)) ∘
      (fun y => (coverChart j).1 ((coverChart i).1.symm y)) =ᶠ[nhds ((coverChart i).1 x)] id := by
    have hcont : ContinuousAt (coverChart i).1.symm ((coverChart i).1 x) :=
      (coverChart i).1.continuousOn_symm.continuousWithinAt
        ((coverChart i).1.map_source hi_src) |>.continuousAt
        ((coverChart i).1.open_target.mem_nhds ((coverChart i).1.map_source hi_src))
    have hmem : (coverChart i).1.symm ((coverChart i).1 x) ∈ (coverChart j).1.source := by
      rw [(coverChart i).1.left_inv hi_src]; exact hj_src
    filter_upwards [((coverChart i).1.open_target).mem_nhds ((coverChart i).1.map_source hi_src),
      hcont.preimage_mem_nhds ((coverChart j).1.open_source.mem_nhds hmem)] with y hy hyj
    show (coverChart i).1 ((coverChart j).1.symm ((coverChart j).1 ((coverChart i).1.symm y))) = y
    rw [(coverChart j).1.left_inv hyj, (coverChart i).1.right_inv hy]
  refine ⟨LinearMap.toMatrix stdBasis8 stdBasis8 (ContinuousLinearMap.toLinearMap (fderiv ℝ
      (fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x))), ?_, ?_, ?_⟩
  · -- the chain rule, read in the standard basis
    intro a
    have hchain := fderiv_chartRep_eq (E.e) (embedding_contMDiff E) (coverChart i) (coverChart j)
      hi_src hj_src
    show fderiv ℝ (chartRep E.e (coverChart i)) ((coverChart i).1 x)
        (EuclideanSpace.single a 1) = _
    rw [hchain, ContinuousLinearMap.comp_apply]
    rw [clm_expand_basis (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
      ((coverChart i).1 x)) a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [map_smul]
    rfl
  · -- the chart change is invertible, so the determinant does not vanish
    rw [LinearMap.det_toMatrix]
    have hdψ' : DifferentiableAt ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y))
        ((fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x)) :=
      hφei ▸ hdiffψ
    have h1 : fderiv ℝ ((fun y => (coverChart i).1 ((coverChart j).1.symm y)) ∘
        (fun y => (coverChart j).1 ((coverChart i).1.symm y))) ((coverChart i).1 x)
        = (fderiv ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y)) ((coverChart j).1 x)).comp
          (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x)) :=
      hφei ▸ fderiv_comp ((coverChart i).1 x) hdψ' hdiffφ
    have h2 : fderiv ℝ ((fun y => (coverChart i).1 ((coverChart j).1.symm y)) ∘
        (fun y => (coverChart j).1 ((coverChart i).1.symm y))) ((coverChart i).1 x)
        = ContinuousLinearMap.id ℝ (Euc 8) := by
      rw [heq.fderiv_eq, fderiv_id]
    have hcomp :
        (fderiv ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y))
            ((coverChart j).1 x)).comp
          (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
            ((coverChart i).1 x))
        = ContinuousLinearMap.id ℝ (Euc 8) := h1.symm.trans h2
    have hinj : Function.Injective
        (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x)) := by
      intro u v huv
      have hu := congrArg (fun (F : Euc 8 →L[ℝ] Euc 8) => F u) hcomp
      have hv := congrArg (fun (F : Euc 8 →L[ℝ] Euc 8) => F v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu hv
      rw [← hu, huv, hv]
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    refine h0 ?_
    rw [LinearMap.ker_eq_bot]
    exact hinj
  · -- the determinant of the matrix is the determinant of the linear map
    exact LinearMap.det_toMatrix stdBasis8 (ContinuousLinearMap.toLinearMap (fderiv ℝ
      (fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x)))

end

end Work.ThomBordism.OrthFrame
