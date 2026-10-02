import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Oriented
import Submission.Work.ThomBordism.Grassmann.Smooth.gramSchmidtContinuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the graph charts

The graph point `graphPoint S`, the sign gauge `signMat S` and the two oriented points
`posPoint S`, `negPoint S` depend continuously on their arguments.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Topology
open Set

noncomputable section

variable {k m : ℕ}

/-! ## The graph frame -/

theorem continuous_graphVec (S : ChartIdx k m) (i : Fin k) :
    Continuous fun d : Amb k →L[ℝ] Amb m => graphVec S d i := by
  have h : (fun d : Amb k →L[ℝ] Amb m => graphVec S d i)
      = fun d => inclS S (EuclideanSpace.single i 1)
          + inclC S (d (EuclideanSpace.single i 1)) := by
    funext d; rw [graphVec, graphMap_apply]
  rw [h]
  fun_prop

theorem continuous_graphFrame (S : ChartIdx k m) : Continuous (graphFrame S) := by
  refine continuous_pi fun i => ?_
  have h : (fun d : Amb k →L[ℝ] Amb m => graphFrame S d i)
      = fun d => InnerProductSpace.gramSchmidtNormed ℝ (graphVec S d) i := by
    funext d; rw [graphFrame]
  rw [h]
  exact gramSchmidtContinuous (fun d : Amb k →L[ℝ] Amb m => graphVec S d)
    (continuous_graphVec S) (fun d => linearIndependent_graphVec S d) i

theorem continuous_graphPoint (S : ChartIdx k m) : Continuous (graphPoint S) := by
  have h : graphPoint S = fun d : Amb k →L[ℝ] Amb m =>
      Quotient.mk'' (⟨graphFrame S d, orthonormal_graphFrame S d⟩ : Stiefel k m) := by
    funext d; rw [graphPoint]
  rw [h]
  exact continuous_quotient_mk'.comp
    (Continuous.subtype_mk (continuous_graphFrame S) (fun d => orthonormal_graphFrame S d))

/-! ## The entries of the sign gauge -/

theorem continuous_frameMatrix_graphFrame (S : ChartIdx k m) :
    Continuous fun d : Amb k →L[ℝ] Amb m => frameMatrix S (graphFrame S d) :=
  (continuous_frameMatrix S).comp (Continuous.subtype_mk (continuous_graphFrame S)
    (fun d => orthonormal_graphFrame S d))

theorem continuous_frameMatrix_det_graphFrame (S : ChartIdx k m) :
    Continuous fun d : Amb k →L[ℝ] Amb m => (frameMatrix S (graphFrame S d)).det :=
  (continuous_matrix_det (k := k)).comp (continuous_frameMatrix_graphFrame S)

theorem signMat_apply (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) (i j : Fin k) :
    signMat S d i j = if i = j then
      (if (i : ℕ) = 0 then (frameMatrix S (graphFrame S d)).det
        / |(frameMatrix S (graphFrame S d)).det| else 1) else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [signMat, Matrix.diagonal_apply_eq, if_pos rfl]
  · rw [signMat, Matrix.diagonal_apply_ne _ hij, if_neg hij]

theorem continuous_signMat (S : ChartIdx k m) : Continuous (signMat S) := by
  refine continuous_matrix fun i j => ?_
  have h : (fun d : Amb k →L[ℝ] Amb m => signMat S d i j) = fun d =>
      if i = j then (if (i : ℕ) = 0 then (frameMatrix S (graphFrame S d)).det
        / |(frameMatrix S (graphFrame S d)).det| else 1) else 0 := by
    funext d; rw [signMat_apply]
  rw [h]
  by_cases hij : i = j
  · have h2 : (fun d : Amb k →L[ℝ] Amb m => if i = j then
        (if (i : ℕ) = 0 then (frameMatrix S (graphFrame S d)).det
          / |(frameMatrix S (graphFrame S d)).det| else 1) else 0)
        = fun d => (if (i : ℕ) = 0 then (frameMatrix S (graphFrame S d)).det
          / |(frameMatrix S (graphFrame S d)).det| else 1) := by
      funext d; rw [if_pos hij]
    rw [h2]
    by_cases hi : (i : ℕ) = 0
    · have h3 : (fun d : Amb k →L[ℝ] Amb m => if (i : ℕ) = 0 then
          (frameMatrix S (graphFrame S d)).det / |(frameMatrix S (graphFrame S d)).det|
          else 1) = fun d => (frameMatrix S (graphFrame S d)).det
            / |(frameMatrix S (graphFrame S d)).det| := by
        funext d; rw [if_pos hi]
      rw [h3]
      exact (continuous_frameMatrix_det_graphFrame S).div
        (continuous_frameMatrix_det_graphFrame S).abs
        (fun d => abs_ne_zero.mpr (graphFrame_det_ne_zero S d))
    · have h3 : (fun d : Amb k →L[ℝ] Amb m => if (i : ℕ) = 0 then
          (frameMatrix S (graphFrame S d)).det / |(frameMatrix S (graphFrame S d)).det|
          else 1) = fun _ => (1 : ℝ) := by
        funext d; rw [if_neg hi]
      rw [h3]; exact continuous_const
  · have h2 : (fun d : Amb k →L[ℝ] Amb m => if i = j then
        (if (i : ℕ) = 0 then (frameMatrix S (graphFrame S d)).det
          / |(frameMatrix S (graphFrame S d)).det| else 1) else 0) = fun _ => (0 : ℝ) := by
      funext d; rw [if_neg hij]
    rw [h2]; exact continuous_const

/-! ## The correction matrix of the negative chart -/

theorem flipMat_mul_signMat_apply (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) (a b : Fin k) :
    (flipMat k * signMat S d) a b = if a = b then
      (if (a : ℕ) = 0 then -((frameMatrix S (graphFrame S d)).det
        / |(frameMatrix S (graphFrame S d)).det|) else 1) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hab : a = b
  · subst hab
    rw [Finset.sum_eq_single a]
    · rw [signMat_apply, flipMat, Matrix.diagonal_apply_eq]
      split_ifs <;> ring
    · intro b _ hb
      rw [flipMat, Matrix.diagonal_apply_ne _ (Ne.symm hb)]; simp
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Finset.sum_eq_single a]
    · simp only [signMat_apply, if_neg hab, mul_zero]
    · intro b _ hb
      rw [flipMat, Matrix.diagonal_apply_ne _ (fun h => hb h.symm)]; simp
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

theorem continuous_flipMat_mul_signMat (S : ChartIdx k m) :
    Continuous (fun d : Amb k →L[ℝ] Amb m => flipMat k * signMat S d) := by
  refine continuous_matrix fun a b => ?_
  have h : (fun d : Amb k →L[ℝ] Amb m => (flipMat k * signMat S d) a b) = fun d =>
      if a = b then (if (a : ℕ) = 0 then -((frameMatrix S (graphFrame S d)).det
        / |(frameMatrix S (graphFrame S d)).det|) else 1) else 0 := by
    funext d; rw [flipMat_mul_signMat_apply]
  rw [h]
  by_cases hab : a = b
  · have h2 : (fun d : Amb k →L[ℝ] Amb m => if a = b then
        (if (a : ℕ) = 0 then -((frameMatrix S (graphFrame S d)).det
          / |(frameMatrix S (graphFrame S d)).det|) else 1) else 0)
        = fun d => (if (a : ℕ) = 0 then -((frameMatrix S (graphFrame S d)).det
          / |(frameMatrix S (graphFrame S d)).det|) else 1) := by
      funext d; rw [if_pos hab]
    rw [h2]
    by_cases ha : (a : ℕ) = 0
    · have h3 : (fun d : Amb k →L[ℝ] Amb m => if (a : ℕ) = 0 then
          -((frameMatrix S (graphFrame S d)).det / |(frameMatrix S (graphFrame S d)).det|)
          else 1) = fun d => -((frameMatrix S (graphFrame S d)).det
            / |(frameMatrix S (graphFrame S d)).det|) := by
        funext d; rw [if_pos ha]
      rw [h3]
      exact (((continuous_frameMatrix_det_graphFrame S).div
        (continuous_frameMatrix_det_graphFrame S).abs
        (fun d => abs_ne_zero.mpr (graphFrame_det_ne_zero S d)))).neg
    · have h3 : (fun d : Amb k →L[ℝ] Amb m => if (a : ℕ) = 0 then
          -((frameMatrix S (graphFrame S d)).det / |(frameMatrix S (graphFrame S d)).det|)
          else 1) = fun _ => (1 : ℝ) := by
        funext d; rw [if_neg ha]
      rw [h3]; exact continuous_const
  · have h2 : (fun d : Amb k →L[ℝ] Amb m => if a = b then
        (if (a : ℕ) = 0 then -((frameMatrix S (graphFrame S d)).det
          / |(frameMatrix S (graphFrame S d)).det|) else 1) else 0) = fun _ => (0 : ℝ) := by
      funext d; rw [if_neg hab]
    rw [h2]; exact continuous_const

/-! ## The two corrected frames and points -/

theorem continuous_posFrame (S : ChartIdx k m) : Continuous (posFrame S) := by
  refine continuous_pi fun i => ?_
  have h : (fun d : Amb k →L[ℝ] Amb m => posFrame S d i)
      = fun d => ∑ j, signMat S d j i • graphFrame S d j := by
    funext d; rw [posFrame, soActFun]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun d : Amb k →L[ℝ] Amb m => signMat S d j i :=
    (continuous_apply i).comp ((continuous_apply j).comp (continuous_signMat S))
  have h2 : Continuous fun d : Amb k →L[ℝ] Amb m => graphFrame S d j :=
    (continuous_apply j).comp (continuous_graphFrame S)
  exact h1.smul h2

theorem continuous_negFrame (S : ChartIdx k m) : Continuous (negFrame S) := by
  refine continuous_pi fun i => ?_
  have h : (fun d : Amb k →L[ℝ] Amb m => negFrame S d i)
      = fun d => ∑ j, (flipMat k * signMat S d) j i • graphFrame S d j := by
    funext d; rw [negFrame, soActFun]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun d : Amb k →L[ℝ] Amb m => (flipMat k * signMat S d) j i :=
    (continuous_apply i).comp ((continuous_apply j).comp (continuous_flipMat_mul_signMat S))
  have h2 : Continuous fun d : Amb k →L[ℝ] Amb m => graphFrame S d j :=
    (continuous_apply j).comp (continuous_graphFrame S)
  exact h1.smul h2

theorem continuous_posPoint (S : ChartIdx k m) : Continuous (posPoint S) := by
  have h : posPoint S = fun d : Amb k →L[ℝ] Amb m =>
      Quotient.mk'' (⟨posFrame S d,
        orthonormal_soActFun (signMat_transpose_mul_self S d) (orthonormal_graphFrame S d)⟩ :
          Stiefel k m) := by
    funext d; rw [posPoint]
  rw [h]
  exact continuous_quotient_mk'.comp (Continuous.subtype_mk (continuous_posFrame S) _)

theorem continuous_negPoint (S : ChartIdx k m) : Continuous (negPoint S) := by
  have h : negPoint S = fun d : Amb k →L[ℝ] Amb m =>
      Quotient.mk'' (⟨negFrame S d,
        orthonormal_soActFun (flipMat_signMat_transpose_mul_self S d)
          (orthonormal_graphFrame S d)⟩ : Stiefel k m) := by
    funext d; rw [negPoint]
  rw [h]
  exact continuous_quotient_mk'.comp (Continuous.subtype_mk (continuous_negFrame S) _)

/-! ## Continuity of the chart data -/

theorem continuousOn_chartFun (S : ChartIdx k m) : ContinuousOn (chartFun S) (chartSet S) := by
  have hvec : ∀ i : Fin k,
      ContinuousOn (fun f : Stiefel k m => coordVecFun S f.1 i) (chartSet S) :=
    fun i => (continuousOn_coordVec S i).congr (fun f _ => (coordVecFun_stiefel S f i).symm)
  have hclm : ContinuousOn (fun f : Stiefel k m => coordEvalCLM S f.1) (chartSet S) := by
    rw [show (fun f : Stiefel k m => coordEvalCLM S f.1)
        = fun f => ∑ i : Fin k,
            (ContinuousLinearMap.smulRightL ℝ (Amb k) (Amb (k + m)))
              (EuclideanSpace.proj (𝕜 := ℝ) i) (coordVecFun S f.1 i) from by
      funext f; rw [coordEvalCLM]; rfl]
    exact continuousOn_finsetSum _ fun i _ =>
      (ContinuousLinearMap.continuous _).comp_continuousOn (hvec i)
  exact (ContinuousLinearMap.continuous
    (ContinuousLinearMap.compL ℝ (Amb k) (Amb (k + m)) (Amb m) (projC S))).comp_continuousOn hclm

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_chartData (S : ChartIdx k m) : ContinuousOn (chartData S) (baseSet S) := by
  have hmain : ContinuousOn (chartData S) (baseSet S ∩ baseSet S) := by
    have hpre : (Quotient.mk'' ⁻¹' (baseSet S ∩ baseSet S)) = chartSet S ∩ chartSet S := by
      ext f
      rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_inter_iff, mem_baseSet_iff]
    have hq : Topology.IsQuotientMap
        ((baseSet S ∩ baseSet S).restrictPreimage (Quotient.mk'' : Stiefel k m → OG k m)) :=
      Topology.IsQuotientMap.restrictPreimage_isOpen isQuotientMap_quotient_mk'
        ((isOpen_baseSet S).inter (isOpen_baseSet S))
    have hcomp : ((baseSet S ∩ baseSet S).domRestrict (chartData S)) ∘
          ((baseSet S ∩ baseSet S).restrictPreimage (Quotient.mk'' : Stiefel k m → OG k m))
        = fun y : ↥(Quotient.mk'' ⁻¹' (baseSet S ∩ baseSet S)) => chartFun S y.1 := by
      funext y
      exact chartData_mk S y.1
    rw [continuousOn_iff_continuous_domRestrict, hq.isCoinducing.eq_coinduced,
      continuous_coinduced_dom]
    rw [hcomp, hpre]
    exact continuousOn_iff_continuous_domRestrict.mp
      ((continuousOn_chartFun S).mono Set.inter_subset_left)
  rwa [Set.inter_self] at hmain


end

end Work.ThomBordism.Grassmann.Smooth
