import Mathlib
import Submission.Work.Whitney.RankTwo.RepDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

theorem eBall_δ_apply {n : ℕ} (x : (ssBall Y) _⦋n + 1⦌) (i : Fin (n + 2))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    eBall Y n ((ssBall Y).δ i x) z = eBall Y (n + 1) x (stdSimplex.map i.succAbove z) :=
  TopCat.toSSetObjEquivOld_δ_apply x i z

theorem ssBall_δ_zero_segSimp (y : Y) (k : ℕ) :
    (ssBall Y).δ 0 (segSimp Y y k)
      = ptBall Y (y, ⟨segVecC k (stdSimplex.vertex (1 : Fin 2)), segVecC_mem k _⟩) := by
  apply (eBall Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [eBall_δ_apply, eBall_ptBall, ContinuousMap.const_apply, map_succAbove0_eq_vertex,
    eBall_segSimp]
  rfl

theorem ssBall_δ_one_segSimp (y : Y) (k : ℕ) :
    (ssBall Y).δ 1 (segSimp Y y k)
      = ptBall Y (y, ⟨segVecC k (stdSimplex.vertex (0 : Fin 2)), segVecC_mem k _⟩) := by
  apply (eBall Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [eBall_δ_apply, eBall_ptBall, ContinuousMap.const_apply, map_succAbove1_eq_vertex,
    eBall_segSimp]
  rfl

/-- The intermediate points of the first two straight simplices coincide. -/
theorem segVecC_end_eq (y : Y) :
    ((y, ⟨segVecC 0 (stdSimplex.vertex (1 : Fin 2)), segVecC_mem 0 _⟩) : BBall Y)
      = ((y, ⟨segVecC 1 (stdSimplex.vertex (0 : Fin 2)), segVecC_mem 1 _⟩) : BBall Y) := by
  have hv : segVecC 0 (stdSimplex.vertex (1 : Fin 2))
      = segVecC 1 (stdSimplex.vertex (0 : Fin 2)) := by
    simp [segVecC_apply, segCosC, ContinuousMap.comp_apply, arcAngC_apply, stdSimplex.vertex,
      ang_zero, ang_one]
  congr 1
  exact Subtype.ext hv

/-- The intermediate points of the last two straight simplices coincide. -/
theorem segVecC_end_eq' (y : Y) :
    ((y, ⟨segVecC 1 (stdSimplex.vertex (1 : Fin 2)), segVecC_mem 1 _⟩) : BBall Y)
      = ((y, ⟨segVecC 2 (stdSimplex.vertex (0 : Fin 2)), segVecC_mem 2 _⟩) : BBall Y) := by
  have hv : segVecC 1 (stdSimplex.vertex (1 : Fin 2))
      = segVecC 2 (stdSimplex.vertex (0 : Fin 2)) := by
    simp [segVecC_apply, segCosC, ContinuousMap.comp_apply, arcAngC_apply, stdSimplex.vertex,
      ang_zero, ang_one, ang_two]
  congr 1
  exact Subtype.ext hv

/-- The initial point of the chain of straight simplices is the point `(y, +1)`. -/
theorem segVecC_start_eq (y : Y) :
    ((y, ⟨segVecC 0 (stdSimplex.vertex (0 : Fin 2)), segVecC_mem 0 _⟩) : BBall Y)
      = ((y, ⟨sphPlus, sphPlus_mem_ball⟩) : BBall Y) := by
  have hv : segVecC 0 (stdSimplex.vertex (0 : Fin 2))
      = (sphPlus : EuclideanSpace ℝ (Fin 1)) := by
    simp [segVecC_apply, segCosC, ContinuousMap.comp_apply, arcAngC_apply, stdSimplex.vertex,
      ang_zero, Real.cos_zero, sphPlus, one1]
  congr 1
  exact Subtype.ext hv

/-- The final point of the chain of straight simplices is the point `(y, -1)`. -/
theorem segVecC_endpoint_eq (y : Y) :
    ((y, ⟨segVecC 2 (stdSimplex.vertex (1 : Fin 2)), segVecC_mem 2 _⟩) : BBall Y)
      = ((y, ⟨sphMinus, sphMinus_mem_ball⟩) : BBall Y) := by
  have hv : segVecC 2 (stdSimplex.vertex (1 : Fin 2))
      = (sphMinus : EuclideanSpace ℝ (Fin 1)) := by
    simp [segVecC_apply, segCosC, ContinuousMap.comp_apply, arcAngC_apply, stdSimplex.vertex,
      ang_zero, ang_two, ang_three, Real.cos_pi, sphMinus_eq_neg, sphPlus, one1]
  congr 1
  exact Subtype.ext hv


/-- The boundary of the chain of straight simplices of the ball. -/
theorem segChain_boundary (y : Y) :
    (((ssBall Y).chainComplex zR).d 1 0) (segChain Y y)
      = ((ssBall Y).ιChainComplex (R := zR) (ballMinus Y y)).hom 1
        - ((ssBall Y).ιChainComplex (R := zR) (ballPlus Y y)).hom 1 := by
  have hterm : ∀ k ∈ Finset.range 3,
      (((ssBall Y).chainComplex zR).d 1 0)
          (((ssBall Y).ιChainComplex (R := zR) (segSimp Y y k)).hom 1)
        = ((ssBall Y).ιChainComplex (R := zR) ((ssBall Y).δ 0 (segSimp Y y k))).hom 1
          - ((ssBall Y).ιChainComplex (R := zR) ((ssBall Y).δ 1 (segSimp Y y k))).hom 1 := by
    intro k _
    have h := congrArg (fun (g : zR ⟶ ((ssBall Y).chainComplex zR).X 0) => g.hom (1 : zR))
      (SSet.ιChainComplex_d (ssBall Y) zR (segSimp Y y k))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, Fin.sum_univ_two]
    simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply]
    norm_num
    rw [sub_eq_add_neg]
  rw [segChain, map_sum, Finset.sum_congr rfl hterm]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero, zero_add]
  rw [ssBall_δ_zero_segSimp Y y 0, ssBall_δ_zero_segSimp Y y 1, ssBall_δ_zero_segSimp Y y 2,
    ssBall_δ_one_segSimp Y y 0, ssBall_δ_one_segSimp Y y 1, ssBall_δ_one_segSimp Y y 2]
  rw [ballPlus, ballMinus]
  have hAB : ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨segVecC 0 (stdSimplex.vertex (1 : Fin 2)), segVecC_mem 0 _⟩))).hom 1
      = ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨segVecC 1 (stdSimplex.vertex (0 : Fin 2)), segVecC_mem 1 _⟩))).hom 1 := by
    rw [segVecC_end_eq Y y]
  have hBC : ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨segVecC 1 (stdSimplex.vertex (1 : Fin 2)), segVecC_mem 1 _⟩))).hom 1
      = ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨segVecC 2 (stdSimplex.vertex (0 : Fin 2)), segVecC_mem 2 _⟩))).hom 1 := by
    rw [segVecC_end_eq' Y y]
  have hA : ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨segVecC 0 (stdSimplex.vertex (0 : Fin 2)), segVecC_mem 0 _⟩))).hom 1
      = ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨sphPlus, sphPlus_mem_ball⟩))).hom 1 := by
    rw [segVecC_start_eq Y y]
  have hC : ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨segVecC 2 (stdSimplex.vertex (1 : Fin 2)), segVecC_mem 2 _⟩))).hom 1
      = ((ssBall Y).ιChainComplex (R := zR)
        (ptBall Y (y, ⟨sphMinus, sphMinus_mem_ball⟩))).hom 1 := by
    rw [segVecC_endpoint_eq Y y]
  rw [hAB, hBC, hA, hC]
  abel

end

end Work.Whitney.RankTwo
