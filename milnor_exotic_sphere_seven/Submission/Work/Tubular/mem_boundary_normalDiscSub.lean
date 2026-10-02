import Mathlib
import Submission.Work.Tubular.exists_normalDiscManifold
import Submission.Work.Tubular.DiscManifold.Manifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The boundary of the normal disc bundle is the normal sphere bundle

The closed `ε`-disc bundle `D_ε(ν)` of the normal bundle of an embedding `V ↪ ℝ^{8+k}` is a `C¹`
manifold with boundary modelled on the half space `EuclideanHalfSpace (8+k)`
(`Work.Tubular.NormalDiscManifold`, `Work.Tubular.exists_normalDiscManifold`).  This file identifies
its **boundary**: a point is a boundary point exactly when its normal vector has norm `ε`, i.e. the
boundary is the sphere bundle `S_ε(ν)`.

The charted space at stake is the one of `Work.Tubular.discChartedSpace C`, transported along the
model homeomorphism `R.Λ` (`Work.Tubular.DiscManifold.HalfModelReindex`) — the reindexing which
moves the first `k` coordinates of `ℝ^{8+k}` into the *fibre* factor of the product model
`ℝ⁸ × Half (k-1)`; the half-space coordinate of the model is therefore decided by the fibre chart,
which is exactly what makes the boundary the sphere bundle.

The two ingredients of the computation are
* `Work.Tubular.DiscManifold.HalfModelReindex.Λ_symm_apply_zero`: the `0`-th coordinate of `Λ.symm`
  is the `0`-th coordinate of the fibre part;
* `Work.Tubular.ball_chartAt_coord_zero_iff`: the preferred chart of the closed ball at `x` has
  `0`-th coordinate `0` exactly when `x` is a unit vector — the unfolding of
  `Work.SignatureBordism.ball_mem_boundary_iff_norm`, which says that the boundary of `D^k` is
  `S^{k-1}`.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Tubular

open Work.SignatureBordism

variable {k : ℕ} [NeZero k]

/-! ## The two auxiliary computations -/

/-- **The `0`-th coordinate of `Λ.symm` is the `0`-th coordinate of the fibre part.**  The reindexing
`Λ : EuclideanHalfSpace (8+k) ≃ ℝ⁸ × Half (k-1)` puts the first `k` coordinates of the ambient
space into the fibre factor, so the half-space condition `0 ≤ x 0` is the fibre condition
`0 ≤ (Λ x).2 0`.  This is the coordinate form of the structure field `Λ_snd_val`. -/
theorem DiscManifold.HalfModelReindex.Λ_symm_apply_zero (R : DiscManifold.HalfModelReindex k)
    (a : Euc 8) (b : EuclideanHalfSpace ((k - 1) + 1)) :
    ((R.Λ.symm (a, b)).val) 0 = (b.val) 0 := by
  have h := R.Λ_snd_val (R.Λ.symm (a, b))
  rw [Homeomorph.apply_symm_apply] at h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin ((k - 1) + 1)) => v 0) h
  rw [R.split_snd_zero] at h2
  exact h2.symm

/-- **The preferred chart of the closed ball is `0` on the boundary hyperplane exactly on the
sphere**: for `x ∈ D^{n+1}`, the `0`-th coordinate of `chartAt (Half n) x x` vanishes if and only if
`x` is a unit vector.  This is `Work.SignatureBordism.ball_mem_boundary_iff_norm` with the boundary
of `Ball n` unfolded by its definition through the preferred chart. -/
theorem ball_chartAt_coord_zero_iff (n : ℕ) (x : Ball n) :
    0 = ((((chartAt (Half n) x) x)).val : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔
      ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  have h := ball_mem_boundary_iff_norm n x
  rw [ModelWithCorners.boundary, Set.mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff,
    extChartAt_ball, frontier_range_modelWithCornersEuclideanHalfSpace (n + 1),
    Set.mem_ofPred_eq] at h
  exact h

/-! ## The boundary of the disc bundle -/

theorem mem_boundary_normalDiscSub {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (C : Work.Tubular.TubeChart E ε)
    (R : Work.Tubular.DiscManifold.HalfModelReindex k) (p : Work.Tubular.NormalDiscSub E ε) :
    letI := Work.Tubular.chartedSpaceOfModelHomeo (Work.Tubular.discChartedSpace C) R.Λ
    (p ∈ (modelWithCornersEuclideanHalfSpace (8 + k)).boundary (Work.Tubular.NormalDiscSub E ε) ↔
      Work.Tubular.normalNorm E (p : Work.Tubular.NormalTotal E) = ε) := by
  letI := Work.Tubular.chartedSpaceOfModelHomeo (Work.Tubular.discChartedSpace C) R.Λ
  -- unfold the boundary of the half-space model
  have hfront : frontier (Set.range (modelWithCornersEuclideanHalfSpace (8 + k))) =
      {t : Euc (8+k) | 0 = t 0} := frontier_range_modelWithCornersEuclideanHalfSpace (8+k)
  rw [ModelWithCorners.boundary, Set.mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff, hfront,
    Set.mem_ofPred_eq]
  -- the value of the chart at `p`, and of the extended chart applied to `p`
  have hch : (chartAt (EuclideanHalfSpace (8+k)) p) p = R.Λ.symm ((discChart C p) p) := rfl
  have hd : (discChart C p) p = ((chartBaseC p) (NormalTotal.proj p.1),
      (chartFibC C p) (chartFibPt C p)) := by
    rw [discChart_apply]
    show chartToFun C p p = _
    simp only [chartToFun]
    rw [discPt_of_mem (k-1) (mem_ball_ballVecI (mem_coverBaseSet_discPiece p))]
    rfl
  have hcoord : (extChartAt (modelWithCornersEuclideanHalfSpace (8+k)) p p) 0
      = (((chartFibC C p) (chartFibPt C p)).val) 0 := by
    rw [extChartAt_coe]
    show ((modelWithCornersEuclideanHalfSpace (8+k))
      ((chartAt (EuclideanHalfSpace (8+k)) p) p)) 0 = _
    rw [modelWithCornersEuclideanHalfSpace_apply, hch, hd]
    exact DiscManifold.HalfModelReindex.Λ_symm_apply_zero R _ _
  rw [hcoord]
  -- the half-space coordinate is the fibre coordinate, whose vanishing is the sphere condition
  show 0 = ((((chartAt (Half (k-1)) (chartFibPt C p)) (chartFibPt C p))).val) 0 ↔
    normalNorm E (p : NormalTotal E) = ε
  rw [ball_chartAt_coord_zero_iff (k-1) (chartFibPt C p)]
  have hnorm : ‖(chartFibPt C p : EuclideanSpace ℝ (Fin ((k-1)+1)))‖ = 1 ↔
      normalNorm E (p : NormalTotal E) = ε := by
    have hcoe : ((chartFibPt C p : Ball (k-1)) : EuclideanSpace ℝ (Fin ((k-1)+1)))
        = ballVecI C (discPiece p) p := rfl
    rw [hcoe, ballVecI, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos C.eps_pos,
      norm_readFE C (discPiece p) (mem_coverBaseSet_discPiece p) (NormalTotal.vec_mem p.1)]
    show ε⁻¹ * ‖NormalTotal.vec p.1‖ = 1 ↔ ‖NormalTotal.vec p.1‖ = ε
    rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt C.eps_pos), mul_one]
  exact hnorm

end Work.Tubular
