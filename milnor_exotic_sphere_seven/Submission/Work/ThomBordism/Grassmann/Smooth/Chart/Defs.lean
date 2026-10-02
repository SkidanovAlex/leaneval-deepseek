import Mathlib
import Submission.Work.ThomBordism.Grassmann.ChartFrame
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.ThomBordism.Grassmann.Smooth.Graph
import Submission.Work.ThomBordism.Grassmann.Smooth.Orientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Charts of the oriented Grassmannian: definitions

This file sets up the vocabulary for the chart construction on `OG k m = G̃r_k(ℝ^{k+m})`:

* `coordVecFun`, `coordEvalFun`, `coordEvalCLM` — the plane of a *plain* (not necessarily
  orthonormal) family `f : Fin k → Amb (k+m)`, described by its `S`-coordinates;
* `chartData S x` — the graph data of the plane of `x` with respect to the chart index `S`;
* `graphChange S T` — the model expression for the change of chart `S → T`;
* `flipMat k` — the diagonal matrix `diag(-1,1,…,1)`, which reverses orientation for `k ≥ 1`.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Topology
open Set

noncomputable section

variable {k m : ℕ}

/-! ## The plane of a plain family, in `S`-coordinates -/

/-- The `i`-th `S`-coordinate vector of the family `f` (a plain family, not necessarily
orthonormal; the interesting case is `(frameMatrix S f).det ≠ 0`). -/
def coordVecFun (S : ChartIdx k m) (f : Fin k → Amb (k + m)) (i : Fin k) : Amb (k + m) :=
  ∑ j, (frameMatrix S f)⁻¹ j i • f j

/-- The vector of the plane of `f` whose `S`-coordinates are `v`. -/
def coordEvalFun (S : ChartIdx k m) (f : Fin k → Amb (k + m)) (v : Amb k) : Amb (k + m) :=
  ∑ i, WithLp.ofLp v i • coordVecFun S f i

/-- The same as a continuous linear map in the coordinate vector. -/
def coordEvalCLM (S : ChartIdx k m) (f : Fin k → Amb (k + m)) : Amb k →L[ℝ] Amb (k + m) :=
  ∑ i : Fin k, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (coordVecFun S f i)

@[simp] theorem coordVecFun_stiefel (S : ChartIdx k m) (f : Stiefel k m) (i : Fin k) :
    coordVecFun S f.1 i = coordVec S f i := rfl

theorem coordEvalCLM_apply (S : ChartIdx k m) (f : Fin k → Amb (k + m)) (v : Amb k) :
    coordEvalCLM S f v = coordEvalFun S f v := by
  rw [coordEvalFun, coordEvalCLM, sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj]

theorem coordEvalCLM_stiefel_apply (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    coordEvalCLM S f.1 v = coordEval S f v := by
  rw [coordEvalCLM_apply]
  rfl

/-! ## Invariance of the coordinate evaluation under the `SO(k)`-action -/

theorem coordVecFun_soActFun (S : ChartIdx k m) (A : SOk k) (f : Stiefel k m) (i : Fin k) :
    coordVecFun S (soActFun A.1 f.1) i = coordVecFun S f.1 i := by
  rw [show coordVecFun S (soActFun A.1 f.1) i = coordVec S (A.act f) i from rfl,
    coordVec_soActFun]
  rfl

theorem SOk_act_val (A : SOk k) (f : Stiefel k m) : (A.act f).1 = soActFun A.1 f.1 := rfl

theorem coordEvalCLM_soActFun (S : ChartIdx k m) (A : SOk k) (f : Stiefel k m) :
    coordEvalCLM S (soActFun A.1 f.1) = coordEvalCLM S f.1 := by
  simp only [coordEvalCLM]
  exact Finset.sum_congr rfl fun i _ => by rw [coordVecFun_soActFun S A f i]

/-! ## The graph data of a point -/

/-- The chart map at the frame level: the complement coordinates of the plane of `f`, read through
the `S`-coordinate trivialisation of the tautological bundle. -/
def chartFun (S : ChartIdx k m) (f : Stiefel k m) : Amb k →L[ℝ] Amb m :=
  (projC S).comp (coordEvalCLM S f.1)

theorem chartFun_apply (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    chartFun S f v = projC S (coordEval S f v) := by
  rw [chartFun, ContinuousLinearMap.comp_apply, coordEvalCLM_stiefel_apply]

/-- **The graph data of a point of the oriented Grassmannian** in the chart `S`: the map sending
a coordinate vector `v ∈ ℝ^k` to the coordinates in the complement of `S` of the vector of the
plane of `x` whose `S`-coordinates are `v`.  Off the chart `U_S` it takes a junk value. -/
def chartData (S : ChartIdx k m) : OG k m → (Amb k →L[ℝ] Amb m) :=
  Quotient.lift (chartFun S) fun f g hfg => by
    obtain ⟨A, rfl⟩ := hfg
    show chartFun S f = chartFun S (A.act f)
    rw [chartFun, chartFun, SOk_act_val, coordEvalCLM_soActFun]

@[simp] theorem chartData_mk (S : ChartIdx k m) (f : Stiefel k m) :
    chartData S (Quotient.mk'' f) = chartFun S f := rfl

theorem chartData_mk_apply (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    chartData S (Quotient.mk'' f) v = projC S (coordEval S f v) := by
  rw [chartData_mk, chartFun_apply]

/-! ## The model expression for a change of chart -/

/-- The condition under which the graph change is defined: the `T`-coordinate projection is
invertible on the graph of `d`. -/
def graphUnit (S T : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) : Prop :=
  IsUnit ((projS T).comp (graphMap S d))

/-- **The change of chart `S → T` on graph data**: the graph of `d` is re-read in the chart `T`.
Written with `Ring.inverse` so that it is smooth on the open set where `projS T ∘ graphMap S d`
is invertible. -/
def graphChange (S T : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) : Amb k →L[ℝ] Amb m :=
  (projC T).comp ((graphMap S d).comp (Ring.inverse ((projS T).comp (graphMap S d))))

theorem graphChange_apply (S T : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) (v : Amb k) :
    graphChange S T d v
      = projC T (graphMap S d (Ring.inverse ((projS T).comp (graphMap S d)) v)) := by
  rw [graphChange, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

/-! ## The orientation reversing matrix -/

/-- The diagonal matrix `diag(-1,1,…,1)`; for `0 < k` it is orthogonal of determinant `-1`. -/
def flipMat (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun i : Fin k => if (i : ℕ) = 0 then -1 else 1

theorem flipMat_transpose (k : ℕ) : (flipMat k).transpose = flipMat k :=
  Matrix.diagonal_transpose _

theorem flipMat_mul_self (k : ℕ) : flipMat k * flipMat k = 1 := by
  rw [flipMat, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff).mpr fun i => ?_
  by_cases h : (i : ℕ) = 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

theorem flipMat_transpose_mul_self (k : ℕ) : (flipMat k).transpose * flipMat k = 1 := by
  rw [flipMat_transpose, flipMat_mul_self]

theorem flipMat_det_of_pos {k : ℕ} (hk : 0 < k) : (flipMat k).det = -1 := by
  rw [flipMat, Matrix.det_diagonal]
  refine (Finset.prod_eq_single (⟨0, hk⟩ : Fin k) ?_ ?_).trans ?_
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext h))]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [if_pos rfl]


theorem flipMat_det_ne_zero (k : ℕ) : (flipMat k).det ≠ 0 := by
  by_cases hk : k = 0
  · subst hk
    have h : flipMat 0 = 1 := Subsingleton.elim _ _
    rw [h, Matrix.det_one]; exact one_ne_zero
  · rw [flipMat_det_of_pos (Nat.pos_of_ne_zero hk)]; norm_num
end

end Work.ThomBordism.Grassmann.Smooth
