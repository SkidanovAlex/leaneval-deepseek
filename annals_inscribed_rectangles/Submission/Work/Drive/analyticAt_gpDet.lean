import Mathlib
import Submission.Work.Drive.linGpDefs

/-!
# Analyticity of the general-position determinant `gpDet`

`Work.Drive.gpDet A k` is the determinant of the `4 × 4` matrix `Work.Drive.gpMat A k t` whose
four rows are the functionals

* `linFun (gpPsi A n t)` (`n = 0,1,2`) — the normal of the `n`-th transported plane, and
* `gpCoordPull 2 (gpPsi A k t)` — the functional cutting the boundary line out of the `k`-th plane,

evaluated on the standard basis `gpStdVec j`.  Its nonvanishing is the general-position condition of
`Work.Drive.rowCD_linTrans_generalPosition_openDense`, and the density engine
`Work.Drive.isOpen_denseAtBall_ne_zero` needs it to be *analytic*.

Every row is of the form `gpInvCoord A n m (gpStdVec j)`, i.e. a coordinate of `(Ψ n t)⁻¹ v`; by the
explicit inverse formula `Work.Drive.gpInvCoord_formula` such a coordinate equals

> `(1 + ‖blk n t‖²)⁻¹ * (linear function of t)`,

a rational function with strictly positive denominator `1 + classNormSq (blk n t) ≥ 1`.  Analyticity
then follows from the closure properties of `AnalyticAt` — a continuous linear function of `t` is
analytic, and the reciprocal of an analytic function with nonvanishing value is analytic — together
with the Leibniz formula `Matrix.det_apply'` for the determinant.

The file is self-contained: the only inputs are the definitions in `Submission.Work.Drive.linGpDefs`
and the facts `classNormSq_nonneg`, `gpInvCoord_formula`, `gpClassGenCoord_apply` proved there.
-/

namespace Work.Drive

noncomputable section

open Filter

/-! ## The entries of `gpMat` are analytic -/

/-- The coordinates of the `k`-th block of the parameter are analytic in `t`. -/
lemma analyticAt_gpBlkCoord (k : Fin 3) (j : Fin 4) (t₀ : EuclideanSpace ℝ (Fin 12)) :
    AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => ((blk k t) : EuclideanSpace ℝ (Fin 4)) j) t₀ := by
  have h : AnalyticAt ℝ (fun t => gpLinCoord k j t) t₀ := (gpLinCoord k j).analyticAt t₀
  simpa only [gpLinCoord_apply] using h

/-- The class norm square `t ↦ ‖blk k t‖²` of a block of the parameter is analytic. -/
lemma analyticAt_gpClassNormSq_blk (k : Fin 3) (t₀ : EuclideanSpace ℝ (Fin 12)) :
    AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => classNormSq (blk k t)) t₀ := by
  have h1 : AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => ((blk k t) 1) ^ 2) t₀ :=
    (analyticAt_gpBlkCoord k 1 t₀).pow 2
  have h2 : AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => ((blk k t) 2) ^ 2) t₀ :=
    (analyticAt_gpBlkCoord k 2 t₀).pow 2
  have h3 : AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => ((blk k t) 3) ^ 2) t₀ :=
    (analyticAt_gpBlkCoord k 3 t₀).pow 2
  have hf : (fun t : EuclideanSpace ℝ (Fin 12) => classNormSq (blk k t))
      = ((fun t : EuclideanSpace ℝ (Fin 12) => ((blk k t) 1) ^ 2)
          + fun t : EuclideanSpace ℝ (Fin 12) => ((blk k t) 2) ^ 2)
          + fun t : EuclideanSpace ℝ (Fin 12) => ((blk k t) 3) ^ 2 := by
    funext t
    simp only [classNormSq, Pi.add_apply]
  rw [hf]
  exact (h1.add h2).add h3

/-- **Each coordinate of the inverse of a transported chart is analytic.**  This is the analytic
content of the explicit formula `gpInvCoord_formula`: a rational function with denominator
`1 + ‖blk n t‖² ≥ 1`. -/
lemma analyticAt_gpInvCoord (A : Eucl 3 ≃L[ℝ] Eucl 3) (n : Fin 3) (j : Fin 4) (v : Eucl 3)
    (t₀ : EuclideanSpace ℝ (Fin 12)) :
    AnalyticAt ℝ (fun t => gpInvCoord A n j v t) t₀ := by
  have hden : AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => 1 + classNormSq (blk n t)) t₀ :=
    analyticAt_const.add (analyticAt_gpClassNormSq_blk n t₀)
  have hpos : (1 + classNormSq (blk n t₀)) ≠ 0 := by
    have h := classNormSq_nonneg (blk n t₀); linarith
  have hinv : AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) => (1 + classNormSq (blk n t))⁻¹) t₀ := hden.inv hpos
  have hcoord : AnalyticAt ℝ
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        ((linBase A n)⁻¹ v).ofLp j - gpClassGenCoord A n v j t) t₀ :=
    analyticAt_const.sub ((gpClassGenCoord A n v j).analyticAt t₀)
  refine (hinv.mul hcoord).congr (Eventually.of_forall fun t => ?_)
  show (1 + classNormSq (blk n t))⁻¹ *
      (((linBase A n)⁻¹ v).ofLp j - gpClassGenCoord A n v j t) = gpInvCoord A n j v t
  rw [gpInvCoord_formula, gpClassGenCoord_apply]

/-- The rows of `gpMat` are `gpInvCoord`s: the `i`-th row of `gpMat A k t`, read in the standard
basis, is the `3`-rd coordinate of `(Ψ i t)⁻¹` for `i = 0,1,2` and the `2`-nd coordinate of
`(Ψ k t)⁻¹` for `i = 3`.  Hence every entry of `gpMat A k t` is analytic in `t`. -/
lemma analyticAt_gpMat_entry (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (i j : Fin 4)
    (t₀ : EuclideanSpace ℝ (Fin 12)) :
    AnalyticAt ℝ (fun t => gpMat A k t i j) t₀ := by
  rcases i with ⟨n, hn⟩
  interval_cases n
  · show AnalyticAt ℝ (fun t => gpInvCoord A 0 3 (gpStdVec j) t) t₀
    exact analyticAt_gpInvCoord A 0 3 (gpStdVec j) t₀
  · show AnalyticAt ℝ (fun t => gpInvCoord A 1 3 (gpStdVec j) t) t₀
    exact analyticAt_gpInvCoord A 1 3 (gpStdVec j) t₀
  · show AnalyticAt ℝ (fun t => gpInvCoord A 2 3 (gpStdVec j) t) t₀
    exact analyticAt_gpInvCoord A 2 3 (gpStdVec j) t₀
  · show AnalyticAt ℝ (fun t => gpInvCoord A k 2 (gpStdVec j) t) t₀
    exact analyticAt_gpInvCoord A k 2 (gpStdVec j) t₀

/-! ## Analyticity of a determinant of analytic entries -/

/-- **The determinant of a matrix of analytic functions is analytic**, by the Leibniz formula
`Matrix.det_apply'` (a finite sum of finite products of the entries). -/
lemma analyticAt_matrix_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : E → Matrix ι ι ℝ) (t₀ : E)
    (hf : ∀ i j, AnalyticAt ℝ (fun t => f t i j) t₀) :
    AnalyticAt ℝ (fun t => (f t).det) t₀ := by
  have h : (fun t : E => (f t).det)
      = fun t => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, f t (σ i) i := by
    funext t
    rw [Matrix.det_apply']
  have h2 : (fun t : E => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤˣ) : ℤ) *
        ∏ i, f t (σ i) i)
      = ∑ σ : Equiv.Perm ι,
          fun t : E => ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, f t (σ i) i := by
    funext t
    rw [Finset.sum_apply]
  rw [h, h2]
  refine Finset.analyticAt_sum _ (fun σ _ => ?_)
  have hgoal : (fun t : E => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * ∏ i, f t (σ i) i)
      = (fun _ : E => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ)) : ℝ))
        * ∏ i, (fun t : E => f t (σ i) i) := by
    funext t
    simp only [Pi.mul_apply, Finset.prod_apply]
  rw [hgoal]
  exact analyticAt_const.mul (Finset.analyticAt_prod _ (fun i _ => hf (σ i) i))

/-- The general-position determinant of the `k`-th quadruple is analytic. -/
lemma analyticAt_gpMat_det (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t₀ : EuclideanSpace ℝ (Fin 12)) :
    AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => (gpMat A k t).det) t₀ :=
  analyticAt_matrix_det (fun t => gpMat A k t) t₀ (fun i j => analyticAt_gpMat_entry A k i j t₀)

/-- **`Work.Drive.gpDet` is analytic**, the analyticity input of the density engine
`Work.Drive.isOpen_denseAtBall_ne_zero` for the general-position clause of the transported linear
family. -/
theorem analyticAt_gpDet (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (k : Fin 3)
    (t₀ : EuclideanSpace ℝ (Fin 12)) :
    AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => Work.Drive.gpDet A k t) t₀ := by
  show AnalyticAt ℝ (fun t : EuclideanSpace ℝ (Fin 12) => (gpMat A k t).det) t₀
  exact analyticAt_gpMat_det A k t₀

end

end Work.Drive
