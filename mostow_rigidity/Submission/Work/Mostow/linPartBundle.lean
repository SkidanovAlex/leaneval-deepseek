import Mathlib
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.Margulis.ComplexifyOrth
import Submission.Work.Mostow.linPartAux
import Submission.Work.Mostow.cAct_eigen_root_charpoly

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

/-! ## Entry bounds for the spatial block -/

/-- The deviation of the `(i,j)` spatial entry of `R` from the identity is the inner product
of `e_i` with `(R - 1) e_j`. -/
lemma Rmat_sub_dE_eq (R : E n ≃ₗᵢ[ℝ] E n) (i j : Fin n) :
    Rmat n R i j - dE n (Sum.inl i) (Sum.inl j)
      = inner ℝ (EuclideanSpace.single i (1:ℝ))
          (((R : E n →L[ℝ] E n) - 1) (EuclideanSpace.single j (1:ℝ))) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
    inner_single, inner_single, dE_apply, EuclideanSpace.single, PiLp.single_apply]
  simp [Rmat, Matrix.of_apply, Sum.inl.injEq]

/-- The spatial entries of `R - 1` are bounded by its operator norm. -/
lemma Rmat_sub_dE_abs_le (R : E n ≃ₗᵢ[ℝ] E n) (i j : Fin n) :
    |Rmat n R i j - dE n (Sum.inl i) (Sum.inl j)| ≤ ‖(R : E n →L[ℝ] E n) - 1‖ := by
  rw [Rmat_sub_dE_eq]
  have hn : ∀ k : Fin n, ‖EuclideanSpace.single k (1:ℝ)‖ = 1 := by
    intro k; rw [EuclideanSpace.norm_single, norm_one]
  calc |inner ℝ (EuclideanSpace.single i (1:ℝ))
        (((R : E n →L[ℝ] E n) - 1) (EuclideanSpace.single j (1:ℝ)))|
      ≤ ‖EuclideanSpace.single i (1:ℝ)‖
          * ‖((R : E n →L[ℝ] E n) - 1) (EuclideanSpace.single j (1:ℝ))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ 1 * (‖(R : E n →L[ℝ] E n) - 1‖ * ‖EuclideanSpace.single j (1:ℝ)‖) := by
        rw [hn i]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) zero_le_one
    _ = ‖(R : E n →L[ℝ] E n) - 1‖ := by
        rw [hn j, mul_one, one_mul]

/-! ## The lift of an isometry fixing the base point -/

/-- Bundle of facts about an isometry `g` fixing the base point, with linear part `R`:
the matrix `LambdaMat g` fixes the time vector, its spatial block is `R`, its trace is
`tr R + 1`, it is entrywise near the identity once `R` is near the identity in operator norm,
and the complex eigenvalues of `R` are roots of its characteristic polynomial. -/
theorem linPartBundle (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hR : ∀ u : EuclideanSpace ℝ (Fin n), g • u = R u) :
    ((Work.Mostow.LambdaMat g).mulVec (Submission.Mostow.Hyper.etime n) = Submission.Mostow.Hyper.etime n) ∧
    (∀ u : EuclideanSpace ℝ (Fin n), (Work.Mostow.LambdaMat g).mulVec (Work.Mostow.wvec u) = Work.Mostow.wvec (R u)) ∧
    ((Work.Mostow.LambdaMat g).trace = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (R : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) + 1) ∧
    (∀ q : ℝ, ‖(R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) - 1‖ ≤ q → Work.Mostow.Near1 (Work.Mostow.ToO g) q) ∧
    (∀ μ : ℂ, Module.End.HasEigenvalue ((Work.Mostow.Margulis.cAct R : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℂ] (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))) μ →
      (Matrix.charpoly ((Work.Mostow.LambdaMat g).map (algebraMap ℝ ℂ))).IsRoot μ) := by
  have hfix : LambdaMat g *ᵥ Hyper.etime n = Hyper.etime n := by
    have h := hlift_LambdaMat hA g (0 : E n)
    rw [hR 0, R.map_zero, Hyper.hlift_zero] at h
    exact h.symm
  refine ⟨hfix, ?_, ?_, ?_, ?_⟩
  · intro u
    have hub := hlift_LambdaMat hA g u
    rw [hR u] at hub
    rw [hlift_eq_wvec_add u, Matrix.mulVec_add, Matrix.mulVec_smul, hfix] at hub
    rw [hlift_eq_wvec_add (R u), tpart_linIso] at hub
    exact (add_right_cancel hub).symm
  · have htr : LinearMap.trace ℝ (E n) (R : E n →ₗ[ℝ] E n) = ∑ i : Fin n, Rmat n R i i := by
      rw [LinearMap.trace_eq_sum_inner (R : E n →ₗ[ℝ] E n) (EuclideanSpace.basisFun (Fin n) ℝ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EuclideanSpace.basisFun_apply, inner_single]
      rfl
    have h1 : (LambdaMat g).trace = (∑ i : Fin n, Rmat n R i i) + 1 := by
      rw [Matrix.trace]
      simp only [Matrix.diag_apply]
      rw [Fintype.sum_sum_type]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Lam_inl_inl hA g R hR i i]
      · rw [Fin.sum_univ_one, Lam_inr_inr hA g R hR]
    rw [h1, ← htr]
  · intro q hq
    have hq0 : 0 ≤ q := le_trans (norm_nonneg ((R : E n →L[ℝ] E n) - 1)) hq
    intro i j
    rw [mat_ToO]
    rcases i with i | i <;> rcases j with j | j
    · rw [Lam_inl_inl hA g R hR i j]
      exact le_trans (Rmat_sub_dE_abs_le R i j) hq
    · rw [show j = (0 : Fin 1) from Subsingleton.elim j 0, Lam_inl_inr hA g R hR i]
      simpa [dE_apply, Sum.inl_ne_inr] using hq0
    · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0, Lam_inr_inl hA g R hR j]
      simpa [dE_apply, Sum.inr_ne_inl] using hq0
    · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0,
        show j = (0 : Fin 1) from Subsingleton.elim j 0, Lam_inr_inr hA g R hR]
      simpa [dE_apply] using hq0
  · intro μ hμ
    have hroot := cAct_eigen_root_charpoly n R μ hμ
    rw [Lam_map_eq_fromBlocks hA g R hR, Matrix.charpoly_fromBlocks_zero₁₂]
    exact Polynomial.root_mul.mpr (Or.inl hroot)

end

end Work.Mostow
