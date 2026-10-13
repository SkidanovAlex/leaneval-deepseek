import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE5.Operators.rank_eq_of_det_ne_zero_submatrix

noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-! ## §0b. Analyticity and derivatives of `eaEval` -/

/-- The affine forms `ℓ_j` are analytic. -/
theorem analyticAt_ell {k r : ℕ} (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) :
    AnalyticAt ℝ (fun w : Fin k → ℝ => c.ell j w) x := by
  have hfun : (fun w : Fin k → ℝ => c.ell j w) =
      fun w => (∑ i, c.a j i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) w + c.b j := by
    funext w
    simp [EAChain.ell, smul_eq_mul]
  rw [hfun]
  exact (ContinuousLinearMap.analyticAt _ x).add analyticAt_const

/-- `eaEval c Q` is analytic in the point. -/
theorem analyticAt_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) :
    AnalyticAt ℝ (fun w : Fin k → ℝ => eaEval c Q w) x := by
  rw [show (fun w : Fin k → ℝ => eaEval c Q w) = fun w =>
      MvPolynomial.aeval (Sum.elim w (fun j => Real.exp (c.ell j w))) Q from by
    funext w; rfl]
  apply AnalyticAt.aeval_mvPolynomial
  intro i
  rcases i with i | j
  · exact (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).analyticAt x
  · have h1 : AnalyticAt ℝ (fun t : ℝ => Real.exp t) (c.ell j x) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.exp_analytic _
    exact h1.comp (analyticAt_ell c j x)

/-- A finite sum of multiples of the coordinate projections, evaluated at a basis vector. -/
theorem sum_smul_proj_single {k : ℕ} (cs : Fin k → ℝ) (j : Fin k) :
    (∑ i : Fin k, cs i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))
      (Pi.single j 1) = cs j := by
  classical
  have h1 : (∑ i : Fin k, cs i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))
      (Pi.single j 1) = ∑ i : Fin k, cs i * ((Pi.single j 1 : Fin k → ℝ) i) := by
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [h1]
  have h2 : ∀ i : Fin k, cs i * ((Pi.single j 1 : Fin k → ℝ) i) = if i = j then cs i else 0 := by
    intro i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne, h]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]

/-- Evaluating the derivative of `eaEval c Q` at the standard basis vector. -/
theorem fderiv_eaEval_apply_single {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    (x : Fin k → ℝ) (i : Fin k) :
    (fderiv ℝ (fun w : Fin k → ℝ => eaEval c Q w) x) (Pi.single i 1) = eaEval c (eaD c i Q) x := by
  rw [(Work.WilE5.Calc.hasFDerivAt_eaEval c Q x).fderiv]
  exact sum_smul_proj_single _ i

/-- The `fderiv` of a finite family of `eaEval`s, as a `ContinuousLinearMap.pi`. -/
theorem fderiv_pi_eaEval {k r j : ℕ} (c : EAChain k r) (hh : Fin j → EAPoly k r)
    (x : Fin k → ℝ) :
    fderiv ℝ (fun w : Fin k → ℝ => fun a : Fin j => eaEval c (hh a) w) x
      = ContinuousLinearMap.pi (fun a : Fin j =>
          (∑ i : Fin k, eaEval c (eaD c i (hh a)) x •
            (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))) := by
  rw [fderiv_pi (fun a => (Work.WilE5.Calc.hasFDerivAt_eaEval c (hh a) x).differentiableAt)]
  congr 1
  funext a
  exact (Work.WilE5.Calc.hasFDerivAt_eaEval c (hh a) x).fderiv

/-- A matrix with an invertible `m × m` submatrix gives a surjective linear map. -/
theorem range_pi_eq_top_of_det_submatrix_ne_zero {m n : ℕ} (cs : Fin m → Fin n → ℝ)
    (κ : Fin m → Fin n) (hdet : ((Matrix.of cs).submatrix id κ).det ≠ 0) :
    (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ i : Fin n, cs a i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)))).range
      = ⊤ := by
  have hrank : (Matrix.of cs).rank = m :=
    Work.WilE5.Operators.rank_eq_of_det_ne_zero_submatrix (Matrix.of cs) κ hdet
  have hpoint : ∀ v : Fin n → ℝ, (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ i : Fin n, cs a i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)))) v
      = (Matrix.of cs).mulVecLin v := by
    intro v
    funext a
    rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]
  have hcoe : ((ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ i : Fin n, cs a i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))) :
        (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
      = (Matrix.of cs).mulVecLin := LinearMap.ext hpoint
  have hfin : Module.finrank ℝ (LinearMap.range (Matrix.of cs).mulVecLin)
      = Module.finrank ℝ (Fin m → ℝ) := by
    show (Matrix.of cs).rank = Module.finrank ℝ (Fin m → ℝ)
    rw [hrank]
    exact ((Module.finrank_fintype_fun_eq_card (R := ℝ)).trans (Fintype.card_fin m)).symm
  have htop : LinearMap.range (Matrix.of cs).mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq hfin
  rw [show (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ i : Fin n, cs a i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)))).range
        = LinearMap.range (Matrix.of cs).mulVecLin from by rw [← hcoe], htop]

/-- Evaluating the `ContinuousLinearMap.pi` built from a matrix at a basis vector. -/
theorem pi_apply_single {m n : ℕ} (cs : Fin m → Fin n → ℝ) (i : Fin n) (b : Fin m) :
    (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin n, cs a j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))))
        (Pi.single i 1) b = cs b i := by
  rw [ContinuousLinearMap.pi_apply]
  exact sum_smul_proj_single (fun j => cs b j) i

end Work.WilE5.Strat
