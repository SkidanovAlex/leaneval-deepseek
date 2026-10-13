import Mathlib

namespace Work.WilE9.EaD

open MvPolynomial

/-- Evaluating the continuous linear map `∑ i, f i • proj i` on a vector gives the
finite sum `∑ i, f i * v i`. -/
lemma sum_smul_proj_apply {σ : Type*} [Fintype σ] (f v : σ → ℝ) :
    (∑ i, f i • (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) v = ∑ i, f i * v i := by
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The derivative of the coordinate function `y ↦ y n`, in the `∑ pderiv • proj` form. -/
lemma sum_eval_pderiv_X {σ : Type*} [Fintype σ] (n : σ) (x : σ → ℝ) :
    (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.X n))) •
      (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) =
      (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ) := by
  classical
  ext v
  rw [sum_smul_proj_apply]
  simp only [ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single n]
  · rw [MvPolynomial.pderiv_X_self]; simp
  · intro b _ hb
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hb)]
    simp
  · intro hn; exact absurd (Finset.mem_univ n) hn

/-- The derivative of a constant polynomial vanishes. -/
lemma sum_eval_pderiv_C {σ : Type*} [Fintype σ] (a : ℝ) (x : σ → ℝ) :
    (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.C a))) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) = 0 := by
  simp

/-- The `∑ pderiv • proj` expression is additive in the polynomial. -/
lemma sum_eval_pderiv_add {σ : Type*} [Fintype σ] (p q : MvPolynomial σ ℝ) (x : σ → ℝ) :
    (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i (p + q))) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
    = (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
      + (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i q)) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Derivation.map_add, MvPolynomial.eval_add, add_smul]

/-- The `∑ pderiv • proj` expression satisfies the Leibniz rule for multiplication
by an indeterminate. -/
lemma sum_eval_pderiv_mul_X {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (n : σ)
    (x : σ → ℝ) :
    (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i (p * MvPolynomial.X n))) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
    = (MvPolynomial.eval x p) • (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ)
      + (x n) • (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) := by
  classical
  have hterm : ∀ i, (MvPolynomial.eval x (MvPolynomial.pderiv i (p * MvPolynomial.X n))) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)
      = (MvPolynomial.eval x (MvPolynomial.pderiv i p) * x n) •
          (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)
        + (MvPolynomial.eval x p *
            MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.X n))) •
          (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ) := by
    intro i
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, add_smul]
  have hA : (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i p) * x n) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
      = x n • (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_smul, smul_comm]
  have hB : (∑ i, (MvPolynomial.eval x p *
          MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.X n))) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
      = MvPolynomial.eval x p • (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [mul_smul]), Finset.smul_sum.symm,
      sum_eval_pderiv_X]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, hA, hB, add_comm]

/-- The derivative of a multivariate polynomial function: for `p : MvPolynomial σ ℝ` the map
`y ↦ p.eval y` has derivative `∑ i, (pderiv i p).eval x • proj i` at `x`. -/
theorem mvPoly_eval_hasFDerivAt {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasFDerivAt (fun y : σ → ℝ => MvPolynomial.eval y p)
      (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [sum_eval_pderiv_C]
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (MvPolynomial.C a)) = (fun _ => a) := by
      funext y; simp [MvPolynomial.eval_C]
    rw [hfun]
    exact hasFDerivAt_const (𝕜 := ℝ) a x
  | add p q hp hq =>
    rw [sum_eval_pderiv_add]
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (p + q))
        = (fun y : σ → ℝ => MvPolynomial.eval y p) +
          (fun y : σ → ℝ => MvPolynomial.eval y q) := by
      funext y; simp [MvPolynomial.eval_add]
    rw [hfun]
    exact hp.add hq
  | mul_X p n hp =>
    rw [sum_eval_pderiv_mul_X]
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (p * MvPolynomial.X n))
        = (fun y : σ → ℝ => MvPolynomial.eval y p) *
          (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ) := by
      funext y
      simp [MvPolynomial.eval_mul, MvPolynomial.eval_X, ContinuousLinearMap.proj_apply]
    rw [hfun]
    exact hp.mul (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ))

end Work.WilE9.EaD
