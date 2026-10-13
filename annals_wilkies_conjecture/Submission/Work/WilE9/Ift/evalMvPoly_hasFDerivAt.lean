import Mathlib

set_option autoImplicit false

namespace Work.WilE9.Ift

/-- The evaluation of the "delta" polynomial `Pi.single i 1`. -/
theorem eval_piSingle {σ : Type*} [DecidableEq σ] (x : σ → ℝ) (i n : σ) :
    MvPolynomial.eval x
        (Pi.single (M := fun _ => MvPolynomial σ ℝ) i (1 : MvPolynomial σ ℝ) n)
      = Pi.single (M := fun _ => ℝ) i (1 : ℝ) n := by
  by_cases h : n = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- The derivative of a multivariate polynomial function: for `p : MvPolynomial σ ℝ` the map
`y ↦ p.eval y` has derivative `∑ i, (pderiv i p).eval x • proj i` at `x`. -/
theorem evalMvPoly_hasFDerivAt {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasFDerivAt (fun y : σ → ℝ => MvPolynomial.eval y p)
      (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (MvPolynomial.C a)) = fun _ => a := by
      funext y; simp
    rw [hfun]
    have hsum : (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.C a))) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) = 0 := by
      simp
    rw [hsum]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (p + q))
        = (fun y : σ → ℝ => MvPolynomial.eval y p)
          + (fun y : σ → ℝ => MvPolynomial.eval y q) := by
      funext y; simp [MvPolynomial.eval_add]
    rw [hfun]
    refine (hp.add hq).congr_fderiv ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add (MvPolynomial.pderiv i) p q, MvPolynomial.eval_add, add_smul]
  | mul_X p n hp =>
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (p * MvPolynomial.X n))
        = (fun y : σ → ℝ => MvPolynomial.eval y p) * (fun y : σ → ℝ => y n) := by
      funext y; simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    rw [hfun]
    have hn : HasFDerivAt (fun y : σ → ℝ => y n)
        (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply n x
    refine (hp.mul hn).congr_fderiv ?_
    have hsplit : (∑ i : σ,
          (MvPolynomial.eval x (MvPolynomial.pderiv i (p * MvPolynomial.X n))) •
            (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
        = (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i p) * x n) •
              (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
          + (∑ i : σ, (MvPolynomial.eval x p * Pi.single (M := fun _ => ℝ) i (1 : ℝ) n) •
              (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.pderiv_X, eval_piSingle,
        add_smul]
    have hfac : (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i p) * x n) •
          (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
        = x n • (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
            (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, mul_comm]
    have hdelta : (∑ i : σ,
          (MvPolynomial.eval x p * Pi.single (M := fun _ => ℝ) i (1 : ℝ) n) •
            (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
        = MvPolynomial.eval x p • (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero, zero_smul]
      · intro h; exact absurd (Finset.mem_univ n) h
    rw [hsplit, hfac, hdelta, add_comm]

end Work.WilE9.Ift
