import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.EaD.mvPoly_eval_hasFDerivAt
import Submission.Work.WilE9.EaD.hasFDerivAt_br

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology

namespace Work.WilE9.EaD
open WilkiesDesign WilkiesDesign.E

/-- Evaluating the symbolic derivative `eaD c i Q` at the branch point: the `inl i` variable
contributes its partial derivative and each exponential atom `X (inr j)` contributes the factor
`a j i * exp (ell_j v)` times the partial derivative in that atom. -/
theorem eaEval_eaD {N r : ℕ} (c : EAChain N r) (Q : EAPoly N r) (v : Fin N → ℝ) (i : Fin N) :
    MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v))) (eaD c i Q)
      = MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
          (MvPolynomial.pderiv (Sum.inl i) Q)
        + ∑ j, c.a j i * Real.exp (c.ell j v) *
            MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
              (MvPolynomial.pderiv (Sum.inr j) Q) := by
  simp only [eaD, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inr]

/-- The symbolic derivative `eaD c i` computes the partial derivative of `eaEval c Q`. -/
theorem eaD_hasFDerivAt {N r : ℕ} (c : WilkiesDesign.E.EAChain N r)
    (Q : WilkiesDesign.E.EAPoly N r) (v : Fin N → ℝ) :
    HasFDerivAt (fun w : Fin N → ℝ => WilkiesDesign.E.eaEval c Q w)
      (∑ i, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Q) v) •
        (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) v := by
  classical
  -- `eaEval c Q` is the composition of `MvPolynomial.eval · Q` with the branch map
  -- `x ↦ Sum.elim x (fun j => exp (ell_j x))`.
  have heval := mvPoly_eval_hasFDerivAt Q (Sum.elim v (fun j => Real.exp (c.ell j v)))
  have hbr := hasFDerivAt_br c v
  have hcomp := heval.comp v hbr
  have hfun : (fun w : Fin N → ℝ => eaEval c Q w)
      = (fun y : Fin N ⊕ Fin r → ℝ => MvPolynomial.eval y Q) ∘
          (fun x : Fin N → ℝ => Sum.elim x (fun j => Real.exp (c.ell j x))) := rfl
  rw [hfun]
  refine hcomp.congr_fderiv ?_
  -- It remains to identify the derivative supplied by the chain rule with the claimed one.
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.pi_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply, smul_eq_mul, eaEval]
  -- Both sides are now explicit sums; rewrite the right-hand side with `eaEval_eaD`.
  have hR : (∑ i : Fin N, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
        (eaD c i Q) * w i)
      = ∑ i : Fin N, (MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
            (MvPolynomial.pderiv (Sum.inl i) Q)
          + ∑ j : Fin r, c.a j i * Real.exp (c.ell j v) *
              MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
                (MvPolynomial.pderiv (Sum.inr j) Q)) * w i :=
    Finset.sum_congr rfl fun i _ => by simp only [eaEval_eaD c Q v i]
  rw [hR]
  -- Pull the `j`-sum out of the product and reorder the two sums.
  have hswap : (∑ j : Fin r, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
          (MvPolynomial.pderiv (Sum.inr j) Q) *
        (Real.exp (c.ell j v) * ∑ i : Fin N, c.a j i * w i))
      = ∑ i : Fin N, ∑ j : Fin r,
          MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
            (MvPolynomial.pderiv (Sum.inr j) Q) *
          (Real.exp (c.ell j v) * (c.a j i * w i)) := by
    have h1 : ∀ j : Fin r, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
          (MvPolynomial.pderiv (Sum.inr j) Q) *
        (Real.exp (c.ell j v) * ∑ i : Fin N, c.a j i * w i)
        = ∑ i : Fin N, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
            (MvPolynomial.pderiv (Sum.inr j) Q) *
          (Real.exp (c.ell j v) * (c.a j i * w i)) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_mul, Finset.sum_mul]
  exact congrArg
    (fun t => MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
      (MvPolynomial.pderiv (Sum.inl i) Q) * w i + t)
    (Finset.sum_congr rfl fun j _ => by ring)

end Work.WilE9.EaD
