import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE9.Ift.evalMvPoly_hasFDerivAt
import Submission.Work.WilE9.EaD.hasFDerivAt_br

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Ift

open WilkiesDesign WilkiesDesign.E

/-! ## The ambient-dimension computation, from its two ingredients

The chain rule `fderiv_eaEval_append` below needs the ambient-dimension statement
`Work.WilE9.EaD.eaD_hasFDerivAt` (`Submission/Work/WilE9/EaD/eaD_hasFDerivAt.lean`), which is
being proved in parallel.  To keep this file's axiom closure free of the parallel development's
`sorry`s, we re-derive that statement here as a `private` lemma from its two ingredients, which
are already proved:

* `Work.WilE9.Ift.evalMvPoly_hasFDerivAt` (`Submission/Work/WilE9/Ift/evalMvPoly_hasFDerivAt.lean`),
  the derivative of `y ↦ MvPolynomial.eval y Q`;
* `Work.WilE9.EaD.hasFDerivAt_br` (`Submission/Work/WilE9/EaD/hasFDerivAt_br.lean`),
  the derivative of the branch map `x ↦ Sum.elim x (fun j => exp (ℓ_j x))`.
-/

/-- Evaluating the symbolic derivative `eaD c i Q` at the branch point: the `inl i` variable
contributes its partial derivative and each exponential atom `X (inr j)` contributes the factor
`a j i * exp (ell_j v)` times the partial derivative in that atom. -/
private theorem eaEval_eaD_ift {N r : ℕ} (c : EAChain N r) (Q : EAPoly N r)
    (v : Fin N → ℝ) (i : Fin N) :
    MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v))) (eaD c i Q)
      = MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
          (MvPolynomial.pderiv (Sum.inl i) Q)
        + ∑ j, c.a j i * Real.exp (c.ell j v) *
            MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
              (MvPolynomial.pderiv (Sum.inr j) Q) := by
  simp only [eaD, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inr]

/-- The symbolic derivative `eaD c i` computes the partial derivative of `eaEval c Q`. -/
private theorem eaD_hasFDerivAt_ift {N r : ℕ} (c : WilkiesDesign.E.EAChain N r)
    (Q : WilkiesDesign.E.EAPoly N r) (v : Fin N → ℝ) :
    HasFDerivAt (fun w : Fin N → ℝ => WilkiesDesign.E.eaEval c Q w)
      (∑ i, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Q) v) •
        (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) v := by
  classical
  -- `eaEval c Q` is the composition of `MvPolynomial.eval · Q` with the branch map
  -- `x ↦ Sum.elim x (fun j => exp (ell_j x))`.
  have heval := evalMvPoly_hasFDerivAt Q (Sum.elim v (fun j => Real.exp (c.ell j v)))
  have hbr := Work.WilE9.EaD.hasFDerivAt_br c v
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
  -- Both sides are now explicit sums; rewrite the right-hand side with `eaEval_eaD_ift`.
  have hR : (∑ i : Fin N, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
        (eaD c i Q) * w i)
      = ∑ i : Fin N, (MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
            (MvPolynomial.pderiv (Sum.inl i) Q)
          + ∑ j : Fin r, c.a j i * Real.exp (c.ell j v) *
              MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
                (MvPolynomial.pderiv (Sum.inr j) Q)) * w i :=
    Finset.sum_congr rfl fun i _ => by simp only [eaEval_eaD_ift c Q v i]
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

/-! ## The chain rule -/

/-- Chain rule: the derivative of `x ↦ eaEval c P (x, y x)` in terms of the symbolic
derivatives `eaD` in the base and in the fibre directions.

This is the second fundamental ingredient of WilE9 (after `eaD_hasFDerivAt`): every derivative
computation in the implicit-function recursion goes through it.  Note
`Work.WilE9.EaD.eaD_hasFDerivAt` (`Submission/Work/WilE9/EaD/eaD_hasFDerivAt.lean`) is the
ambient-dimension form of the same computation and is being proved in parallel; it may be
imported. -/
theorem fderiv_eaEval_append {n q r : ℕ} (c : WilkiesDesign.E.EAChain (n + q) r)
    (P : WilkiesDesign.E.EAPoly (n + q) r) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (x : Fin n → ℝ) (hy : HasFDerivAt y (fderiv ℝ y x) x) :
    HasFDerivAt (fun x' : Fin n → ℝ => WilkiesDesign.E.eaEval c P (Fin.append x' (y x')))
      ((∑ i : Fin n, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.castAdd q i) P)
            (Fin.append x (y x))) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l : Fin q, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd n l) P)
            (Fin.append x (y x))) •
            ((ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x)))) x := by
  classical
  -- The symbolic derivative of the ambient function `eaEval c P` at the point `(x, y x)`.
  set L : (Fin (n + q) → ℝ) →L[ℝ] ℝ :=
    ∑ s : Fin (n + q),
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c s P) (Fin.append x (y x)) •
        (ContinuousLinearMap.proj s : (Fin (n + q) → ℝ) →L[ℝ] ℝ) with hL
  -- Derivative of the graph map `x' ↦ (x', y x')`.
  have h1 : HasFDerivAt (fun x' : Fin n → ℝ => (x', y x'))
      ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x)) x :=
    (hasFDerivAt_id x).prodMk hy
  -- `Fin.append` is linear, with derivative `appendCLM n q` everywhere.
  have hΦ : HasFDerivAt (fun p : (Fin n → ℝ) × (Fin q → ℝ) => Fin.append p.1 p.2)
      (appendCLM n q) (x, y x) := by
    refine (appendCLM n q).hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with p
    rcases p with ⟨v, w⟩
    exact (appendCLM_apply n q v w).symm
  -- Chain rule for the graph map in the ambient coordinates.
  have hA : HasFDerivAt
      ((fun p : (Fin n → ℝ) × (Fin q → ℝ) => Fin.append p.1 p.2) ∘
        (fun x' : Fin n → ℝ => (x', y x')))
      ((appendCLM n q).comp
        ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x))) x :=
    HasFDerivAt.comp x hΦ h1
  -- The ambient derivative, in terms of `L`.
  have hL' : HasFDerivAt (fun w : Fin (n + q) → ℝ => WilkiesDesign.E.eaEval c P w)
      L (Fin.append x (y x)) := by
    simpa only [hL] using eaD_hasFDerivAt_ift c P (Fin.append x (y x))
  -- Chain rule: the composite of the two calculations above.
  have hK : HasFDerivAt
      ((fun w : Fin (n + q) → ℝ => WilkiesDesign.E.eaEval c P w) ∘
        (fun x' : Fin n → ℝ => Fin.append x' (y x')))
      (L.comp ((appendCLM n q).comp
        ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x)))) x :=
    HasFDerivAt.comp x hL' hA
  -- Split the ambient sum into its base part and its fibre part.
  have hCLM : L.comp ((appendCLM n q).comp
        ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x)))
      = (∑ i : Fin n, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.castAdd q i) P)
            (Fin.append x (y x))) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l : Fin q, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd n l) P)
            (Fin.append x (y x))) •
            ((ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x))) := by
    rw [hL]
    ext v
    -- Evaluate both sides on `v`: the ambient sum becomes a sum over `Fin (n + q)`, which
    -- splits into its base part (in terms of `v`) and its fibre part (in terms of `dy v`).
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.prod_apply, appendCLM_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rfl
  rw [hCLM] at hK
  exact hK

end Work.WilE9.Ift
