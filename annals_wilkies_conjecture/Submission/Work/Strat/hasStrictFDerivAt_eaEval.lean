import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.Strat

open WilkiesDesign WilkiesDesign.E

/-!
## Strict Fréchet derivative of `eaEval`

`eaEval c Q x` is the evaluation of the EA-polynomial `Q` at the point `(x, exp (ℓ_j x))`, hence a
composition of the (smooth) polynomial map with the (smooth) exponential of affine forms; the
symbolic operator `eaD c i` is its total derivative along the `i`-th coordinate, which is proved to
be the Fréchet derivative in `Work.WilE5.Calc.hasFDerivAt_eaEval`.

Here we upgrade this to a *strict* Fréchet derivative. The argument is the same induction on `Q`
(`MvPolynomial.induction_on`), this time using the strict-derivative API throughout: strict
differentiability is closed under sums, products, composition with `Real.exp` and the addition of
constants, and the coordinate projections are strictly differentiable.

The auxiliary lemma `hasStrictFDerivAt_eaEval_X` treats the two kinds of variable.
-/

/-- The affine forms `ℓ_j` are strictly differentiable, with derivative the linear form
`ellLin c j`. -/
private theorem hasStrictFDerivAt_ell {k r : ℕ} (c : EAChain k r) (j : Fin r)
    (x : Fin k → ℝ) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => c.ell j z) (Work.WilE5.Calc.ellLin c j) x := by
  rw [show (fun z : Fin k → ℝ => c.ell j z)
      = fun z => c.b j + (Work.WilE5.Calc.ellLin c j) z from
    funext fun z => Work.WilE5.Calc.ell_eq c j z]
  exact (ContinuousLinearMap.hasStrictFDerivAt (Work.WilE5.Calc.ellLin c j)).const_add (c.b j)

/-- The variables of the EA ring are strictly differentiable, with derivative `eaEvalD` at the
variable. -/
private theorem hasStrictFDerivAt_eaEval_X {k r : ℕ} (c : EAChain k r) (n : Fin k ⊕ Fin r)
    (x : Fin k → ℝ) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => eaEval c (MvPolynomial.X n) z)
      (Work.WilE5.Calc.eaEvalD c (MvPolynomial.X n) x) x := by
  rcases n with i | j
  · rw [Work.WilE5.Calc.eaEvalD_X_inl]
    rw [show (fun z : Fin k → ℝ => eaEval c (MvPolynomial.X (Sum.inl i)) z) = fun z => z i from
      funext fun z => Work.WilE5.Calc.eaEval_X_inl' c i z]
    exact ContinuousLinearMap.hasStrictFDerivAt
      (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)
  · rw [Work.WilE5.Calc.eaEvalD_X_inr]
    rw [show (fun z : Fin k → ℝ => eaEval c (MvPolynomial.X (Sum.inr j)) z)
        = fun z => Real.exp (c.ell j z) from
      funext fun z => Work.WilE5.Calc.eaEval_X_inr' c j z]
    exact (hasStrictFDerivAt_ell c j x).exp

theorem hasStrictFDerivAt_eaEval {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Q : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Q z)
      ((∑ i : Fin k, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Q) x) •
        ContinuousLinearMap.proj i) : (Fin k → ℝ) →L[ℝ] ℝ) x := by
  show HasStrictFDerivAt (fun z : Fin k → ℝ => eaEval c Q z) (Work.WilE5.Calc.eaEvalD c Q x) x
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [Work.WilE5.Calc.eaEvalD_C]
    rw [show (fun z : Fin k → ℝ => eaEval c (MvPolynomial.C a) z) = fun _ => a from
      funext fun z => Work.WilE5.Calc.eaEval_C' c a z]
    exact hasStrictFDerivAt_const a x
  | add p q hp hq =>
    rw [Work.WilE5.Calc.eaEvalD_add]
    refine (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only [Work.WilE5.Calc.eaEval_add', Pi.add_apply]
  | mul_X p n hp =>
    rw [Work.WilE5.Calc.eaEvalD_mul_X]
    refine (hp.mul (hasStrictFDerivAt_eaEval_X c n x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Work.WilE5.Calc.eaEval_mul', Pi.mul_apply]

end Work.Strat
