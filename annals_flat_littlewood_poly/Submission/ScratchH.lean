import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

/-- exp(c·x) is smooth -/
lemma exp_c_mul_contDiff {n : WithTop ℕ∞} (c : ℂ) :
    ContDiff ℝ n (fun x : ℝ => Complex.exp (c * (x : ℂ))) := by
  let L : ℝ →L[ℝ] ℂ := ((ContinuousLinearMap.mul ℝ ℂ) c).comp Complex.ofRealCLM
  have hL : ContDiff ℝ n (L : ℝ → ℂ) := ContinuousLinearMap.contDiff L
  have hexp : ContDiff ℝ n (Complex.exp : ℂ → ℂ) :=
    (Complex.contDiff_exp : ContDiff ℂ n (Complex.exp : ℂ → ℂ)).restrict_scalars ℝ
  have h : ContDiff ℝ n (fun x : ℝ => Complex.exp (L x)) := by
    change ContDiff ℝ n (Complex.exp ∘ (L : ℝ → ℂ))
    exact hexp.comp hL
  convert h using 1
  ext x
  exact congrArg Complex.exp (by simp [L, ContinuousLinearMap.mul_apply'])

/-- `e^{ix}` is smooth -/
lemma contDiff_eθ {n : WithTop ℕ∞} : ContDiff ℝ n (fun x : ℝ => Sec3.eθ x) := by
  have h := exp_c_mul_contDiff (n := n) Complex.I
  unfold Sec3.eθ
  convert h using 1
  ext x
  ring

/-- `e^{icx}` is smooth -/
lemma contDiff_eθ_mul {n : WithTop ℕ∞} (c : ℝ) : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (c * x)) := by
  have h := exp_c_mul_contDiff (n := n) (((c : ℂ) * Complex.I))
  -- h : ContDiff (fun x => exp (((c : ℂ) * I) * (x:ℂ)))
  unfold Sec3.eθ
  convert h using 1
  ext x
  apply congrArg Complex.exp
  rw [Complex.ofReal_mul]
  ring

/-- polynomial-eval is smooth on ℂ (as function of a complex variable over ℝ) -/
lemma polyEval_contDiff {n : WithTop ℕ∞} (Q : ℂ[X]) : ContDiff ℝ n (fun z : ℂ => Q.eval z) := by
  simpa using ((Polynomial.contDiff_aeval (R := ℂ) (𝕜 := ℂ) Q n).restrict_scalars ℝ)

/-- Q.eval(eθ x) is smooth -/
lemma contDiff_poly_eθ {n : WithTop ℕ∞} (Q : ℂ[X]) : ContDiff ℝ n (fun x : ℝ => Q.eval (Sec3.eθ x)) := by
  have h1 := polyEval_contDiff (n := n) Q
  have h2 := contDiff_eθ (n := n)
  -- (fun x => Q.eval (eθ x)) = (fun z => Q.eval z) ∘ eθ
  change ContDiff ℝ n ((fun z : ℂ => Q.eval z) ∘ (fun x : ℝ => Sec3.eθ x))
  exact h1.comp h2

/-- alpha is smooth -/
lemma contDiff_alpha {n : WithTop ℕ∞} (t : ℕ) : ContDiff ℝ n (fun x : ℝ => alpha t x) := by
  -- alpha t x = (scale t : ℂ) * (P.eval (eθ (x / T))) : write x / T = (T:ℝ)⁻¹ * x
  have hmain : ContDiff ℝ n (fun x : ℝ => (RudinShapiro.P t).eval (Sec3.eθ (x / (T t : ℝ)))) := by
    -- x/(T:ℝ) = (T:ℝ)⁻¹ * x ; compose eθ with real-linear
    have hin : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (((T t : ℝ)⁻¹) * x)) := by
      have h := contDiff_eθ_mul (n := n) ((T t : ℝ)⁻¹)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hq := polyEval_contDiff (n := n) (RudinShapiro.P t)
    change ContDiff ℝ n ((fun z : ℂ => (RudinShapiro.P t).eval z) ∘ (fun x : ℝ => Sec3.eθ (x / (T t : ℝ))))
    apply hq.comp
    -- the inner function (fun x => eθ (x / (T t : ℝ))) equals (fun x => eθ (((T t : ℝ)⁻¹) * x))
    simpa [div_eq_mul_inv, mul_comm] using hin
  -- multiply by constant (scale : ℂ)
  have hc : ContDiff ℝ n (fun _ : ℝ => (scale t : ℂ)) := contDiff_const
  have hprod := hc.mul hmain
  unfold alpha
  exact hprod

end Submission.Sec3H
