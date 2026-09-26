import Mathlib
import Submission.Work.CKFinal.LineDecay.model_base

/-!
# Calculus tools for the two scalar model identities of the line-decay computation

The scalar identities of `LineDecay/model_base.lean`,
`i·A0 k = -k·psi1 k` and `i·A1 k = -i·psi1 k·(k+1)`, are evaluations of the four elementary
integrals `QA, QB, PA, PB`.  This file collects the primitive formulas those evaluations need.

* `integral_lin_exp` — `∫ₐᵇ (x+d)e^{cx}dx` for `c ≠ 0`;
* `integral_lin_Eexp` — the same with the `Eexp` integrand `(x+d)e^{ikx}`, `k ≠ 0`;
* `integral_ofReal_id` — `∫ₐᵇ x dx` for a complex-valued integrand;
* `integral_affine` — `∫ₐᵇ (x+d)dx`.
-/

noncomputable section

open MeasureTheory

namespace Work.CKFinal.LineDecay

/-- `∫ₐᵇ (x+d)e^{cx}dx = e^{cb}((b+d)/c - 1/c²) - e^{ca}((a+d)/c - 1/c²)` for `c ≠ 0`
(the primitive being `x ↦ e^{cx}((x+d)/c - 1/c²)`). -/
lemma integral_lin_exp (c d : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, ((x : ℂ) + d) * Complex.exp (c * (x : ℂ))
      = Complex.exp (c * (b:ℂ)) * (((b : ℂ) + d) / c - 1 / c ^ 2)
        - Complex.exp (c * (a:ℂ)) * (((a : ℂ) + d) / c - 1 / c ^ 2) := by
  have key : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Complex.exp (c * (y:ℂ)) * (((y:ℂ) + d)/c - 1/c^2))
        (((x:ℂ) + d) * Complex.exp (c * (x:ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (c * (y:ℂ)))
        (Complex.exp (c*(x:ℂ)) * c) x := by
      have h := ((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul c).cexp
      simpa using h
    have h2 : HasDerivAt (fun y : ℝ => (((y:ℂ) + d)/c - 1/c^2)) (1/c) x := by
      have h := ((Complex.ofRealCLM.hasDerivAt (x:=x)).add_const d).div_const c
      have h' := h.sub_const (1/c^2)
      simpa using h'
    refine (h1.mul h2).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key (by
    apply Continuous.intervalIntegrable
    fun_prop)]

/-- The `Eexp` version of `integral_lin_exp`. -/
lemma integral_lin_Eexp (k : ℝ) (hk : k ≠ 0) (d : ℂ) (a b : ℝ) :
    ∫ x in a..b, ((x : ℂ) + d) * Eexp k x
      = Eexp k b * (((b : ℂ) + d) / (Complex.I * (k:ℂ)) - 1 / (Complex.I * (k:ℂ)) ^ 2)
        - Eexp k a * (((a : ℂ) + d) / (Complex.I * (k:ℂ)) - 1 / (Complex.I * (k:ℂ)) ^ 2) := by
  have hk' : (k:ℂ) ≠ 0 := by exact_mod_cast hk
  have key : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ =>
          Complex.exp ((Complex.I * (k:ℂ)) * (y:ℂ))
            * (((y:ℂ) + d)/(Complex.I * (k:ℂ)) - 1/(Complex.I * (k:ℂ))^2))
        (((x:ℂ) + d) * Complex.exp ((Complex.I * (k:ℂ)) * (x:ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp ((Complex.I * (k:ℂ)) * (y:ℂ)))
        (Complex.exp ((Complex.I * (k:ℂ))*(x:ℂ)) * (Complex.I * (k:ℂ))) x := by
      have h := ((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul (Complex.I * (k:ℂ))).cexp
      simpa using h
    have h2 : HasDerivAt
        (fun y : ℝ => (((y:ℂ) + d)/(Complex.I * (k:ℂ)) - 1/(Complex.I * (k:ℂ))^2))
        (1/(Complex.I * (k:ℂ))) x := by
      have h := ((Complex.ofRealCLM.hasDerivAt (x:=x)).add_const d).div_const (Complex.I * (k:ℂ))
      have h' := h.sub_const (1/(Complex.I * (k:ℂ))^2)
      simpa using h'
    refine (h1.mul h2).congr_deriv ?_
    field_simp [hk']
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt key (by
    apply Continuous.intervalIntegrable
    fun_prop)
  simpa only [Eexp] using h

/-- `∫ₐᵇ x dx` for a complex-valued integrand, `x` real. -/
lemma integral_ofReal_id (a b : ℝ) :
    (∫ x in a..b, ((x : ℝ) : ℂ)) = (((b:ℂ)^2 - (a:ℂ)^2)/2) := by
  have h : (∫ x in a..b, ((x:ℝ):ℂ)) = ((∫ x in a..b, x : ℝ) : ℂ) := by
    simpa using (intervalIntegral.integral_ofReal (a := a) (b := b) (f := fun x : ℝ => x)
      (μ := volume))
  rw [h, integral_id]
  push_cast
  ring

/-- `∫ₐᵇ (x+d)dx = (b²/2 + d b) - (a²/2 + d a)`. -/
lemma integral_affine (d : ℂ) (a b : ℝ) :
    ∫ x in a..b, ((x : ℂ) + d) = ((b:ℂ)^2/2 + d*(b:ℂ)) - ((a:ℂ)^2/2 + d*(a:ℂ)) := by
  have hsplit : ∫ x in a..b, ((x:ℂ) + d)
      = (∫ x in a..b, ((x:ℝ):ℂ)) + ∫ x in a..b, d := by
    rw [intervalIntegral.integral_add]
    · exact (by fun_prop : Continuous fun x : ℝ => ((x:ℝ):ℂ)).intervalIntegrable a b
    · exact continuous_const.intervalIntegrable a b
  rw [hsplit, integral_ofReal_id, intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

end Work.CKFinal.LineDecay
