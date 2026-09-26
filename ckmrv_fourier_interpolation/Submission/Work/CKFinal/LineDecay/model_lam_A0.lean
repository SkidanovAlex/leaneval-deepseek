import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.model_base
import Submission.Work.CKFinal.LineDecay.sint_cint

/-!
# The model identity `i·A₀(k) = -k·ψ₁(k)` of the line-decay computation

With `A₀(k) = ∫₀¹ e^{ikx} dx - ∫₋₁⁰ e^{ikx} dx` and `ψ₁(k) = 2∫₀¹ (1-s) cos(sk) ds`, both
sides reduce to the single real quantity `-2∫₀¹ sin(kx) dx`:

* the complex side comes from the substitution `x ↦ -x` on `∫₋₁⁰ e^{ikx}dx`, which turns it
  into `∫₀¹ e^{-ikx}dx`, together with the pointwise identity `e^{ikx} - e^{-ikx} = 2i sin(kx)`;
* the real side comes from `k∫₀¹(1-s)cos(sk)ds = ∫₀¹ sin(kx)dx` (integration by parts, with no
  division by `k`, so it is valid also at `k = 0`), the identity `sint_cint`.
-/

noncomputable section

open MeasureTheory

namespace Work.CKFinal.LineDecay

/-- The pointwise identity `e^{ikx} - e^{-ikx} = 2i sin(kx)` for real `k, x`. -/
private lemma exp_sub_exp (k x : ℝ) :
    Complex.exp (Complex.I * (k:ℂ) * (x:ℂ)) - Complex.exp (-(Complex.I * (k:ℂ) * (x:ℂ)))
      = 2 * Complex.I * (Real.sin (k*x) : ℂ) := by
  have h : Complex.I * (k:ℂ) * (x:ℂ) = ((k*x:ℝ):ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.ofReal_sin (k*x), Complex.sin]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The complex side of the model identity: `i·A₀(k) = -2∫₀¹ sin(kx)dx`. -/
private lemma I_mul_A0 (k : ℝ) :
    Complex.I * A0 k = ((-2 * (∫ x in (0:ℝ)..1, Real.sin (k*x))) : ℂ) := by
  -- rewrite the `QB` integral over `[-1,0]` as the integral of `e^{-ikx}` over `[0,1]`
  have hQB : QB k = ∫ x in (0:ℝ)..1, Complex.exp (-(Complex.I * (k:ℂ) * (x:ℂ))) := by
    unfold QB Eexp
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := (1:ℝ))
          (f := fun x : ℝ => Complex.exp (Complex.I * (k:ℂ) * (x:ℂ)))
    simp only [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only []
    congr 1
    push_cast
    ring
  have hcont1 : Continuous (fun x : ℝ => Complex.exp (Complex.I * (k:ℂ) * (x:ℂ))) := by fun_prop
  have hcont2 : Continuous (fun x : ℝ => Complex.exp (-(Complex.I * (k:ℂ) * (x:ℂ)))) := by fun_prop
  -- combine `QA - QB` into a single integral of the difference
  have hA0 : A0 k = ∫ x in (0:ℝ)..1,
      (Complex.exp (Complex.I*(k:ℂ)*(x:ℂ)) - Complex.exp (-(Complex.I*(k:ℂ)*(x:ℂ)))) := by
    rw [A0, hQB]
    simp only [QA, Eexp]
    rw [intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)]
  rw [hA0, ← intervalIntegral.integral_const_mul]
  -- move `i` inside and replace the integrand by `-2 sin(kx)`
  rw [show (∫ x in (0:ℝ)..1, Complex.I * (Complex.exp (Complex.I*(k:ℂ)*(x:ℂ)) - Complex.exp (-(Complex.I*(k:ℂ)*(x:ℂ)))))
      = ∫ x in (0:ℝ)..1, ((-2 : ℂ) * (Real.sin (k*x) : ℂ)) from by
    apply intervalIntegral.integral_congr
    intro x _
    simp only []
    rw [exp_sub_exp k x]
    ring_nf
    rw [Complex.I_sq]
    ring]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

/-- The real side of the model identity: `-k·ψ₁(k) = -2∫₀¹ sin(kx)dx`. -/
private lemma neg_mul_psi1 (k : ℝ) :
    -(k : ℂ) * (Work.Asymptotics.psi1 k : ℂ)
      = ((-2 * (∫ x in (0:ℝ)..1, Real.sin (k*x))) : ℂ) := by
  have hreal : -(k * Work.Asymptotics.psi1 k) = -2 * (∫ x in (0:ℝ)..1, Real.sin (k*x)) := by
    rw [Work.Asymptotics.psi1]
    rw [show k * (2 * (∫ s in (0:ℝ)..1, (1 - s) * Real.cos (s * k)))
          = 2 * (k * (∫ s in (0:ℝ)..1, (1 - s) * Real.cos (s * k))) by ring, sint_cint k]
    ring
  rw [neg_mul, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
  rw [show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_mul]
  rw [Complex.ofReal_inj]
  exact hreal

theorem model_lam_A0 (k : ℝ) : Complex.I * A0 k = -(k : ℂ) * (Work.Asymptotics.psi1 k : ℂ) := by
  rw [I_mul_A0 k, neg_mul_psi1 k]

end Work.CKFinal.LineDecay
