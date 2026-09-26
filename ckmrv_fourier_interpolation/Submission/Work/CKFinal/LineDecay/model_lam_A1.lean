import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.model_base
import Submission.Work.CKFinal.LineDecay.model_lam_tools

/-!
# The scalar model identity `i·A1 k = -i·psi1 k·(k+1)`

`A1 k = ∫₀¹ (x+i-1)e^{ikx}dx - ∫₋₁⁰ (x+i+1)e^{ikx}dx` (`model_base.lean`).  Evaluating the
two integrals with the primitive `x ↦ e^{ikx}((x+d)/(ik) + 1/k²)` (for `k ≠ 0`) and combining
with `k²·psi1 k = 2 - 2cos k` gives `A1 k = -(k+1)·psi1 k`, which is the statement below.
The case `k = 0` is evaluated directly.
-/

noncomputable section

open MeasureTheory

namespace Work.CKFinal.LineDecay

/-- `∫₀¹ (x+i-1)e^{ikx}dx = e^{ik}(1/k + 1/k²) - ((1+i)/k + 1/k²)` for `k ≠ 0`. -/
lemma PA_closed (k : ℝ) (hk : k ≠ 0) :
    PA k = Eexp k 1 * (1/(k:ℂ) + 1/(k:ℂ)^2) - ((1+Complex.I)/(k:ℂ) + 1/(k:ℂ)^2) := by
  have hfun : (fun x : ℝ => ((x:ℂ) + Complex.I - 1) * Eexp k x)
      = (fun x : ℝ => ((x:ℂ) + (Complex.I - 1)) * Eexp k x) := by
    funext x; ring
  have h := integral_lin_Eexp k hk (Complex.I - 1) 0 1
  rw [PA, hfun, h]
  simp only [Eexp, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_one, mul_one,
    one_mul]
  field_simp
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

/-- `∫₋₁⁰ (x+i+1)e^{ikx}dx = ((1-i)/k + 1/k²) - e^{-ik}(1/k + 1/k²)` for `k ≠ 0`. -/
lemma PB_closed (k : ℝ) (hk : k ≠ 0) :
    PB k = ((1-Complex.I)/(k:ℂ) + 1/(k:ℂ)^2) - Eexp k (-1) * (1/(k:ℂ) + 1/(k:ℂ)^2) := by
  have hfun : (fun x : ℝ => ((x:ℂ) + Complex.I + 1) * Eexp k x)
      = (fun x : ℝ => ((x:ℂ) + (Complex.I + 1)) * Eexp k x) := by
    funext x; ring
  have h := integral_lin_Eexp k hk (Complex.I + 1) (-1) 0
  rw [PB, hfun, h]
  simp only [Eexp, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_neg,
    Complex.ofReal_one, one_mul]
  field_simp
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

/-- `e^{ik} + e^{-ik} = 2 cos k`. -/
lemma Eexp_add_Eexp_neg (k : ℝ) : Eexp k 1 + Eexp k (-1) = 2 * (Real.cos k : ℂ) := by
  have h1 : Eexp k 1 = Complex.exp ((k:ℂ) * Complex.I) := by
    simp only [Eexp]; congr 1; push_cast; ring
  have h2 : Eexp k (-1) = Complex.exp (-((k:ℂ) * Complex.I)) := by
    simp only [Eexp]; congr 1; push_cast; ring
  rw [h1, h2, Complex.ofReal_cos]
  have ht : 2 * Complex.cos (k:ℂ)
      = Complex.exp ((k:ℂ)*Complex.I) + Complex.exp (-((k:ℂ)*Complex.I)) := by
    rw [Complex.two_cos, neg_mul]
  exact ht.symm

/-- `k²·psi1 k = 2 - 2cos k`, complexified. -/
lemma sq_mul_psi1_complex (k : ℝ) :
    (k:ℂ)^2 * (Work.Asymptotics.psi1 k : ℂ) = 2 - 2*(Real.cos k : ℂ) := by
  have h := Work.Asymptotics.sq_mul_psi1 k
  have h2 : ((k^2 * Work.Asymptotics.psi1 k : ℝ) : ℂ) = ((2 - 2*Real.cos k : ℝ) : ℂ) := by
    rw [h]
  push_cast at h2
  simpa only [Complex.ofReal_cos] using h2

theorem model_lam_A1 (k : ℝ) : Complex.I * A1 k
    = -Complex.I * (Work.Asymptotics.psi1 k : ℂ) * ((k : ℂ) + 1) := by
  rcases eq_or_ne k 0 with rfl | hk
  · -- `k = 0`: both integrals are evaluated by a linear primitive, `A1 0 = -1`, `psi1 0 = 1`.
    have hPA0 : PA 0 = Complex.I - 1/2 := by
      rw [PA]
      have hfun : (fun x : ℝ => ((x:ℂ) + Complex.I - 1) * Eexp 0 x)
          = (fun x : ℝ => ((x:ℂ) + (Complex.I - 1))) := by
        funext x; simp [Eexp]; ring
      rw [hfun, integral_affine (Complex.I - 1) 0 1]
      push_cast; ring
    have hPB0 : PB 0 = Complex.I + 1/2 := by
      rw [PB]
      have hfun : (fun x : ℝ => ((x:ℂ) + Complex.I + 1) * Eexp 0 x)
          = (fun x : ℝ => ((x:ℂ) + (Complex.I + 1))) := by
        funext x; simp [Eexp]; ring
      rw [hfun, integral_affine (Complex.I + 1) (-1) 0]
      push_cast; ring
    have hA10 : A1 0 = -1 := by rw [A1, hPA0, hPB0]; ring
    rw [hA10, Work.Asymptotics.psi1_zero]
    push_cast; ring
  · -- `k ≠ 0`: the two closed forms combine to `A1 k = (e^{ik}+e^{-ik}-2)(k+1)/k²`.
    have hk' : (k:ℂ) ≠ 0 := by exact_mod_cast hk
    have hA1 : A1 k = (Eexp k 1 + Eexp k (-1) - 2) * ((k:ℂ)+1)/(k:ℂ)^2 := by
      rw [A1, PA_closed k hk, PB_closed k hk]
      field_simp
      ring
    have hEsum : Eexp k 1 + Eexp k (-1) - 2
        = -((k:ℂ)^2 * (Work.Asymptotics.psi1 k : ℂ)) := by
      rw [Eexp_add_Eexp_neg k, sq_mul_psi1_complex k]; ring
    rw [hA1, hEsum]
    field_simp [hk']
    try ring

end Work.CKFinal.LineDecay
