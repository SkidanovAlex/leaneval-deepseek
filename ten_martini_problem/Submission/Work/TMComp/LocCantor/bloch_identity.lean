import Mathlib
import Submission.Work.TMComp.LocCantor.Defs

/-!
# Bloch identity for the Fourier transform of a decaying eigenfunction

Let `u : ℤ → ℂ` decay exponentially and satisfy the almost Mathieu recurrence
`u(n+1) + u(n-1) + 2λ cos 2π(θ+nα) u(n) = E u(n)`.  Then its Fourier transform
`U(x) = Σ_n u_n e^{2πinx}` satisfies

`(e^{-2πix} + e^{2πix}) U(x) + λ e^{2πiθ} U(x+α) + λ e^{-2πiθ} U(x-α) = E U(x)`.

This is the Fourier transform of the recurrence (AJ §5, equation preceding (5.9)):
the shift `u_{n±1}` produces the factors `e^{∓2πix}` while the potential splits into
`λ e^{2πiθ} U(x+α) + λ e^{-2πiθ} U(x-α)`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Filter Topology Set

namespace Work.TMComp.LocCantor

open Work.TMContract

/-- The phase `e^{2πinx}` of the `n`-th Fourier mode at frequency `x`. -/
def blochAux_phase (x : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * (n : ℝ) * x * Complex.I)

@[simp] theorem blochAux_norm_phase (x : ℝ) (n : ℤ) : ‖blochAux_phase x n‖ = 1 := by
  rw [blochAux_phase, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The Fourier sum is `∑_n u_n e^{2πinx}`. -/
theorem blochAux_fourier_eq (u : ℤ → ℂ) (x : ℝ) :
    Work.TMComp.fourier u x = ∑' n : ℤ, u n * blochAux_phase x n := rfl

/-- `∑_{n:ℤ} e^{-c|n|}` converges for `c > 0`. -/
theorem blochAux_summable_exp_neg_abs (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-(c * |(n : ℝ)|))) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  constructor
  · refine (summable_geometric_of_norm_lt_one hr).congr ?_
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    rw [abs_of_nonneg (by positivity)]
    push_cast; ring
  · refine (summable_geometric_of_norm_lt_one hr).congr ?_
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    have h : ((↑(-↑n) : ℤ) : ℝ) = -(n : ℝ) := by push_cast; ring
    rw [h, abs_neg, abs_of_nonneg (by positivity)]
    ring

/-- Exponential decay makes the Fourier series absolutely convergent. -/
theorem blochAux_summable_fourier (u : ℤ → ℂ) (hu : ExpDecay u) (x : ℝ) :
    Summable (fun n : ℤ => u n * blochAux_phase x n) := by
  obtain ⟨c, hc, C, hC⟩ := hu
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (Summable.mul_left (max C 0) (blochAux_summable_exp_neg_abs c hc))
  rw [norm_mul, blochAux_norm_phase, mul_one]
  calc ‖u n‖ ≤ C * Real.exp (-(c * |(n : ℝ)|)) := hC n
    _ ≤ max C 0 * Real.exp (-(c * |(n : ℝ)|)) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _)

theorem blochAux_hasSum_fourier (u : ℤ → ℂ) (hu : ExpDecay u) (x : ℝ) :
    HasSum (fun n : ℤ => u n * blochAux_phase x n) (Work.TMComp.fourier u x) :=
  (blochAux_summable_fourier u hu x).hasSum

/-- `e^{-2πix} e^{2πi(n+1)x} = e^{2πinx}`. -/
theorem blochAux_exp_neg_mul_phase_add_one (x : ℝ) (n : ℤ) :
    Complex.exp (-(2 * Real.pi * x * Complex.I)) * blochAux_phase x (n + 1)
      = blochAux_phase x n := by
  rw [blochAux_phase, blochAux_phase]
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

/-- `e^{2πix} e^{2πi(n-1)x} = e^{2πinx}`. -/
theorem blochAux_exp_mul_phase_sub_one (x : ℝ) (n : ℤ) :
    Complex.exp (2 * Real.pi * x * Complex.I) * blochAux_phase x (n - 1)
      = blochAux_phase x n := by
  rw [blochAux_phase, blochAux_phase]
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

/-- `2 cos y = e^{iy} + e^{-iy}`. -/
theorem blochAux_ofReal_two_cos (y : ℝ) :
    ((2 * Real.cos y : ℝ) : ℂ) = Complex.exp (y * Complex.I) + Complex.exp (-(y * Complex.I)) := by
  have h1 : Complex.exp (y * Complex.I) =
      ((Real.cos y : ℝ) : ℂ) + ((Real.sin y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h2 : Complex.exp (-(y * Complex.I)) =
      ((Real.cos y : ℝ) : ℂ) - ((Real.sin y : ℝ) : ℂ) * Complex.I := by
    rw [show -(y * Complex.I) = (-y) * Complex.I by ring, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [h1, h2]
  push_cast
  ring

/-- The potential expressed through phases. -/
theorem blochAux_amoPot_eq (α lam θ : ℝ) (n : ℤ) :
    ((amoPot α lam θ n : ℝ) : ℂ)
      = lam * (Complex.exp (2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I)
               + Complex.exp (-(2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I))) := by
  rw [amoPot]
  rw [show (2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ)
        = lam * (2 * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))) by ring]
  rw [Complex.ofReal_mul, blochAux_ofReal_two_cos]
  push_cast; ring

/-- Positive phase shift in the potential. -/
theorem blochAux_exp_theta_alpha_mul_phase (α θ x : ℝ) (n : ℤ) :
    Complex.exp (2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I) * blochAux_phase x n
      = Complex.exp (2 * Real.pi * θ * Complex.I) * blochAux_phase (x + α) n := by
  rw [blochAux_phase, blochAux_phase]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Negative phase shift in the potential. -/
theorem blochAux_exp_neg_theta_alpha_mul_phase (α θ x : ℝ) (n : ℤ) :
    Complex.exp (-(2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I)) * blochAux_phase x n
      = Complex.exp (-(2 * Real.pi * θ * Complex.I)) * blochAux_phase (x - α) n := by
  rw [blochAux_phase, blochAux_phase]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- The potential term of the recurrence, factorised through the shifted phases. -/
theorem blochAux_amoPot_phase (α lam θ x : ℝ) (c : ℂ) (n : ℤ) :
    ((amoPot α lam θ n : ℝ) : ℂ) * c * blochAux_phase x n
      = lam * (Complex.exp (2 * Real.pi * θ * Complex.I) * (c * blochAux_phase (x + α) n)
               + Complex.exp (-(2 * Real.pi * θ * Complex.I)) * (c * blochAux_phase (x - α) n)) := by
  rw [blochAux_amoPot_eq α lam θ n]
  rw [show lam * (Complex.exp (2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I)
          + Complex.exp (-(2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I))) * c * blochAux_phase x n
        = lam * (c * (Complex.exp (2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I)
                * blochAux_phase x n)
               + c * (Complex.exp (-(2 * Real.pi * (θ + (n : ℝ) * α) * Complex.I))
                * blochAux_phase x n)) by ring]
  rw [blochAux_exp_theta_alpha_mul_phase α θ x n, blochAux_exp_neg_theta_alpha_mul_phase α θ x n]
  ring

theorem bloch_identity {α lam θ E : ℝ} {u : ℤ → ℂ} (hu : Work.TMContract.ExpDecay u)
    (hrec : ∀ n : ℤ, Work.TMContract.amoAct α lam θ u n = (E : ℂ) * u n) :
    ∀ x : ℝ, (Complex.exp (-(2 * Real.pi * x * Complex.I)) + Complex.exp (2 * Real.pi * x * Complex.I)) * Work.TMComp.fourier u x
      + lam * Complex.exp (2 * Real.pi * θ * Complex.I) * Work.TMComp.fourier u (x + α)
      + lam * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * Work.TMComp.fourier u (x - α)
      = (E : ℂ) * Work.TMComp.fourier u x := by
  intro x
  have hF : ∀ y : ℝ, HasSum (fun n : ℤ => u n * blochAux_phase y n) (Work.TMComp.fourier u y) :=
    fun y => blochAux_hasSum_fourier u hu y
  have hA : HasSum (fun n : ℤ => Complex.exp (-(2 * Real.pi * x * Complex.I))
        * (u (n + 1) * blochAux_phase x (n + 1)))
      (Complex.exp (-(2 * Real.pi * x * Complex.I)) * Work.TMComp.fourier u x) := by
    have h0 : HasSum (fun n : ℤ => u (n + 1) * blochAux_phase x (n + 1))
        (Work.TMComp.fourier u x) :=
      (Equiv.hasSum_iff (Equiv.addRight (1 : ℤ)) (f := fun m => u m * blochAux_phase x m)).mpr
        (hF x)
    exact h0.mul_left _
  have hB : HasSum (fun n : ℤ => Complex.exp (2 * Real.pi * x * Complex.I)
        * (u (n - 1) * blochAux_phase x (n - 1)))
      (Complex.exp (2 * Real.pi * x * Complex.I) * Work.TMComp.fourier u x) := by
    have h0 : HasSum (fun n : ℤ => u (n - 1) * blochAux_phase x (n - 1))
        (Work.TMComp.fourier u x) :=
      (Equiv.hasSum_iff (Equiv.addRight (-1 : ℤ)) (f := fun m => u m * blochAux_phase x m)).mpr
        (hF x)
    exact h0.mul_left _
  have hD : HasSum (fun n : ℤ => ((amoPot α lam θ n : ℝ) : ℂ) * u n * blochAux_phase x n)
      (lam * (Complex.exp (2 * Real.pi * θ * Complex.I) * Work.TMComp.fourier u (x + α)
              + Complex.exp (-(2 * Real.pi * θ * Complex.I)) * Work.TMComp.fourier u (x - α))) := by
    have h1 := (hF (x + α)).mul_left (Complex.exp (2 * Real.pi * θ * Complex.I))
    have h2 := (hF (x - α)).mul_left (Complex.exp (-(2 * Real.pi * θ * Complex.I)))
    have h3 := (h1.add h2).mul_left (lam : ℂ)
    refine h3.congr_fun (fun n => ?_)
    rw [blochAux_amoPot_phase α lam θ x (u n) n]
  have hABD : HasSum (fun n : ℤ => (Complex.exp (-(2 * Real.pi * x * Complex.I))
          * (u (n + 1) * blochAux_phase x (n + 1))
        + Complex.exp (2 * Real.pi * x * Complex.I) * (u (n - 1) * blochAux_phase x (n - 1)))
          + ((amoPot α lam θ n : ℝ) : ℂ) * u n * blochAux_phase x n)
      ((Complex.exp (-(2 * Real.pi * x * Complex.I)) * Work.TMComp.fourier u x
          + Complex.exp (2 * Real.pi * x * Complex.I) * Work.TMComp.fourier u x)
        + lam * (Complex.exp (2 * Real.pi * θ * Complex.I) * Work.TMComp.fourier u (x + α)
              + Complex.exp (-(2 * Real.pi * θ * Complex.I)) * Work.TMComp.fourier u (x - α))) :=
    (hA.add hB).add hD
  have hCeq : (fun n : ℤ => amoAct α lam θ u n * blochAux_phase x n)
      = (fun n : ℤ => (Complex.exp (-(2 * Real.pi * x * Complex.I))
            * (u (n + 1) * blochAux_phase x (n + 1))
          + Complex.exp (2 * Real.pi * x * Complex.I) * (u (n - 1) * blochAux_phase x (n - 1)))
            + ((amoPot α lam θ n : ℝ) : ℂ) * u n * blochAux_phase x n) := by
    funext n
    have h1 : Complex.exp (-(2 * Real.pi * x * Complex.I)) * (u (n + 1) * blochAux_phase x (n + 1))
        = u (n + 1) * blochAux_phase x n := by
      rw [← mul_assoc, mul_comm (Complex.exp (-(2 * Real.pi * x * Complex.I))) (u (n + 1)),
        mul_assoc, blochAux_exp_neg_mul_phase_add_one]
    have h2 : Complex.exp (2 * Real.pi * x * Complex.I) * (u (n - 1) * blochAux_phase x (n - 1))
        = u (n - 1) * blochAux_phase x n := by
      rw [← mul_assoc, mul_comm (Complex.exp (2 * Real.pi * x * Complex.I)) (u (n - 1)),
        mul_assoc, blochAux_exp_mul_phase_sub_one]
    simp only [amoAct]
    rw [h1, h2]
    ring
  have hC : HasSum (fun n : ℤ => amoAct α lam θ u n * blochAux_phase x n)
      ((Complex.exp (-(2 * Real.pi * x * Complex.I)) * Work.TMComp.fourier u x
          + Complex.exp (2 * Real.pi * x * Complex.I) * Work.TMComp.fourier u x)
        + lam * (Complex.exp (2 * Real.pi * θ * Complex.I) * Work.TMComp.fourier u (x + α)
              + Complex.exp (-(2 * Real.pi * θ * Complex.I)) * Work.TMComp.fourier u (x - α))) :=
    hABD.congr_fun (fun n => congrFun hCeq n)
  have hrecC : HasSum (fun n : ℤ => amoAct α lam θ u n * blochAux_phase x n)
      ((E : ℂ) * Work.TMComp.fourier u x) := by
    have h0 := (hF x).mul_left (E : ℂ)
    refine h0.congr_fun (fun n => ?_)
    rw [hrec n, mul_assoc]
  have hVU : (Complex.exp (-(2 * Real.pi * x * Complex.I)) * Work.TMComp.fourier u x
        + Complex.exp (2 * Real.pi * x * Complex.I) * Work.TMComp.fourier u x)
      + lam * (Complex.exp (2 * Real.pi * θ * Complex.I) * Work.TMComp.fourier u (x + α)
            + Complex.exp (-(2 * Real.pi * θ * Complex.I)) * Work.TMComp.fourier u (x - α))
      = (E : ℂ) * Work.TMComp.fourier u x :=
    hC.unique hrecC
  rw [← hVU]
  ring

end Work.TMComp.LocCantor
