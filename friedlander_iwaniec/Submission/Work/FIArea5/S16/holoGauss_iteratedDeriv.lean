import Mathlib
import Submission.Work.FIArea5.S16.holoGaussDefs

namespace Work.FIArea5.S16

open Complex

/-- The `m`-th derivative at `0` of `t ↦ c * exp (k * t)`. -/
lemma iteratedDeriv_const_mul_exp (m : ℕ) (c k : ℂ) :
    iteratedDeriv m (fun t : ℂ => c * Complex.exp (k * t)) 0 = c * k ^ m := by
  rw [iteratedDeriv_const_mul_field]
  rw [show iteratedDeriv m (fun t : ℂ => Complex.exp (k * t)) 0 = k ^ m from by
    rw [iteratedDeriv_comp_const_mul Complex.contDiff_exp k]
    simp [show iteratedDeriv m Complex.exp = Complex.exp from by
      rw [iteratedDeriv_eq_iterate]; exact Complex.iter_deriv_exp m]]

theorem holoGauss_iteratedDeriv {u : ℝ} (hu : 0 < u) (m : ℕ) (a b : ℂ) :
    iteratedDeriv m (fun t : ℂ => gaussW u (a + t) * gaussW u (b + Complex.I * t)) 0
      = (1 / (u : ℂ) ^ (1 / 2 : ℂ)) ^ 2 *
          Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (a ^ 2 + b ^ 2)) *
          (-(2 * (Real.pi : ℂ) / (u : ℂ) * (a + Complex.I * b))) ^ m := by
  have _hu : (0 : ℝ) < u := hu
  have hpt : ∀ t : ℂ, gaussW u (a + t) * gaussW u (b + Complex.I * t)
      = ((1 / (u : ℂ) ^ (1 / 2 : ℂ)) ^ 2 *
            Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (a ^ 2 + b ^ 2))) *
          Complex.exp ((-(2 * (Real.pi : ℂ) / (u : ℂ) * (a + Complex.I * b))) * t) := by
    intro t
    simp only [gaussW]
    have h1 : (1 / (u : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (a + t) ^ 2)) *
              (1 / (u : ℂ) ^ (1 / 2 : ℂ) *
                Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (b + Complex.I * t) ^ 2))
          = (1 / (u : ℂ) ^ (1 / 2 : ℂ)) ^ 2 *
              (Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (a + t) ^ 2) *
                Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (b + Complex.I * t) ^ 2)) := by
      ring
    rw [h1, ← Complex.exp_add]
    have harg : -(Real.pi : ℂ) / (u : ℂ) * (a + t) ^ 2 +
                -(Real.pi : ℂ) / (u : ℂ) * (b + Complex.I * t) ^ 2
          = -(Real.pi : ℂ) / (u : ℂ) * (a ^ 2 + b ^ 2) +
              (-(2 * (Real.pi : ℂ) / (u : ℂ) * (a + Complex.I * b))) * t := by
      ring_nf
      rw [Complex.I_sq]; ring
    rw [harg, Complex.exp_add]
    ring
  rw [show (fun t : ℂ => gaussW u (a + t) * gaussW u (b + Complex.I * t))
        = (fun t : ℂ => ((1 / (u : ℂ) ^ (1 / 2 : ℂ)) ^ 2 *
              Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (a ^ 2 + b ^ 2))) *
            Complex.exp ((-(2 * (Real.pi : ℂ) / (u : ℂ) * (a + Complex.I * b))) * t))
        from funext hpt]
  exact iteratedDeriv_const_mul_exp m _ _

end Work.FIArea5.S16
