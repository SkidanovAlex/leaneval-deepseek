import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The time derivative of the heat kernel on `ℝ³`, and its size on a multiplicative window

`∂_t γ_t(z) = (4πt)^{-3/2}·(‖z‖²/(4t²) - 3/(2t))·exp(-‖z‖²/(4t))`, and for `t > 0` and
`s ∈ [t/2, 2t]` this is bounded by
`(4π(t/2))^{-3/2}·(3/t + ‖z‖²/t²)·exp(-‖z‖²/(8t))`.

Both factors are compared on the window: the prefactor `(4π·)^{-3/2}` decreases, the polynomial
factor grows by a constant factor, and the Gaussian decays when the exponent shrinks.
-/

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

open scoped Topology

/-- The explicit time derivative of the heat kernel `γ_t(z) = (4πt)^{-3/2} exp(-‖z‖²/(4t))`. -/
lemma deriv_heatKernel_time_of_pos (r : ℝ) (hr : 0 < r) (z : R3) :
    deriv (fun x : ℝ => heatKernel x z) r
      = (4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * r ^ 2) - 3 / (2 * r)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * r))) := by
  have hx : (4 * Real.pi * r) ^ (-(3 / 2 : ℝ))
      = (4 * Real.pi * r) ^ (-(3 / 2 : ℝ) - 1) * (4 * Real.pi * r) := by
    have h := Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi * r) (-(3 / 2 : ℝ) - 1) 1
    rw [show (-(3 / 2 : ℝ) - 1) + 1 = -(3 / 2 : ℝ) by norm_num] at h
    simpa using h
  have key : (-(3 / 2 : ℝ)) * (4 * Real.pi * r) ^ (-(3 / 2 : ℝ) - 1) * (4 * Real.pi)
      = (4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (-(3 / (2 * r))) := by
    rw [hx]; field_simp
  have hA : HasDerivAt (fun x : ℝ => (4 * Real.pi * x) ^ (-(3 / 2 : ℝ)))
      ((4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (-(3 / (2 * r)))) r := by
    have hin : HasDerivAt (fun x : ℝ => 4 * Real.pi * x) (4 * Real.pi) r := by
      simpa using (hasDerivAt_id r).const_mul (4 * Real.pi)
    have hout : HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ)))
        ((-(3 / 2 : ℝ)) * (4 * Real.pi * r) ^ (-(3 / 2 : ℝ) - 1)) (4 * Real.pi * r) :=
      Real.hasDerivAt_rpow_const (Or.inl (by positivity))
    have h := hout.comp r hin
    rw [key] at h
    exact h
  have hB : HasDerivAt (fun x : ℝ => Real.exp (-(‖z‖ ^ 2 / (4 * x))))
      (Real.exp (-(‖z‖ ^ 2 / (4 * r))) * (‖z‖ ^ 2 / (4 * r ^ 2))) r := by
    have hden : HasDerivAt (fun x : ℝ => 4 * x) 4 r := by
      simpa using (hasDerivAt_id r).const_mul (4 : ℝ)
    have hquot : HasDerivAt (fun u : ℝ => ‖z‖ ^ 2 / u) (-(‖z‖ ^ 2) / (4 * r) ^ 2) (4 * r) := by
      have h := (hasDerivAt_const (4 * r) (‖z‖ ^ 2)).div (hasDerivAt_id (4 * r))
        (by simpa using (show (4 : ℝ) * r ≠ 0 by positivity))
      have hfun : ((fun _ : ℝ => ‖z‖ ^ 2) / id : ℝ → ℝ) = fun u : ℝ => ‖z‖ ^ 2 / u := by
        ext u; simp [Pi.div_apply]
      rw [hfun] at h
      simpa using h
    have hcomp : HasDerivAt (fun x : ℝ => ‖z‖ ^ 2 / (4 * x))
        ((-(‖z‖ ^ 2) / (4 * r) ^ 2) * 4) r := hquot.comp r hden
    have hneg : HasDerivAt (fun x : ℝ => -(‖z‖ ^ 2 / (4 * x)))
        (-((-(‖z‖ ^ 2) / (4 * r) ^ 2) * 4)) r := hcomp.neg
    have hkey : -((-(‖z‖ ^ 2) / (4 * r) ^ 2) * 4) = ‖z‖ ^ 2 / (4 * r ^ 2) := by field_simp
    have hneg' : HasDerivAt (fun x : ℝ => -(‖z‖ ^ 2 / (4 * x))) (‖z‖ ^ 2 / (4 * r ^ 2)) r := by
      rw [← hkey]; exact hneg
    exact hneg'.exp
  have hprod : HasDerivAt
      (fun x : ℝ => (4 * Real.pi * x) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * x))))
      ((4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (-(3 / (2 * r))) * Real.exp (-(‖z‖ ^ 2 / (4 * r))) +
        (4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) *
          (Real.exp (-(‖z‖ ^ 2 / (4 * r))) * (‖z‖ ^ 2 / (4 * r ^ 2)))) r := hA.mul hB
  simp only [heatKernel]
  rw [hprod.deriv]
  ring_nf

theorem abs_deriv_heatKernel_time_le (t : ℝ) (ht : 0 < t) (s : ℝ) (hs : t / 2 ≤ s)
    (hs2 : s ≤ 2 * t) (z : Work.FTS.PressureOn.R3) :
    |deriv (fun r : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel r z) s| ≤
      (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) * (3 / t + ‖z‖ ^ 2 / t ^ 2) *
        Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
  have ht2 : 0 < t / 2 := by linarith
  have hs0 : 0 < s := by linarith
  rw [deriv_heatKernel_time_of_pos s hs0 z]
  have hApos : 0 < (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hA'pos : 0 < (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hA'nn : 0 ≤ (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) := hA'pos.le
  have hAle : (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) ≤ (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [hs, Real.pi_pos]) (by norm_num)
  have h1 : ‖z‖ ^ 2 / (4 * s ^ 2) ≤ ‖z‖ ^ 2 / t ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hs, ht])
  have h2 : 3 / (2 * s) ≤ 3 / t :=
    div_le_div_of_nonneg_left (by norm_num) ht (by nlinarith [hs])
  have hBnn : 0 ≤ 3 / t + ‖z‖ ^ 2 / t ^ 2 := by positivity
  have hB : |‖z‖ ^ 2 / (4 * s ^ 2) - 3 / (2 * s)| ≤ 3 / t + ‖z‖ ^ 2 / t ^ 2 := by
    have ha : 0 ≤ ‖z‖ ^ 2 / (4 * s ^ 2) := by positivity
    have hb : 0 ≤ 3 / (2 * s) := by positivity
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hC : Real.exp (-(‖z‖ ^ 2 / (4 * s))) ≤ Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
    rw [Real.exp_le_exp]
    have h : ‖z‖ ^ 2 / (8 * t) ≤ ‖z‖ ^ 2 / (4 * s) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hs2, ht])
    linarith
  have hCpos : 0 < Real.exp (-(‖z‖ ^ 2 / (4 * s))) := Real.exp_pos _
  rw [abs_mul, abs_mul, abs_of_pos hApos, abs_of_pos hCpos]
  calc (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) * |‖z‖ ^ 2 / (4 * s ^ 2) - 3 / (2 * s)| *
          Real.exp (-(‖z‖ ^ 2 / (4 * s)))
      ≤ ((4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) * (3 / t + ‖z‖ ^ 2 / t ^ 2)) *
          Real.exp (-(‖z‖ ^ 2 / (8 * t))) :=
        mul_le_mul (mul_le_mul hAle hB (abs_nonneg _) hA'nn) hC hCpos.le (mul_nonneg hA'nn hBnn)
    _ = (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) * (3 / t + ‖z‖ ^ 2 / t ^ 2) *
          Real.exp (-(‖z‖ ^ 2 / (8 * t))) := rfl

end

end Work.FTS.PressureOn.Auxiliary
