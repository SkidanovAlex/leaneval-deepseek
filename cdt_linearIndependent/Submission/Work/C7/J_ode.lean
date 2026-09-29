import Mathlib
import Submission.Work.C7.xdefs

-- v4.35: `MvPowerSeries.inv_pow` (φ⁻¹ ^ n = (φ ^ n)⁻¹) became `@[simp]`; keep the old simp normal form
attribute [-simp] MvPowerSeries.inv_pow

namespace Work.C7

open PowerSeries

local notation "Xs" => (PowerSeries.X : PowerSeries ℚ)
local notation "u" => ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹
local notation "v" => ((PowerSeries.X : PowerSeries ℚ) - 1)

/-- `J = x·₃F₂(1/2,1,1;3/2,3/2;y/4)` (`y = x²/(x-1)`) satisfies the order-one ODE obtained by
pullback of the ODE of `B₅` along `y = x²/(x-1)`.  Purely algebraic: the auxiliary data are the
defining identities of `yps`, `cfun` together with the ODE of the fourth pure function `B₄ ∘ y`. -/
theorem J_ode
    (h1 : Work.C7.g 1 = 2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps)
    (hg5 : Work.C7.g 4 = (PowerSeries.X * (PowerSeries.X - 1)⁻¹) * Work.C7.Jps)
    (h5 : 2 * Work.C7.yps * (4 - Work.C7.yps) * PowerSeries.derivative (R := ℚ) (Work.C7.g 4)
            = ((4 - Work.C7.yps) * (Work.C7.g 4) - 2 * (Work.C7.g 1) + 4 * Work.C7.yps)
              * PowerSeries.derivative (R := ℚ) Work.C7.yps) :
    2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps - PowerSeries.X * Work.C7.Jps
      = 2 * (1 - PowerSeries.X) * Work.C7.Lps := by
  have huv : u * v = 1 := by simp
  -- basic identities of the pulled-back functions
  have hyps : yps = Xs^2 * u := by
    simp only [Work.C7.yps, Submission.CDT.sympY, Submission.CDT.sympPhi]; ring
  have h4y : 4 - yps = -(Xs - 2)^2 * u := by
    have h : v * u = 1 := by simp
    simp only [Work.C7.yps, Submission.CDT.sympY, Submission.CDT.sympPhi]
    linear_combination (-4) * h
  have hcfun : cfun = Xs * (Xs - 2) * u := rfl
  have hdy : PowerSeries.derivative (R := ℚ) yps = Xs * (Xs - 2) * u^2 := by
    have h : v * u = 1 := by simp
    have h' : PowerSeries.derivative (R := ℚ) yps = cfun * u := by
      simp only [Work.C7.yps, Submission.CDT.sympY, Submission.CDT.sympPhi, Work.C7.cfun]
      simp
      linear_combination (-2 * Xs * u) * h
    rw [h', hcfun]; ring
  have hdr : PowerSeries.derivative (R := ℚ) (Xs * u) = -(u^2) := by
    have h : v * u = 1 := by simp
    simp
    linear_combination (-u) * h
  -- substitute the hypotheses into `h5`
  have hDg4 : PowerSeries.derivative (R := ℚ) ((Xs * u) * Jps)
      = (PowerSeries.derivative (R := ℚ) (Xs*u)) * Jps + (Xs*u) * PowerSeries.derivative (R := ℚ) Jps := by
    simp; ring
  have hS : 2 * yps * (4 - yps) * ((PowerSeries.derivative (R := ℚ) (Xs * u)) * Jps + (Xs * u) * PowerSeries.derivative (R := ℚ) Jps)
      = ((4 - yps) * (Xs * u) * Jps + 2 * (cfun * Lps)) * PowerSeries.derivative (R := ℚ) yps := by
    have h := h5
    rw [hg5, h1] at h
    rw [hDg4] at h
    have hR : (4 - yps) * ((Xs * u) * Jps) - 2 * (2 * yps - cfun * Lps) + 4 * yps
        = (4 - yps) * (Xs * u) * Jps + 2 * (cfun * Lps) := by ring
    rw [hR] at h
    exact h
  -- clear the denominators `(x-1)⁻¹`
  have huv4 : u^4 * v^4 = 1 := by rw [← mul_pow, huv, one_pow]
  have huv3 : u^3 * v^4 = v := by
    have h3 : u^3 * v^3 = 1 := by rw [← mul_pow, huv, one_pow]
    calc u^3 * v^4 = (u^3 * v^3) * v := by ring
      _ = 1 * v := by rw [h3]
      _ = v := one_mul v
  have hLHS : v^4 * (2 * yps * (4 - yps) * ((PowerSeries.derivative (R := ℚ) (Xs*u)) * Jps + (Xs*u) * PowerSeries.derivative (R := ℚ) Jps))
      = 2*Xs^2*(Xs-2)^2*Jps - 2*Xs^3*(Xs-2)^2*v*(PowerSeries.derivative (R := ℚ) Jps) := by
    rw [h4y, hyps, hdr]
    rw [show v^4 * (2 * (Xs^2*u) * (-(Xs-2)^2*u) * ((-(u^2)) * Jps + (Xs*u) * PowerSeries.derivative (R := ℚ) Jps))
        = 2*Xs^2*(Xs-2)^2*(u^4*v^4)*Jps - 2*Xs^3*(Xs-2)^2*(u^3*v^4)*(PowerSeries.derivative (R := ℚ) Jps) from by ring,
      huv4, huv3]
    ring
  have hRHS : v^4 * (((4 - yps) * (Xs*u) * Jps + 2 * (cfun * Lps)) * PowerSeries.derivative (R := ℚ) yps)
      = -Xs^2*(Xs-2)^3*Jps + 2*Xs^2*(Xs-2)^2*v*Lps := by
    rw [h4y, hcfun, hdy]
    rw [show v^4 * (((-(Xs-2)^2*u) * (Xs*u) * Jps + 2 * (Xs*(Xs-2)*u * Lps)) * (Xs*(Xs-2)*u^2))
        = -Xs^2*(Xs-2)^3*(u^4*v^4)*Jps + 2*Xs^2*(Xs-2)^2*(u^3*v^4)*Lps from by ring,
      huv4, huv3]
    ring
  have hS4 := congrArg (fun z : PowerSeries ℚ => v^4 * z) hS
  rw [hLHS, hRHS] at hS4
  have hZ : Xs^2*(Xs-2)^2*(Xs*Jps - 2*Xs*v*(PowerSeries.derivative (R := ℚ) Jps) - 2*v*Lps) = 0 := by
    linear_combination hS4
  have hfac : Xs^2*(Xs-2)^2 ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero 2 PowerSeries.X_ne_zero
    · apply pow_ne_zero
      intro h
      have hc : PowerSeries.constantCoeff (Xs - 2 : PowerSeries ℚ) = -2 := by
        rw [map_sub, PowerSeries.constantCoeff_X, map_ofNat]
        norm_num
      rw [h] at hc
      norm_num at hc
  have hzero : Xs*Jps - 2*Xs*v*(PowerSeries.derivative (R := ℚ) Jps) - 2*v*Lps = 0 := by
    rcases mul_eq_zero.mp hZ with h | h
    · exact absurd h hfac
    · exact h
  have hE : 2*Xs*v*(PowerSeries.derivative (R := ℚ) Jps) - Xs*Jps + 2*v*Lps = 0 := by
    linear_combination (-1)*hzero
  linear_combination hE

end Work.C7
