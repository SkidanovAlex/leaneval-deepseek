import Mathlib
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaHol_one_div_dual
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay

namespace Work.FIArea6Hecke.R.MGGrow

open scoped BigOperators

/-- **Near-zero growth of the normalised dual kernel.**  For a strict character `χ` mod `4d`, a
weight `k` with `unitSum χ k ≠ 0`, and `0 < x ≤ 1`, the normalised dual theta kernel satisfies

  `‖thetaDualMG d χ k x‖ ≤ C·x^{-(k+1)}·e^{-π/x}`.

This is the `x → 0⁺` half of the growth control of `thetaDualMG`: the Poisson/Poisson-dual
transformation `thetaHol χ k (1/x) = x^{k+1}·thetaDualMG d χ k x` turns the dual kernel at `x`
into the holomorphic theta series at `1/x ≥ 1`, whose exponential decay `thetaHol_exp_decay`
(relative to the cut `thetaC d = 1/(4d) ≤ 1`) gives the bound. -/
theorem thetaDualMG_near_zero_bound (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (k : ℕ)
    (hU : Work.FIArea5.S16Hecke.unitSum chi k ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖ ≤
        C * x ^ (-((k : ℝ) + 1)) * Real.exp (-Real.pi / x) := by
  -- a strict character modulo `4d` is bounded by `1`
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := fun z => hchi.1.2.2.1 z
  obtain ⟨C₀, hC₀, hdec⟩ := Work.FIArea5.S16Hecke.thetaHol_exp_decay d hd chi k hb
  refine ⟨C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) + 1, ?_, ?_⟩
  · have : 0 ≤ C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) :=
      mul_nonneg hC₀ (Real.exp_nonneg _)
    linarith
  · intro x hx hx1
    -- the cut `thetaC d = 1/(4d)` is at most `1 ≤ 1/x`
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hthetaC_le : Work.FIArea5.S16Hecke.thetaC d ≤ 1 := by
      rw [Work.FIArea5.S16Hecke.thetaC, div_le_one (by positivity)]
      linarith
    have hone : (1:ℝ) ≤ 1/x := by
      have h := one_div_le_one_div_of_le hx hx1
      simpa using h
    have hcd : Work.FIArea5.S16Hecke.thetaC d ≤ 1 / x := le_trans hthetaC_le hone
    -- Poisson duality converts the dual kernel at `x` into `thetaHol` at `1/x`
    have hdual := Work.FIArea6Hecke.R.thetaHol_one_div_dual_pow d hd hchi k hU hx
    have hnorm_eq : ‖Work.FIArea5.S16Hecke.thetaHol chi k (1 / x)‖
        = x ^ (k + 1) * ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖ := by
      rw [hdual, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    have hcut := hdec (1/x) hcd
    rw [hnorm_eq] at hcut
    -- shift the Gaussian decay to the origin: `e^{-π(1/x - c)} = e^{πc}·e^{-π/x}`
    have hexp : Real.exp (-Real.pi * (1 / x - Work.FIArea5.S16Hecke.thetaC d))
        = Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) * Real.exp (-Real.pi / x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hcut
    have hxpow_pos : (0:ℝ) < x ^ (k+1) := pow_pos hx _
    have hstep : ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖
        ≤ C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) *
            Real.exp (-Real.pi / x) / x ^ (k + 1) := by
      rw [le_div_iff₀ hxpow_pos]
      calc ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖ * x ^ (k+1)
          = x ^ (k+1) * ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖ := by ring
        _ ≤ C₀ * (Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) *
              Real.exp (-Real.pi / x)) := hcut
        _ = C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) *
              Real.exp (-Real.pi / x) := by ring
    -- `x^{-(k+1)} = (x^{k+1})⁻¹`
    have hpow : x ^ (-((k:ℝ)+1)) = (x ^ (k+1))⁻¹ := by
      rw [Real.rpow_neg hx.le]
      congr 1
      rw [show ((k:ℝ)+1) = ((k+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
    calc ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖
        ≤ C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) *
            Real.exp (-Real.pi / x) / x ^ (k + 1) := hstep
      _ = (C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d)) *
            x ^ (-((k:ℝ)+1)) * Real.exp (-Real.pi / x) := by
          rw [hpow, div_eq_mul_inv]; ring
      _ ≤ (C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) + 1) *
            x ^ (-((k:ℝ)+1)) * Real.exp (-Real.pi / x) := by
          have hp : 0 ≤ x ^ (-((k:ℝ)+1)) := Real.rpow_nonneg hx.le _
          have he : 0 ≤ Real.exp (-Real.pi/x) := Real.exp_nonneg _
          have hC : C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d)
              ≤ C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) + 1 := by linarith
          calc (C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d)) *
                x ^ (-((k:ℝ)+1)) * Real.exp (-Real.pi / x)
              ≤ ((C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) + 1) *
                x ^ (-((k:ℝ)+1))) * Real.exp (-Real.pi / x) := by
                apply mul_le_mul_of_nonneg_right _ he
                exact mul_le_mul_of_nonneg_right hC hp
            _ = (C₀ * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d) + 1) *
                x ^ (-((k:ℝ)+1)) * Real.exp (-Real.pi / x) := by ring

end Work.FIArea6Hecke.R.MGGrow
