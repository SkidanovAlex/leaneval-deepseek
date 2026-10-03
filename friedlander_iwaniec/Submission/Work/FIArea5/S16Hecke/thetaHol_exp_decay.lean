import Mathlib
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea5.S16Hecke.thetaHol_eq_tsum_heckeLam

namespace Work.FIArea5.S16Hecke

open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- Pointwise majorant for the summand of `thetaHol`: for `u > 0` and `‖χ‖ ≤ 1`,
`‖χ(z) z^m e^{-πu|z|²}‖ ≤ e^{-(πu|z|²)} (1 + |z|²)^m` on primary `z` (and `0` otherwise). -/
lemma thetaSummand_norm_le {chi : GaussianInt → ℂ} {m : ℕ} {u : ℝ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (z : GaussianInt) :
    ‖thetaSummand chi m u z‖ ≤
      Real.exp (-(Real.pi * u * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ))^m := by
  classical
  rw [show thetaSummand chi m u z = (if IsPrimary z then
      chi z * (z.toComplex)^m * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0) from rfl]
  by_cases hz : IsPrimary z
  · rw [if_pos hz]
    have h1 : ‖chi z‖ ≤ 1 := hb z
    have h2 : ‖(z.toComplex)^m‖ ≤ (1 + (gnorm z : ℝ))^m := by
      rw [norm_pow, norm_toComplex]
      apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (gnorm z) : (0:ℝ) ≤ (gnorm z : ℝ)),
        sq_nonneg (Real.sqrt (gnorm z : ℝ) - 1/2), Real.sqrt_nonneg (gnorm z : ℝ)]
    calc ‖chi z * (z.toComplex)^m * Complex.exp (-Real.pi * u * (gnorm z : ℝ))‖
        = ‖chi z‖ * ‖(z.toComplex)^m‖ * Real.exp (-(Real.pi * u * (gnorm z : ℝ))) := by
          rw [norm_mul, norm_mul, norm_exp_theta]
      _ ≤ 1 * (1 + (gnorm z : ℝ))^m * Real.exp (-(Real.pi * u * (gnorm z : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) zero_le_one)
            (Real.exp_nonneg _)
      _ = Real.exp (-(Real.pi * u * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ))^m := by ring
  · rw [if_neg hz, norm_zero]
    positivity

/-- **Absolute convergence of the holomorphic theta series** for `u > 0` and `‖χ‖ ≤ 1`:
the summands are dominated by the summable Gaussian weight `e^{-πu|z|²}(1+|z|²)^m`. -/
lemma summable_thetaSummand {u : ℝ} (hu : 0 < u) (chi : GaussianInt → ℂ) (m : ℕ)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) : Summable (fun z : GaussianInt => thetaSummand chi m u z) :=
  Summable.of_norm_bounded (summable_gnorm_weight hu m) (fun z => thetaSummand_norm_le hb z)

/-- **Exponential decay of the holomorphic theta series beyond the cut** `u ≥ c = 1/(4d)`:
there is a constant `C ≥ 0` with `‖thetaHol χ m u‖ ≤ C·e^{-π(u-c)}` for all `u ≥ c`.  This is the
decay used to make the Mellin cut integrals `heckeA`, `heckeE` absolutely convergent at `t` in a
right half-plane; it follows from `thetaHol_bound_of_summable` applied at `u₀ = c`, the pointwise
majorant being summable because `c > 0`. -/
theorem thetaHol_exp_decay (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, Work.FIArea5.S16Hecke.thetaC d ≤ u →
      ‖Work.FIArea5.S16Hecke.thetaHol chi m u‖ ≤
        C * Real.exp (-Real.pi * (u - Work.FIArea5.S16Hecke.thetaC d)) :=
  thetaHol_bound_of_summable chi m (thetaC_pos hd)
    (summable_thetaSummand (thetaC_pos hd) chi m hb)

end

end Work.FIArea5.S16Hecke
