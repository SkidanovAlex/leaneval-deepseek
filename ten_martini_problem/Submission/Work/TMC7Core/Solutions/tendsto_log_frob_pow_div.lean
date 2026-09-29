import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_add_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Solutions.spectralRadius_eq_eigenvalues
import Submission.Work.TMC7Core.Solutions.tendsto_norm_pow_one_div_of_spectralRadius

/-!
# The exponential growth rate of `‖M ^ n‖_F` for a unimodular `2 × 2` complex matrix

For a `2 × 2` complex matrix `M` with `det M = 1` whose (necessarily) eigenvalues are `la`, `mu`
(so `la + mu = tr M` and `la * mu = 1`), the Frobenius norm of the powers grows like the spectral
radius `ρ = max ‖la‖ ‖mu‖`:

  `log ‖M ^ (k+1)‖_F / (k + 1) → log ρ`.

This is the real-logarithm form of Gelfand's formula, with the spectral radius computed from the
characteristic polynomial.  It is the "one-matrix" input to the periodic (rational frequency)
Lyapunov computation.
-/

open scoped Matrix.Norms.Frobenius

namespace Work.TMC7Core.Solutions

theorem tendsto_log_frob_pow_div (M : Matrix (Fin 2) (Fin 2) ℂ) (hd : M.det = 1)
    (la mu : ℂ) (hsum : la + mu = M.trace) (hprod : la * mu = 1) :
    Filter.Tendsto (fun k : ℕ => Real.log (Work.TMC7Core.frob (M ^ (k + 1))) / ((k : ℝ) + 1))
      Filter.atTop (nhds (Real.log (max ‖la‖ ‖mu‖))) := by
  -- The spectral radius of `M` is `max ‖la‖ ‖mu‖`.
  have hspec : spectralRadius ℂ M = ENNReal.ofReal (max ‖la‖ ‖mu‖) :=
    spectralRadius_eq_eigenvalues M hd la mu hsum hprod
  have hρ0 : (0 : ℝ) ≤ max ‖la‖ ‖mu‖ := le_trans (norm_nonneg la) (le_max_left _ _)
  have hρne : max ‖la‖ ‖mu‖ ≠ 0 := by
    have h1 : (1 : ℝ) ≤ max ‖la‖ ‖mu‖ := by
      by_contra h
      rw [not_le, max_lt_iff] at h
      have hmul : ‖la‖ * ‖mu‖ = 1 := by rw [← norm_mul la mu, hprod, norm_one]
      have : ‖la‖ * ‖mu‖ < 1 := by nlinarith [h.1, h.2, norm_nonneg la, norm_nonneg mu]
      rw [hmul] at this
      exact lt_irrefl _ this
    linarith
  -- Gelfand's formula in real form: `‖M ^ n‖ ^ (1/n) → ρ`.
  have hlim : Filter.Tendsto (fun n : ℕ => ‖M ^ n‖ ^ (1 / (n : ℝ))) Filter.atTop
      (nhds (max ‖la‖ ‖mu‖)) :=
    tendsto_norm_pow_one_div_of_spectralRadius M (max ‖la‖ ‖mu‖) hspec hρ0
  -- Taking logarithms: `log ‖M ^ n‖ / n → log ρ`.
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log ‖M ^ n‖ / (n : ℝ)) Filter.atTop
      (nhds (Real.log (max ‖la‖ ‖mu‖))) := by
    refine Filter.Tendsto.congr' ?_ (hlim.log hρne)
    filter_upwards with n
    have hne : M ^ n ≠ 0 := by
      intro h0
      have hdetn : (M ^ n).det = 1 := by rw [Matrix.det_pow, hd, one_pow]
      rw [h0, Matrix.det_zero] at hdetn
      exact one_ne_zero hdetn.symm
    rw [Real.log_rpow (norm_pos_iff.mpr hne), one_div, div_eq_mul_inv]
    ring
  -- Shift the index `n ↦ k + 1`.
  have hshift : Filter.Tendsto (fun k : ℕ => Real.log ‖M ^ (k + 1)‖ / ((k + 1 : ℕ) : ℝ))
      Filter.atTop (nhds (Real.log (max ‖la‖ ‖mu‖))) :=
    hlog.comp (Filter.tendsto_add_atTop_nat 1)
  -- Replace the Frobenius norm and the cast of the index.
  refine Filter.Tendsto.congr' ?_ hshift
  filter_upwards with k
  simp only [Work.TMC7Core.Cocycle.frob_eq_norm, Nat.cast_add, Nat.cast_one]

end Work.TMC7Core.Solutions
