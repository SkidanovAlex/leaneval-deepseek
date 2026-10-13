/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the weighted `t`-Fourier slice, all orders up to two

`Work.FTS.EllSol.FlatFT.integrable_weighted_slice1`:
for `k ≤ 2` and `h : ℝ → ℂ` of class `C^k` with compact support,
`ξ ↦ (2πξ)^{2k} ‖slice1 h ξ‖²` is integrable.

The point is that `(2πξ)^{2k} ‖slice1 h ξ‖² = ‖slice1 (deriv^k h) ξ‖²` pointwise, by `k`
applications of the derivative rule for the Fourier transform (`slice1_deriv`) and the modulus
identity `norm_sq_mul_two_pi_I`; `deriv^k h` is again continuous with compact support, so the
sibling `integrable_normSq_slice1` finishes.  We prove the statement for *every* `n`
(`integrable_weighted_slice1_aux`, by induction on `n`), and specialise.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv
import Submission.Work.FTS.EllSol.FlatFT.plancherelDeriv2
import Submission.Work.FTS.EllSol.FlatFT.integrable_normSq_slice1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- **The weighted square of the `t`-Fourier slice is integrable, in every order.**  For
`h : ℝ → ℂ` of class `C^n` with compact support, `ξ ↦ (2πξ)^{2n} ‖slice1 h ξ‖²` is integrable.

Induction on `n`: the weight `(2πξ)²` is exactly the squared modulus of the Fourier multiplier
`2πIξ`, so shifting it onto the slice is the same as differentiating `h` (`slice1_deriv`). -/
theorem integrable_weighted_slice1_aux (n : ℕ) {h : ℝ → ℂ} (hh : ContDiff ℝ n h)
    (hs : HasCompactSupport h) :
    MeasureTheory.Integrable
      (fun ξ : ℝ => (2 * Real.pi * ξ) ^ (2 * n) * ‖slice1 h ξ‖ ^ 2) := by
  induction n generalizing h with
  | zero =>
      simpa using integrable_normSq_slice1 hh.continuous hs
  | succ n ih =>
      have h1 : ContDiff ℝ 1 h :=
        hh.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
      have hd : ContDiff ℝ n (deriv h) := hh.deriv'
      have hs' : HasCompactSupport (deriv h) := hs.deriv
      refine (ih hd hs').congr (Filter.Eventually.of_forall fun ξ => ?_)
      beta_reduce
      rw [slice1_deriv h h1 hs ξ, norm_sq_mul_two_pi_I]
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
      ring

theorem integrable_weighted_slice1 {k : ℕ} (hk : k ≤ 2) {h : ℝ → ℂ} (hh : ContDiff ℝ k h)
    (hs : HasCompactSupport h) :
    MeasureTheory.Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ (2 * k) * ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2) := by
  have _ := hk
  exact integrable_weighted_slice1_aux k hh hs

end Work.FTS.EllSol.FlatFT
