/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.WinAux
import Submission.Work.Peluse.WindowControl.normSqSum_one_eq_sum_ball
import Submission.Work.Peluse.WindowControl.sum_ball_eq_sum_Icc

/-!
# The first box-norm power over a window

Peluse's box-norm power `‖g‖^{2^t}_{□^t_{Q₁,…,Q_t}(S)}` is defined through a `tsum` over all of `ℤ`
and an average over the shift tuples; the set `S` enters only through the normalising factor
`1/|S|` (see `Work.Peluse.prodCubeSum`).  For `t = 1` the whole expression collapses to a single
sum of squares, and the `x`-sum is supported in the window `[-2N, 2N]` as soon as the slots `Q₀`
and the function `g` both live in `[-N, N]`:

  `boxNormPow 1 (fun _ => Q0) S g
     = (1/|S|) · (1/|Q0|)² · ∑_{x ∈ [-2N,2N]} ‖∑_{a ∈ Q0} g (x + a)‖²`.

This is the "level one" normal form of the box norm used to control the window sums of the
Gowers-norm argument (`Submission/Work/Peluse/PET/NOTES_boxNormPow_control_v2.md`,
`…/WindowControl/absSq_window_control.lean`).

## Main results

* `Work.Peluse.WindowControl.boxNormPow_one_eq_boxScaling_normSqSum`: the box-norm power is the
  normalising constant times the sum of squares `normSqSum`;
* `Work.Peluse.WindowControl.boxNormPow_one_window`: the statement above.

The two ingredients are the base case of the sum-of-squares identity
(`normSqSum_one_eq_sum_ball`) and the support bookkeeping replacing Peluse's `x`-window
`[-N - ∑|a|, N + ∑|a|]` by `[-2N, 2N]` (`sum_ball_eq_sum_Icc`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.WindowControl

/-- For finitely supported `g` the first box-norm power is the normalising constant
`boxScaling` times the sum of squares `normSqSum`.  This is `boxSumPow_eq_scaling` combined with
the sum-of-squares identity `rawSum_eq_cubeNormSqSum` and `boxSumPow_eq_boxNormPow`. -/
theorem boxNormPow_one_eq_boxScaling_normSqSum {N : ℕ} (Q0 : Finset ℤ) (S : Finset ℤ)
    (g : ℤ → ℂ) (hsupp : Work.Peluse.SupportIn g N) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q0) S g
      = Work.Peluse.BoxNorm.boxScaling 1 (fun _ : Fin 1 => Q0) S *
        Work.Peluse.BoxNorm.normSqSum (fun _ : Fin 1 => Q0) g N := by
  have h1 : Work.Peluse.boxSumPow 1 (fun _ : Fin 1 => Q0) S g
      = (Work.Peluse.BoxNorm.boxScaling 1 (fun _ : Fin 1 => Q0) S : ℂ) *
        Work.Peluse.BoxNorm.rawSum 1 (fun _ : Fin 1 => Q0) g :=
    Work.Peluse.BoxNorm.boxSumPow_eq_scaling 1 (fun _ : Fin 1 => Q0) S g
  have h2 : Work.Peluse.BoxNorm.rawSum 1 (fun _ : Fin 1 => Q0) g
      = ((Work.Peluse.BoxNorm.normSqSum (fun _ : Fin 1 => Q0) g N : ℝ) : ℂ) :=
    Work.Peluse.BoxNorm.rawSum_eq_cubeNormSqSum (fun _ : Fin 1 => Q0) g hsupp
  have h3 : Work.Peluse.boxSumPow 1 (fun _ : Fin 1 => Q0) S g
      = ((Work.Peluse.BoxNorm.boxScaling 1 (fun _ : Fin 1 => Q0) S *
          Work.Peluse.BoxNorm.normSqSum (fun _ : Fin 1 => Q0) g N : ℝ) : ℂ) := by
    rw [h1, h2, ← Complex.ofReal_mul]
  have h4 : Work.Peluse.boxSumPow 1 (fun _ : Fin 1 => Q0) S g
      = ((Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q0) S g : ℝ) : ℂ) :=
    Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow le_rfl ⟨N, hsupp⟩
  rw [h4] at h3
  exact Complex.ofReal_inj.mp h3

/-- The normalising constant `boxScaling` of the first box-norm power, evaluated. -/
theorem boxScaling_one_eq (S Q0 : Finset ℤ) :
    Work.Peluse.BoxNorm.boxScaling 1 (fun _ : Fin 1 => Q0) S
      = ((S.card : ℝ))⁻¹ * ((Q0.card : ℝ))⁻¹ ^ 2 := by
  simp [Work.Peluse.BoxNorm.boxScaling, pow_two]
  ring

theorem boxNormPow_one_window {N : ℕ} (Q0 : Finset ℤ) (S : Finset ℤ) (g : ℤ → ℂ)
    (hbd : ∀ a ∈ Q0, |a| ≤ (N : ℤ)) (hsupp : Work.Peluse.SupportIn g N) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q0) S g
      = ((S.card : ℝ)⁻¹ * ((Q0.card : ℝ))⁻¹ ^ 2)
        * ∑ x ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)), ‖∑ a ∈ Q0, g (x + a)‖ ^ 2 := by
  have hbox := boxNormPow_one_eq_boxScaling_normSqSum Q0 S g hsupp
  rw [hbox, boxScaling_one_eq S Q0, normSqSum_one_eq_sum_ball,
    sum_ball_eq_sum_Icc Q0 g hbd hsupp]

end Work.Peluse.WindowControl
