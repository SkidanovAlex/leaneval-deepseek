/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The three derivative bounds implied by a `C^{2,α}` bound on the polydisc

Let `Pd n R` be the polydisc of radius `R` about the origin of `ℂⁿ` and let `u : ℂⁿ → ℂ` satisfy

  `holderNorm 2 α u (Pd n R) ≤ ofReal b`,   `0 ≤ b`.

This file proves the three consequences of that bound which the Newton correction
needs:

* `‖fderiv ℝ u z‖ ≤ b` for `z ∈ Pd n R` (order `1` sup bound),
* `‖fderiv ℝ (fderiv ℝ u) z‖ ≤ b` for `z ∈ Pd n R` (order `2` sup bound),
* `‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ b ‖x - y‖ ^ α` for
  `x, y ∈ Pd n R` (order `2` Hölder seminorm).

The mechanism is the same as in `holderNorm_one_fderiv_coeff_le`: the `holderNorm`
control of order `i ≤ 2` gives, via
`norm_iteratedFDerivWithin_le_of_holderNorm_le` and
`norm_sub_iteratedFDerivWithin_le_of_holderNorm_with_le`, bounds on the *within*
iterated derivatives, which are then identified with the genuine derivatives because
the polydisc is open.
-/
import Mathlib
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Newton.pushforward_setup

namespace Work.NN.Newton

theorem holderNorm_two_deriv_bounds {n : ℕ} {α b R : ℝ} (hα0 : 0 < α) {u : Work.NN.Core.Cn n → ℂ}
    (hb0 : 0 ≤ b) (hb : Work.CR.Flat.holderNorm 2 α u (Work.NN.Newton.Pd n R) ≤ ENNReal.ofReal b) :
    (∀ z ∈ Work.NN.Newton.Pd n R, ‖fderiv ℝ u z‖ ≤ b) ∧
    (∀ z ∈ Work.NN.Newton.Pd n R, ‖fderiv ℝ (fun z => fderiv ℝ u z) z‖ ≤ b) ∧
    (∀ x ∈ Work.NN.Newton.Pd n R, ∀ y ∈ Work.NN.Newton.Pd n R,
      ‖fderiv ℝ (fun z => fderiv ℝ u z) x - fderiv ℝ (fun z => fderiv ℝ u z) y‖
        ≤ b * ‖x - y‖ ^ α) := by
  have hPopen : IsOpen (Pd n R) := isOpen_Pd n R
  have hb_norm : ∀ (i : ℕ), i ≤ 2 → ∀ z ∈ Pd n R,
      ‖iteratedFDerivWithin ℝ i u (Pd n R) z‖ ≤ b :=
    fun i hi z hz => norm_iteratedFDerivWithin_le_of_holderNorm_le hb0 hb hi hz
  have hb_sub : ∀ x ∈ Pd n R, ∀ y ∈ Pd n R,
      ‖iteratedFDerivWithin ℝ 2 u (Pd n R) x - iteratedFDerivWithin ℝ 2 u (Pd n R) y‖
        ≤ b * ‖x - y‖ ^ α :=
    fun x hx y hy => norm_sub_iteratedFDerivWithin_le_of_holderNorm_le hα0 hb0 hb le_rfl hx hy
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [← fderivWithin_of_mem_nhds (hPopen.mem_nhds hz),
      ← norm_iteratedFDerivWithin_one u (hPopen.uniqueDiffWithinAt hz)]
    exact hb_norm 1 (by norm_num) z hz
  · intro z hz
    rw [norm_fderiv_fderiv_eq_iteratedFDeriv_two,
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := u) (s := Pd n R) 2 hPopen hz]
    exact hb_norm 2 le_rfl z hz
  · intro x hx y hy
    rw [norm_fderiv_fderiv_sub_eq_iteratedFDeriv_two,
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := u) (s := Pd n R) 2 hPopen hx,
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := u) (s := Pd n R) 2 hPopen hy]
    exact hb_sub x hx y hy

end Work.NN.Newton
