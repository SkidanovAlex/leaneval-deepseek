import Mathlib
import Submission.Work.Diff.STE.Lead.KSBP.DiffMassDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `dw` is dominated by the Fréchet `w.length`-th derivative

For a smooth `Φ : ℝⁿ → F` and a word `w` of coordinate directions, the iterated directional
derivative `dw w Φ z` is exactly the `w.length`-th Fréchet derivative of `Φ` at `z`, evaluated
on the tuple `wvec w` of coordinate unit vectors.  The norm of that evaluation is bounded by the
operator norm of the multilinear map (times the product of the norms of the directions, which is
`1`), which is the estimate `norm_dw_le_iteratedFDeriv`.

The identification `dw w Φ = fun z => iteratedFDeriv ℝ w.length Φ z (wvec w)` is proved by
induction on the word, peeling the *first* variable of the multilinear map
(`iteratedFDeriv_succ_apply_left`, which is `rfl`) and using that the derivative of
`y ↦ L y u` (for `L` a multilinear-map-valued function and `u` a fixed tuple) is the derivative
of `L` applied to `u` (`fderiv_continuousMultilinear_apply_const_apply`).
-/

noncomputable section

namespace Work.Diff.STE.Lead.KSBP

/-- The iterated directional derivative along the word `w` is the `w.length`-th Fréchet
derivative, evaluated on the tuple of coordinate unit vectors indexed by `w`. -/
lemma dw_eq_iteratedFDeriv_wvec {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : List (Fin n)) {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    dw w Φ = fun z => iteratedFDeriv ℝ w.length Φ z (wvec w) := by
  induction w with
  | nil =>
      funext z
      simp
  | cons i w ih =>
      funext z
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length Φ) z := by
        have hlt := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top w.length)
        exact (hΦ.differentiable_iteratedFDeriv (m := w.length) hlt).differentiableAt
      show fderiv ℝ (dw w Φ) z (Pi.single i (1 : ℝ)) =
        (iteratedFDeriv ℝ (w.length + 1) Φ z) (wvec (i :: w))
      rw [ih]
      rw [fderiv_continuousMultilinear_apply_const_apply hd (wvec w) (Pi.single i (1 : ℝ))]
      rw [iteratedFDeriv_succ_apply_left]
      rw [wvec_cons_zero, wvec_cons_tail]

theorem norm_dw_le_iteratedFDeriv {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : List (Fin n)) {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.Lead.KSBP.dw w Φ z‖ ≤ ‖iteratedFDeriv ℝ w.length Φ z‖ := by
  rw [dw_eq_iteratedFDeriv_wvec w hΦ]
  calc ‖iteratedFDeriv ℝ w.length Φ z (wvec w)‖
      ≤ ‖iteratedFDeriv ℝ w.length Φ z‖ * ∏ j, ‖wvec w j‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ w.length Φ z‖ := by simp [wvec, Pi.norm_single]

end Work.Diff.STE.Lead.KSBP
