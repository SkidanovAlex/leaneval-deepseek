import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lemma_9_2
import Submission.Work.TMC16Core.Basic.lemma_9_3
import Submission.Work.TMC16Core.Basic.pd_upper
import Submission.Work.TMC16Core.Basic.pd_fourier_large
import Submission.Work.TMC16Core.Basic.singular_of_ne_zero
import Submission.Work.TMC16Core.Basic.regular_of_uniform
import Submission.Work.TMC16Core.Basic.green_bound_notA
import Submission.Work.TMC16Core.CF.cf_data_bridge
import Submission.Work.TMC16Core.Trig.irrat_block
import Submission.Work.TMC16Core.Trig.shift_block
import Submission.Work.TMC16Core.Core.uni_res5
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.uni_nonres3_havoid
import Submission.Work.TMC16Core.Core.Ablock_res_win
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.TMC16Core.Core.pd_step_nr
import Submission.Work.TMC16Core.Core.scale_sel_nr
import Submission.Work.TMC16Core.Core.res_win_fit
import Submission.Work.TMC16Core.Core.pd_window_helpers
import Submission.Work.TMC16Core.Core.orbit_blkmin
import Submission.Work.TMC16Core.Core.blk_sep_base
import Submission.Work.TMC16Core.Core.setup
import Submission.Work.TMC16Core.Assembly.Glue

namespace Work.TMC16Core.Main

/-- **C16 core (AJ §9, Lemmas 9.4 and 9.5).**  For `DiophBelow α b₀` with `0 < b₀` and
`λ > e^{16b₀/9}`, outside the null set `Θ`, a nontrivial generalized eigenfunction with
`u 0 ≠ 0` produces the multiscale regularity family.

This is no longer a gap: it is the two-line application of the assembled chapter
`Work.TMC16Core.Assembly.glue` (see `Submission/Work/TMC16Core/Assembly/NOTES.md` §8 for the
structure of that proof and the list of branch lemmas it consumes).

It consumes C7 only in its Diophantine form `P_BJ_dioph` (the Lyapunov exponent on the
spectrum equals `log λ`), which is what AJ §9 uses (`L = log λ`).  We are now in the
Diophantine regime, so `λ > 1` and `b₀ > 0`. -/
theorem pd_window_reg_dioph (h4 : Work.TMC16Core.P_LEBasics)
    (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam)
    {θ : ℝ} (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    Work.TMC16Core.RegFamily α lam θ E :=
  Work.TMC16Core.Assembly.glue h4 h7 hα hb₀ hDioph hlam hE hθ hu hu0

/-- The `0 ≤ b₀` form of `pd_window_reg_dioph`: for `b₀ = 0` the hypothesis
`DiophBelow α 0` is unsatisfiable (`Core.diophBelow_zero_false`). -/
theorem pd_window_reg_dioph_le (h4 : Work.TMC16Core.P_LEBasics)
    (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 ≤ b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam)
    {θ : ℝ} (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    Work.TMC16Core.RegFamily α lam θ E := by
  rcases eq_or_lt_of_le hb₀ with h | h
  · exact absurd (h ▸ hDioph) Work.TMC16Core.Core.diophBelow_zero_false
  · exact pd_window_reg_dioph h4 h7 hα h hDioph hlam hE hθ hu hu0

/-- The historical `P_BJ`-flavoured form (kept for backward compatibility of the frozen
`P_RegFamily` statement; `P_BJ` restricts to `P_BJ_dioph`). -/
theorem pd_window_reg (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 ≤ b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam)
    {θ : ℝ} (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    Work.TMC16Core.RegFamily α lam θ E :=
  pd_window_reg_dioph_le h4 (Work.TMC16Core.Core.p_bj_dioph_of_p_bj h7) hα hb₀ hDioph hlam hE hθ
    hu hu0

end Work.TMC16Core.Main
