import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.Defs
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.CSq_trunc_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-- **The Friedrichs cutoff is contractive on `CSq t`.**  (Route: `Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut` says `fourierCoeff (flatCut ρ ε w) = trunc ρ ε (fourierCoeff w)`, and `trunc` only multiplies the `m`-th coefficient by the complex number `ρ (ε • m)` of modulus `≤ 1`, so the weighted summands are pointwise dominated; summability of the right-hand side follows from smoothness and `1`-periodicity of `w`.) -/
theorem flatCut_CSq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℝ) → ℝ)
    (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (t : ℕ) (w : (ι → ℝ) → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwp : Work.Diff.STE.Periodic1 w) :
    Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε w))
      ≤ Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff w) := by
  -- The Fourier coefficients of `flatCut ρ ε w` are `trunc ρ ε (fourierCoeff w)`.
  have hfc : Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε w)
      = Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff w) :=
    funext fun k => Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hw hwp k
  -- Summability of the weighted `ℓ²` family of the Fourier coefficients of `w`.
  have hc : Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ t * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) :=
    Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff t hw hwp
  rw [hfc]
  exact Work.Diff.STE.CSq_trunc_le ρ hρ ε t (Work.Diff.STE.fourierCoeff w) hc

end Work.Diff.STE.B3.SymCalcStep7
