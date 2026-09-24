import Mathlib
import Submission.Work.GM.Trace.Defs

namespace Work.GM.Trace

open Complex MeasureTheory
open scoped Real

open Submission.GM Submission.LargeValues

/-- `‖h_t(u)‖ = w(u)²` for **every** `u`: for `u > 0` the phase `u^{it}` has modulus one
(`norm_hfun_of_pos`), while for `u ≤ 0` both sides vanish because `w` is supported in `[1,2]`. -/
theorem norm_hfun (t u : ℝ) : ‖hfun t u‖ = bumpW u ^ 2 := by
  rcases le_or_gt u 0 with hu | hu
  · have h1 : u ∉ Set.Icc (1 : ℝ) 2 := by
      simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith
    rw [hfun, bumpW_eq_zero_of_notMem h1]; simp
  · exact norm_hfun_of_pos t u hu

/-- The trivial uniform bound `‖ĥ_t(ξ)‖ ≤ ∫ ‖h_t‖ = ∫ w² = Azero`, used to bound the "other"
factors in each term of GM's `S₁, S₂, S₃`.

Suggested route: `‖FourierTransform.fourier f ξ‖ ≤ ∫ ‖f‖` (`norm_fourier_le`), and
`‖hfun t u‖ = w(u)²` for `u > 0` (`Work.GM.Trace.norm_hfun_of_pos`), `0` for `u ≤ 0` (since
`bumpW u = 0` there); so `∫ ‖hfun t‖ = ∫ w² = Azero` (`Work.GM.Trace.Azero`). -/
theorem hhat_norm_le_Azero (t ξ : ℝ) :
    ‖Submission.GM.hhat t ξ‖ ≤ Work.GM.Trace.Azero := by
  rw [Submission.GM.hhat, Real.fourier_eq]
  calc ‖∫ v : ℝ, Real.fourierChar (-inner ℝ v ξ) • hfun t v‖
      ≤ ∫ v : ℝ, ‖Real.fourierChar (-inner ℝ v ξ) • hfun t v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v : ℝ, ‖hfun t v‖ := by
        apply integral_congr_ae
        filter_upwards with v
        rw [Circle.norm_smul]
    _ = ∫ v : ℝ, bumpW v ^ 2 := by
        apply integral_congr_ae
        filter_upwards with v
        exact norm_hfun t v
    _ = Work.GM.Trace.Azero := rfl

end Work.GM.Trace
