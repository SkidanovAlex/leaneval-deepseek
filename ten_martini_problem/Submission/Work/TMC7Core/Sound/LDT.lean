import Submission.Work.TMComp.RedC7.large_deviation

/-!
# A sound large deviation theorem for C7

`Submission/Work/TMC7Core/Fourier/large_deviation.lean` routes its arithmetic leg through
`Fourier/blk_block_bound`, which the C11 agent **refuted** (exact counterexample in
`Submission/Work/TMComp/RedC7/NOTES_blk_counterexample.md`), so it should not be used.  The
replacement `Work.TMComp.RedC7.large_deviation` has the *same type* and is sorry-free and
axiom-clean; this file re-exports it under the `TMC7Core` name so that callers of
`Work.TMC7Core.BJ.assembly` can supply a trustworthy `hLDT`.

(Kept in a separate module to avoid an import cycle: `RedC7` imports parts of `TMC7Core`.)
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-- **Sound LDT** (drop-in for `Fourier.large_deviation`): for every `lam, E₀` there are
`c, C, r > 0` with `HasLDTOn lam (Icc (E₀-r) (E₀+r)) c C`. -/
theorem large_deviation_sound (lam E₀ : ℝ) :
    ∃ c C r : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 < r ∧ HasLDTOn lam (Set.Icc (E₀ - r) (E₀ + r)) c C :=
  Work.TMComp.RedC7.large_deviation lam E₀

end Work.TMC7Core
