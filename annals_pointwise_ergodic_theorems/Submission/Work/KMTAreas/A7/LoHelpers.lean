/-
# Helpers for the level-`0` large-scale analysis (Area A7)

Small, independent facts used by `Work.KMTAreas.A7.LoModelLargeScale` and by the pieces of its
proof (the low-pass variational estimates, the `Farey`/bad-scale analysis, the final assembly).

The main item is `variationalNorm_comp_mono_le`: the `r`-variational norm of a *reindexed* family
`n ↦ u (φ n)` is at most that of `u`, for every monotone `φ : ℕ → ℕ`.  This is what lets a
`Λ`-lacunary family of scales (`Λ ∈ (1,2)` for instance) be compared with a `2`-lacunary one:
the dyadic levels `logN (⌊a n⌋)` of a lacunary `a` are monotone, so
`V^r_n (bumpOp K (2^{logN ⌊a n⌋}) 0 f) ≤ V^r_m (bumpOp K (2^m) 0 f)`.
-/
import Mathlib
import ChallengeDeps
import Submission.VarNorm

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **Reindexing a family by a monotone map does not increase its variational norm.** -/
theorem variationalNorm_comp_mono_le {r : NNReal} (u : ℕ → ℂ) {φ : ℕ → ℕ} (hφ : Monotone φ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => u (φ n)) ≤
      PointwiseErgodicTheorems.variationalNorm r u := by
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
    Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  refine add_le_add ?_ ?_
  · exact iSup_le fun n => le_iSup (fun n => ‖u n‖ₑ) (φ n)
  · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    refine le_iSup_of_le J (le_iSup_of_le (fun i => φ (N i)) (le_iSup_of_le ?_ le_rfl))
    exact hφ.comp hN

end

end Work.KMTAreas.A7
