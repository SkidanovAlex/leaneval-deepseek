import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseB6Est.GFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.cellSplitDefs` — the `(τ,β)`-part of the clean bracket

The scaled clean bracket `psiSc v h ρ μ t = 𝒵(τ_s+β_s, β_s) − β_s²/(2‖t‖²)` is
`Work.BoseB6Est.gFun (tauSc t) (betaSc t) ‖t‖` (definitionally), and `gFun` splits as

  `gFun τ β r = cellPhi τ β − β²/(2r²)`,   `cellPhi τ β = τ + β − √(τ² + 2τβ)`.

The point of the split is that the `1/r²`-part of `gFun` is separated from the
square-root part: the two-point oscillation of `psiSc` is then a `τ`-increment of
`cellPhi`, a `β`-increment of `cellPhi` and a purely radial difference
(`Work.BoseBogFS.psiSc_cell_sqrt_le`, whose three pieces are the lemmas
`Work.BoseBogFS.cellPhi_tau_le`, `Work.BoseBogFS.cellPhi_beta_le` and
`Work.BoseBogFS.radialPair_le`).

Note the *junk* convention of `Real.sqrt`: `Real.sqrt x = 0` for `x < 0`.  The
definition above is therefore the honest `𝒵(τ+β,β)` for **all** `β ∈ ℝ` and
`τ ≥ 0` (the case in which `τ² + 2τβ < 0` never arises on the branch
`|β| ≤ τ/2`, and outside it both `Real.sqrt` and `bogZeroPoint` degenerate in the
same way, which is exactly what the three pieces above formalise).
-/

noncomputable section

namespace Work.BoseBogFS

/-- The `(τ,β)`-part `τ + β − √(τ² + 2τβ)` of the clean bracket: `gFun` with its
`1/r²`-part removed. -/
def cellPhi (τ β : ℝ) : ℝ := τ + β - Real.sqrt (τ ^ 2 + 2 * τ * β)

/-- **The split of `gFun`**: the radial part is separated from the square-root part. -/
lemma gFun_eq_cellPhi (τ β r : ℝ) :
    Work.BoseB6Est.gFun τ β r = cellPhi τ β - β ^ 2 / (2 * r ^ 2) := by
  rw [Work.BoseB6Est.gFun, cellPhi]
  have h : (τ + β) ^ 2 - β ^ 2 = τ ^ 2 + 2 * τ * β := by ring
  rw [h]

end Work.BoseBogFS
