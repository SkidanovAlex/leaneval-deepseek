/-
# `Work.FTS.PhiStar.FlatWAux.MomentChiaAux.Defs` — the resummed angular coefficients

The resummed angular profile `chia ψ j = sin 2θ · Wt ψ j` of `FlatWAux/Defs.lean` is, for
`j ≥ 1`, the eigenfunction series

  `chia ψ j θ = Σ_m bco ψ j m · eFam m θ`,   `bco ψ j m = bmode m ψ · (lam m)⁻¹ ^ j`

on the open interval `(0, π/2)` (`chia_eq_tsum`, restated here as `chia_eq_tsum_bco`).  This
file fixes the coefficient notation used by the sibling lemmas of this directory and records
the two elementary facts about it (`bco ψ 0 m = bmode m ψ`, `bco ψ j 0 = 0` for `j ≥ 1`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

set_option autoImplicit false

/-- The `m`-th coefficient of the eigenfunction series of `chia ψ j`, i.e.
`bco ψ j m = bmode m ψ · (lam m)⁻¹ ^ j`.  For `j ≥ 1` the `m = 0` coefficient vanishes
(`lam 0 = 0`), and for `j = 0` the series is the `eFam`-expansion of `ψ` itself. -/
def bco (ψ : ℝ → ℝ) (j m : ℕ) : ℝ :=
  Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j

/-- The `j = 0` coefficient is the `bmode` coefficient of `ψ`. -/
@[simp] theorem bco_zero (ψ : ℝ → ℝ) (m : ℕ) :
    bco ψ 0 m = Work.FTS.PhiStar.Series.bmode m ψ := by
  simp only [bco, pow_zero, mul_one]

/-- The `m = 0` coefficient vanishes for `j ≥ 1`, because `lam 0 = 0`. -/
theorem bco_apply_zero (ψ : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) : bco ψ j 0 = 0 := by
  have hlam : Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    norm_num
  simp only [bco, hlam, inv_zero, zero_pow (by omega : j ≠ 0), mul_zero]

/-- On the open interval, `chia ψ j` (`j ≥ 1`) is the `eFam`-series with coefficients
`bco ψ j`. -/
theorem chia_eq_tsum_bco (ψ : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.PhiStar.FlatWAux.chia ψ j θ
      = ∑' m : ℕ, bco ψ j m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
  simpa only [bco] using Work.FTS.PhiStar.FlatWAux.chia_eq_tsum ψ k hθ

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
