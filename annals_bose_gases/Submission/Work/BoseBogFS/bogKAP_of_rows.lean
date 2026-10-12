import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseBogFS.kapArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.bogKAP_of_rows` — the `𝒞`-slot from three scalar rows

This module turns FS's p. 69 estimate (`thm:BogHamDiag`'s `hkappa`) into a statement about an
*abstract* `Q3Env`: the `𝒞`-sum of the Bogoliubov quadratic `KzBogFS` is bounded by
`(ρ − μ)² (ĝ(0)/2) ℓ³ (1 + 4(δ' + δ₁ + δ₂))` as soon as

* `Σ_k χ̂(kℓ)² ≤ 1 + δ₁` (the localisation normalisation; `δ₁ = 0` at the honest box data,
  where the lattice Parseval identity holds),
* `0 < 𝒜(0) = τ(0) + ρŴ₁(0)` and `ρŴ₁(0) ≤ 8πa(1 + δ')` (the mass/`ĝ(0)` row),
* `2ρŴ₁(0)(1 − δ₂) ≤ τ(k) + 2ρŴ₁(k)` for every mode (FS's "`𝒜+ℬ ≥ 2ρ_zŴ₁(0)(1−C(μa³)R²/a²)`,
  from the second-order variation of `Ŵ₁` and the kinetic domination),

with `δ', δ₁, δ₂ ∈ [0, 1/2]`.  The arithmetic is `Work.BoseBogFS.kapArith`; this module only
identifies the abstract-group summands with the `bogA`/`bogB`/`bogC` of the chapter.

## Why `W₀ = E.W1 0` and not `8πa`

The `𝒞`-coefficient is `𝒞(k) = (ρ − μ)·Ŵ₁(0)·χ̂(kℓ)·z` (`Work.BoseBogFS.bogC`), so the
denominator row and the mass row both refer to `Ŵ₁(0) = E.W1 0`, *not* to FS's `ĝ(0) = 8πa`.
The gap `Ŵ₁(0) − 8πa = 8πa·δ'` is genuinely positive at the honest box data
(`∫W₁ ≥ ∫g₀ = 8πa`, with equality only if `(χ⋆χ)(·/ℓ) ≡ 1` on `supp g₀`), which is exactly why
the envelope routes `FsMatch`/`FsMatchLe` are not inhabitable — see
`FINDING_honest_rows_session7.md` (a).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The `𝒞`-slot from three scalar rows.**  At an abstract `Q3Env`, FS's `hkappa` holds with
the explicit error `4(δ' + δ₁ + δ₂)` as soon as the mass row `0 < E.W1 0 ≤ 8πa(1+δ')`, the
χ̂-normalisation `Σχ̂² ≤ 1 + δ₁` and the denominator row `2ρ(E.W1 0)(1−δ₂) ≤ τ k + 2ρW₁ k`
are available. -/
theorem bogKAP_of_rows (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (ρ gHat0 δ' δ₁ δ₂ : ℝ)
    (hρ : 0 < ρ) (hℓ : 0 ≤ E.ell) (hg0 : gHat0 = 8 * π * E.aScat)
    (hW0pos : 0 < E.W1 0) (hW0up : E.W1 0 ≤ 8 * π * E.aScat * (1 + δ'))
    (hδ'0 : 0 ≤ δ') (hδ'1 : δ' ≤ 1 / 2)
    (hδ₁0 : 0 ≤ δ₁) (hδ₁1 : δ₁ ≤ 1 / 2)
    (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1 / 2)
    (hchi : (∑ k : Mode, (E.hatChi k) ^ 2) ≤ 1 + δ₁)
    (hden : ∀ k : Mode, 2 * ρ * (E.W1 0) * (1 - δ₂) ≤ E.tau k + 2 * ρ * (E.W1 k)) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k)
        (bogC E ρ k))
      ≤ (ρ - E.mu) ^ 2 * (gHat0 / 2) * E.ell ^ 3 * (1 + 4 * (δ' + δ₁ + δ₂)) := by
  have hpos : ∀ k : Mode, 0 < E.tau k + 2 * ρ * (E.W1 k) := by
    intro k
    have h1 : 0 < 1 - δ₂ := by linarith
    have h0 : 0 < 2 * ρ * (E.W1 0) * (1 - δ₂) := by positivity
    exact lt_of_lt_of_le h0 (hden k)
  have ha : 0 ≤ E.aScat := by
    by_contra hcon
    have hle : E.aScat ≤ 0 := (not_le.mp hcon).le
    have h1 : 0 < 1 + δ' := by linarith
    have hp : (0 : ℝ) ≤ 8 * π := by positivity
    have hneg : 8 * π * E.aScat ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp hle
    have hzero : 8 * π * E.aScat * (1 + δ') ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg h1.le
    linarith [lt_of_lt_of_le hW0pos hW0up]
  have h := kapArith (fun k : Mode => E.hatChi k) (fun k : Mode => E.W1 k)
    (fun k : Mode => E.tau k) (E.W1 0) ρ E.mu E.ell E.aScat gHat0 δ' δ₁ δ₂
    hρ hℓ ha hg0 hW0pos hW0up hδ'0 hδ'1 hδ₁0 hδ₁1 hδ₂0 hδ₂1 hchi hden hpos
  simpa only [bogA, bogB, bogC, bogZ] using h

end Work.BoseBogFS
