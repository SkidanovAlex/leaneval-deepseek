/-
# The two protected pieces of `Work.KMTPlan.A6.BoundedHMain`

`Work.KMTPlan.A6.BoundedHMain` is the bounded-height (`lcL l₁ l₂ k₁ k₂ ≤ B`), low-case
(`k₁ = 0 ∨ k₂ = 0`) form of the `(2,2,1)` large-scale estimate of Krause--Mirek--Tao for the
concrete §5 columns `mainPartTuple`, for **every** `ρ ∈ (0,1]` and **every** `B`, and **without**
the unproved deep input `AreaA1` (the Ionescu--Wainger multiplier theorem at even exponents):
at bounded height the smallness restriction on `ρ` disappears (the weights of §6/§8 become
constants, and every arithmetic frequency set has at most `|(ℚ/ℤ)_{≤B}|` elements).

The estimate is assembled in `BoundedHMain.lean` from the pointwise splitting

  `mainPartTuple = modelTupleRep + (mainPartTuple − modelTupleRep)`

(the `§8` model `modelTupleRep` of `Work.KMTAreas.A7.Large.Defs`, plus the `§6` model-approximation
error), by the subadditivity of the variational norm and of the `ℒ¹`-seminorm, exactly as the
sibling `Submission/Work/KMTPlan/A6/PieceBoundedH/mainPiece.lean` does — except that the two
non-elementary halves are stated here *without* `AreaA1` and for `ρ ≤ 1`, and the third
(off-`hiCore`) range is the following degenerate case:

* in the range `l₁ = 0 ∨ l₂ = 0` the repaired model `modelTupleRep` vanishes identically
  (`Tex ρ 0 = 0`, because `iwArithFreqsNew ρ 0 = ∅`), so `mainPartTuple` there is estimated
  directly, which is the "height-zero" chapter of the paper (the `l = 0` half of `mod-approx`
  together with the mixed `§6`--`§8` range).

This file fixes the two `Prop`s used by that assembly, so that the two deferred provers can state
their results in the same vocabulary.

* `ModelPieceBound P r C₀ ρ B` — the `§8` bound for the repaired model `modelTupleRep` at bounded
  height, in the low case, at the fixed parameter `ρ ≤ 1`.
* `HeightZeroMainBound P r C₀ ρ B` — the same bound for the concrete column `mainPartTuple` in the
  degenerate range `l₁ = 0 ∨ l₂ = 0`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- **The `§8` model bound for the repaired model `modelTupleRep` at bounded height.**

For `0 < ρ ≤ 1` and every height bound `B` there is a constant `K : ℝ≥0 → ℝ≥0` such that for every
`Λ`-lacunary scale sequence `a` with `a n ≥ 1`, every quadruple of heights with
`lcL l₁ l₂ k₁ k₂ ≤ B` in the low case `k₁ = 0 ∨ k₂ = 0`, and all `f, g`,

  `‖ V^r_n (modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n ·) ‖_{ℓ¹(ℤ)} ≤ K(Λ) ‖f‖₂ ‖g‖₂`.

No `AreaA1` and no `MemLp` hypotheses occur: at bounded height every loss of the `§6`/`§8`
bookkeeping (`repWeight`, `uRep`, the number `|(ℚ/ℤ)_{≤l}|` of arithmetic frequencies, the
number of off-band scales) is a constant depending only on `ρ` and `B`. -/
def ModelPieceBound (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
      lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **The degenerate range `l₁ = 0 ∨ l₂ = 0` of the concrete column.**

For `0 < ρ ≤ 1` and every height bound `B` there is `K : ℝ≥0 → ℝ≥0` such that for every
`Λ`-lacunary `a ≥ 1`, every quadruple with `lcL l₁ l₂ k₁ k₂ ≤ B`, in the low case
`k₁ = 0 ∨ k₂ = 0` and with one of the two arithmetic heights equal to `0`,

  `‖ V^r_n (mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n ·) ‖_{ℓ¹(ℤ)} ≤ K(Λ) ‖f‖₂ ‖g‖₂`.

This is the range where the repaired model vanishes, so no model approximation is available and
the estimate is a direct one for the concrete columns. -/
def HeightZeroMainBound (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
      lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → (l₁ = 0 ∨ l₂ = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

end

end Work.KMTPlan.A6
