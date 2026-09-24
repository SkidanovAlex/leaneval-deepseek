import Mathlib
import Submission.Work.GM.S3.gen_defs

/-!
# The two statement-level inputs of the cell route, as `Prop`s

`Work.GM.S3.Gen.S30g_le_cell` (the per-cell bound) and `Work.GM.S3.Gen.S3_le_cellSum` (the cell
decomposition) are stated below as `Prop`s so that the final assembly
`Work.GM.S3.Gen.s3_of_cellSum_of` can be stated and proved *with them as hypotheses*, without
importing the (possibly still unfinished) files that prove them.  Each is written as the identical
formula, so the proved theorems are definitionally instances:

`example : CellBoundStatement hAff hL84 := S30g_le_cell hAff hL84`
`example : CellSumStatement := S3_le_cellSum`

(The `example`s are the job of the caller; `Prop`-valued definitions cannot take theorems as
witnesses.)
-/

namespace Work.GM.S3.Gen

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (Rfun energy Separated Iterm Spart affineSum)

/-- The per-cell bound of the §10 pipeline (GM 10.1, one cell of GM 7.2), for fixed bumps:
`S30g ≤ C N^ε (Mbig³ |W|^{3/2} + Mbig² |W|^{1/2} E(W)^{1/2})` whenever `32 ≤ N B` and the three
cell scales are `≤ Mbig`. -/
def CellBoundStatement (hAff : Submission.GM.AffineStatement)
    (hL84 : Work.GM.S3.Lemma84RelaxedStatement) : Prop :=
  ∀ (ψ₁ ψ₂ : ℝ → ℝ), Work.GM.S3.IsBumpAtZero ψ₁ 4 → Work.GM.S3.IsBumpAtOne ψ₂ 4 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ (B M₁ M₂ M₃ Mbig : ℝ), 32 ≤ (N : ℝ) * B →
      0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ Mbig →
      S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
        C * (N : ℝ) ^ ε * (Mbig ^ 3 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
          Mbig ^ 2 * (W.card : ℝ) ^ (1 / 2 : ℝ) *
            (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ))

/-- The cell decomposition (GM 7.2 in the cell form): the truncated sum of `‖I_m‖` is bounded by
the sum over the cells of `cellFam` with the matched smoothing `Bdy`, plus the two error terms. -/
def CellSumStatement : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
  ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
    Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
  ∀ (ψ₁ ψ₂ : ℝ → ℝ), Work.GM.S3.IsBumpAtZero ψ₁ 4 → Work.GM.S3.IsBumpAtOne ψ₂ 4 →
    (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) → (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) →
  (∑ m₁ ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋,
    ∑ m₂ ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋,
    ∑ m₃ ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋,
      if (m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0) then ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0) ≤
    C * (N : ℝ) ^ δ * cellSum N W δ (δ / 2) (cellJ N δ) ψ₁ ψ₂ +
      C * (N : ℝ) ^ δ * (Submission.LargeValues.M N) ^ (3 * (δ / 2)) * (W.card : ℝ) ^ 3 +
      C * (N : ℝ) ^ (-10 : ℤ)

end Work.GM.S3.Gen
