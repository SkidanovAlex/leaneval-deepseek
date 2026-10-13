import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WDp 4 f ≤ 25 * M` from a pointwise bound on the open quadrant

`Work.FTS.VocabO.WDp l f` is the double sum of the open-quadrant sups
`Work.FTS.H2.supAbsO (mixed b j f)` over the pairs `b, j ≤ l` with `b + j ≤ l`
(`mixed b j f = D_z^b D_θ^j f`, `D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`).

`supAbsO` is the supremum of `|g|` over the **same** open quadrant
`{z > 0, 0 < θ < π/2}` on which the hypothesis `h` supplies its pointwise bound,
so `Work.FTS.H2.supAbsO_le` turns `h` into `supAbsO (mixed b j f) ≤ M` for every
relevant pair.  The double sum has `(4+1) · (4+1) = 25` entries (the entries with
`b + j > 4` contribute the junk value `0 ≤ M`, using `hM`), whence `WDp 4 f ≤ 25 * M`
— the constant 25 is deliberately loose (15 would do).

The `open scoped Real` below is needed for the `π` of the statement to denote
`Real.pi`: the supremum defining `supAbsO` ranges over `0 < θ < Real.pi / 2`, and
the hypothesis has to be about that very interval, which it is only if the `π / 2`
occurring in the statement is `Real.pi / 2`.
-/

open scoped Real

namespace Work.FTS.OpenPkg

theorem WDp_le_of_pointwise {α M : ℝ} {f : ℝ → ℝ → ℝ} (hM : 0 ≤ M)
    (h : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j f z θ| ≤ M) :
    Work.FTS.VocabO.WDp 4 f ≤ 25 * M := by
  classical
  rw [Work.FTS.VocabO.WDp]
  calc
    ∑ b ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if b + j ≤ 4 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0)
      ≤ ∑ b ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1), M := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with hbj
        · exact Work.FTS.H2.supAbsO_le (fun z θ hz hθ hθ' => h b j hbj z θ hz hθ hθ')
        · exact hM
    _ = 25 * M := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end Work.FTS.OpenPkg
