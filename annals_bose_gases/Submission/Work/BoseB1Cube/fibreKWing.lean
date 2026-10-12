import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB1Cube.chiFibreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-dimensional wing bound for the `chiSmall` fibre kernel

`chiFibreK M A B t = (ζ(A − t)·ζ(B − t))^M` with `ζ = zeta1d`.  Away from the
value `t = A` (resp. `t = B`) at distance at least `1/2 − δ'`, the face decay
`ζ(y) ≤ 4·(1/2 − |y|)₊` of the cosine profile gives `ζ(y) ≤ 4·δ'`, hence both
factors of the product are `≤ 4·δ'` and the `M`-th power is
`≤ ((4δ')²)^M = (4δ')^{2M}`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.BoseB1Cube

open Submission.BoseGases

/-- **Face decay of `ζ` in absolute constants.**  If `y` is at distance at least
`1/2 − δ'` from the face `|y| = 1/2` (i.e. `1/2 − δ' ≤ |y|`) with `δ' > 0`, then
`ζ(y) ≤ 4·δ'`. -/
lemma zeta1d_le_four_mul_of_sub_le_abs {y δ' : ℝ} (hδ' : 0 < δ')
    (hy : 1 / 2 - δ' ≤ |y|) : zeta1d y ≤ 4 * δ' := by
  have h := zeta1d_le_four_max y
  have hmax : max (1 / 2 - |y|) 0 ≤ δ' :=
    max_le (by linarith) (le_of_lt hδ')
  calc zeta1d y ≤ 4 * max (1 / 2 - |y|) 0 := h
    _ ≤ 4 * δ' := mul_le_mul_of_nonneg_left hmax (by norm_num)

theorem fibreKWing {M : ℕ} (hM : 1 ≤ M) {δ' A B t : ℝ} (hδ' : 0 < δ')
    (hA : 1 / 2 - δ' ≤ |A - t|) (hB : 1 / 2 - δ' ≤ |B - t|) :
    Work.BoseB1Cube.chiFibreK M A B t ≤ (4 * δ') ^ (2 * M) := by
  have hAt : zeta1d (A - t) ≤ 4 * δ' := zeta1d_le_four_mul_of_sub_le_abs hδ' hA
  have hBt : zeta1d (B - t) ≤ 4 * δ' := zeta1d_le_four_mul_of_sub_le_abs hδ' hB
  have h4 : 0 ≤ 4 * δ' := by linarith
  have h0 : 0 ≤ zeta1d (A - t) * zeta1d (B - t) :=
    mul_nonneg (zeta1d_nonneg _) (zeta1d_nonneg _)
  have h1 : zeta1d (A - t) * zeta1d (B - t) ≤ (4 * δ') * (4 * δ') :=
    mul_le_mul hAt hBt (zeta1d_nonneg _) h4
  have hpow := pow_le_pow_left₀ h0 h1 M
  unfold chiFibreK
  calc (zeta1d (A - t) * zeta1d (B - t)) ^ M
      ≤ ((4 * δ') * (4 * δ')) ^ M := hpow
    _ = (4 * δ') ^ (2 * M) := by
        rw [show (4 * δ') * (4 * δ') = (4 * δ') ^ 2 by ring, ← pow_mul]

end Work.BoseB1Cube
