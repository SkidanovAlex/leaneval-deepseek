import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.bogoliubov_one_mode` — the scalar one-mode Bogoliubov (LHY) inequality

The purely algebraic core of FS's one-mode Bogoliubov (LHY) bound.  Writing
`s = √(α² − β²)` and `k = β/(α + s)`, the two numerical inputs are

* `hTP : T − P ≤ c` — the commutator input `T ≤ P + c`;
* `hU  : 0 ≤ P + 2k·R + k²·T` — the positivity of the Bogoliubov-transformed quadratic form,

and the conclusion is the sharp (LHY) background bound

`−((α − s)/2)·c ≤ α·P + β·R` .

## Proof

The whole content is the identity

`α·P + β·R + ((α − s)/2)·c = ((α + s)/2)·(P + 2k·R + k²·T) + ((α − s)/2)·(P + c − T)`

which uses only `k·(α + s) = β` and `k²·(α + s) = α − s` (the latter is
`β²/(α + s) = α − s`, i.e. `s² = α² − β²`).  Both coefficients `(α ± s)/2` are
non-negative (`s ≤ α` because `β² ≤ α²`), `hU` makes the first summand `≥ 0`, and
`hTP` makes `P + c − T ≥ 0`, so the second summand is `≥ 0` too.  This is the
"completion of squares" which is exactly sharp: equality holds at the Bogoliubov
critical point.
-/

namespace Work.BoseFixB1

set_option linter.unusedVariables false

lemma bogoliubov_one_mode {α β P R T c : ℝ} (hα : 0 < α) (hβ : |β| ≤ α) (hc : 0 ≤ c)
    (hTP : T - P ≤ c)
    (hU : 0 ≤ P + 2 * (β / (α + Real.sqrt (α ^ 2 - β ^ 2))) * R
      + (β / (α + Real.sqrt (α ^ 2 - β ^ 2))) ^ 2 * T) :
    - ((α - Real.sqrt (α ^ 2 - β ^ 2)) / 2) * c ≤ α * P + β * R := by
  set s := Real.sqrt (α ^ 2 - β ^ 2) with hs
  have hb2 : β ^ 2 ≤ α ^ 2 := by
    rw [sq_le_sq]
    rwa [abs_of_pos hα]
  have hs2 : s ^ 2 = α ^ 2 - β ^ 2 := by
    rw [hs]; exact Real.sq_sqrt (by linarith)
  have hsnn : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hsle : s ≤ α := by
    have h1 : s ^ 2 ≤ α ^ 2 := by nlinarith [hs2, sq_nonneg β]
    have h2 : |s| ≤ |α| := sq_le_sq.mp h1
    rwa [abs_of_nonneg hsnn, abs_of_pos hα] at h2
  have hden : (0:ℝ) < α + s := by linarith
  set k := β / (α + s) with hk
  have hA : k * (α + s) = β := by rw [hk]; exact div_mul_cancel₀ β (ne_of_gt hden)
  have hB : k ^ 2 * (α + s) = α - s := by
    rw [hk, div_pow]
    field_simp
    nlinarith [hs2]
  have hker : α * P + β * R + (α - s) / 2 * c
      = (α + s) / 2 * (P + 2 * k * R + k ^ 2 * T) + (α - s) / 2 * (P + c - T) := by
    linear_combination (-R) * hA - (T / 2) * hB
  have h1 : 0 ≤ (α + s) / 2 * (P + 2 * k * R + k ^ 2 * T) :=
    mul_nonneg (by linarith) hU
  have h2 : 0 ≤ (α - s) / 2 * (P + c - T) :=
    mul_nonneg (by linarith) (by linarith)
  linarith [h1, h2, hker]

end Work.BoseFixB1
