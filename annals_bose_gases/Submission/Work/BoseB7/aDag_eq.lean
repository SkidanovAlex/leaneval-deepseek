import Mathlib.Tactic.Module
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.aDag_eq` — FS `eq:asInTermsOfbs` for the creation operators

FS §10 (`eq:asInTermsOfbs`) inverts the squeezing substitution

  `b_k = a_k + α_k a_{-k}†`

to express the bare operators through the `b`'s.  Solving the pair of linear
relations `b_k = a_k + α_k a_{-k}†` and `b_{-k}† = a_{-k}† + α_{-k}a_k` (evenness
of `α`) gives

  `a_k  = (1-α_k²)⁻¹ (b_k - α_k b_{-k}†)`,
  `a_k† = (1-α_k²)⁻¹ (b_k† - α_k b_{-k})`.

This file proves the *creation* half.  It is pure linear-algebra bookkeeping on
the module `F.H`: the bracket is `(1-α_k²) • a_k†` by unfolding
`bOpDag α k = a_k† + α_k a_{-k}` and `bOp α (-k) = a_{-k} + α_{-k}a_k†`, and the
inverse of the scalar `1-α_k²` cancels because `1-α_k² ≥ ½` under FS's smallness
`eq:BoverA` (`2|ℬ| ≤ 𝒜`), see `half_le_one_sub_alphaCoef_sq`.

## Contents

* `aDag_eq` — the requested statement.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- FS `eq:asInTermsOfbs` for creation operators: the squeezed mode `b`'s invert
to `a_k† = (1-α_k²)⁻¹(b_k† - α_k b_{-k})`. -/
theorem aDag_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (h : Work.BoseB7.EstHyp F E) (i : Mode) :
    F.aDag i = (1 - E.alpha i ^ 2)⁻¹ • (F.bOpDag E.alpha i - (E.alpha i) • F.bOp E.alpha (-i)) := by
  -- FS's smallness `2|ℬ_i| ≤ 𝒜_i` makes the denominator `1-α_i²` nonzero (`≥ ½`).
  have hpos : 0 < 1 - E.alpha i ^ 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (half_le_one_sub_alphaCoef_sq (h.Apos i) (h.Bsmall i))
  -- the bracket is exactly `(1-α_i²) • a_i†`: unfold `b_k = a_k + α_k a_{-k}†`,
  -- `b_k† = a_k† + α_k a_{-k}` and use the evenness `α_{-i} = α_i`.
  have hkey : F.bOpDag E.alpha i - (E.alpha i) • F.bOp E.alpha (-i)
      = (1 - E.alpha i ^ 2) • F.aDag i := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
      FockData.bOp, FockData.bOpDag, h.alphaEven i, neg_neg]
    module
  rw [hkey, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul]

end Work.BoseB7
