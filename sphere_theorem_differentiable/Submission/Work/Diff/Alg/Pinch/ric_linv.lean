import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- The Ricci tensor of `linv a b Y`, for an algebraic curvature tensor `Y`.

Writing `linv a b Y = Y - c₁ • (Ric₀ Y ∧ id) - c₂ • (id ∧ id)` with
`c₁ = b/(1+(n-2)b)` and `c₂ = ((a/n)/(1+2(n-1)a))·scal Y`, and using the two contraction
formulas `ric (A ∧ id) = (tr A)·id + (n-2)A` (with `tr (Ric₀ Y) = 0`) and
`ric (id ∧ id) = (2n-2)·id`, this computes the displayed combination of `ric Y`, `Ric₀ Y`
and `scal Y`.  No non-degeneracy hypothesis on the two denominators is needed: when one of them
vanishes both the corresponding correction term of `linv` and its coefficient in the formula
below vanish. -/
theorem ric_linv (n : ℕ) (a b : ℝ) {Y : Submission.Diff.Alg.Curv4 n}
    (hY : Submission.Diff.Alg.IsAlgCurv Y) (i j : Fin n) :
    Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.linv a b Y) i j
      = Work.Diff.Alg.Pinch.ric Y i j
        - (((n : ℝ) - 2) * b / (1 + ((n : ℝ) - 2) * b)) * Work.Diff.Alg.Pinch.ric0 Y i j
        - (2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a)))
            * Submission.Diff.Alg.scalAlg Y * (if i = j then 1 else 0) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact i.elim0
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos)
  -- Expand `ric (linv a b Y)` along the two correction terms of `linv`.
  have h1 : ric (linv a b Y) i j
      = ric Y i j
        - (b / (1 + ((n : ℝ) - 2) * b)) * (((n : ℝ) - 2) * ric0 Y i j)
        - (((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a)) * scalAlg Y)
            * ((2 * (n : ℝ) - 2) * id2 n i j) := by
    rw [linv, ellinv_ric_sub, ellinv_ric_sub, ellinv_ric_smul, ellinv_ric_smul,
      ellinv_ric_knProd_ric0 hY, ellinv_ric_knProd_id2_id2]
  rw [h1]
  -- Rearrange the two coefficients into the shape of the statement.
  have hb : (b / (1 + ((n : ℝ) - 2) * b)) * (((n : ℝ) - 2) * ric0 Y i j)
      = (((n : ℝ) - 2) * b / (1 + ((n : ℝ) - 2) * b)) * ric0 Y i j := by ring
  have ha : (((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a)) * scalAlg Y)
        * ((2 * (n : ℝ) - 2) * id2 n i j)
      = (2 * ((n : ℝ) - 1) * a / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * a)))
          * scalAlg Y * id2 n i j := by
    by_cases hE : 1 + 2 * ((n : ℝ) - 1) * a = 0
    · rw [hE]; simp
    · field_simp
  rw [hb, ha]
  simp only [id2]

end Work.Diff.Alg.Pinch
