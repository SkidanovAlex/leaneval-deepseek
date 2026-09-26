import Mathlib

namespace Work.SG.cobstepAux

/-- Core arithmetic step for the space-group counting argument.

Given a positive natural number `n`, integers `A Z C σc Mσc`, that `n ∣ A - Z + C`
and that `σc - Mσc = n * C`, one has
`A/n = Z/n - σc/n² + Mσc/n² + ((A - Z + C)/n)`
where `/` on the integers is exact division (justified by the divisibility
hypothesis) and the other divisions are in `ℝ`. -/
theorem dvd_ediv_real (n : ℕ) (hn : 0 < n) (A Z C σc Mσc : ℤ)
    (h1 : (n : ℤ) ∣ A - Z + C) (h2 : σc - Mσc = (n : ℤ) * C) :
    (A : ℝ) / (n : ℝ) = (Z : ℝ) / (n : ℝ) - (σc : ℝ) / (n : ℝ) ^ 2
      + (Mσc : ℝ) / (n : ℝ) ^ 2 + (((A - Z + C) / (n : ℤ) : ℤ) : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  -- `σc - Mσc = n * C` transported to `ℝ`.
  have hs : (σc : ℝ) - (Mσc : ℝ) = (n : ℝ) * (C : ℝ) := by exact_mod_cast h2
  -- The integer quotient `(A - Z + C) / n` satisfies `q * n = A - Z + C`.
  have hq : (((A - Z + C) / (n : ℤ) : ℤ) : ℝ) * (n : ℝ) = (A : ℝ) - (Z : ℝ) + (C : ℝ) := by
    have h := Int.ediv_mul_cancel h1
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    linarith [h']
  field_simp
  linear_combination (-(n : ℝ)) * hq + hs

end Work.SG.cobstepAux
