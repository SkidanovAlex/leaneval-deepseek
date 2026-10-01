import Mathlib
import Submission.Work.LinnikAreas.TFDefs

/-!
# Summability of the shifted autocorrelation of `aSeq`

The sequence `aSeq r` (`aSeq r 0 = 1`, `aSeq r (n+1) = (1+r) r^n`) decays
geometrically with ratio `r`; hence the shifted product
`n ↦ aSeq r n * aSeq r (n+c)` decays geometrically with ratio `r ^ 2`, and is
summable for `0 ≤ r < 1`.

The key point is the exact identity (valid for every real `r`)

  `aSeq r (m+1) * aSeq r ((m+1)+c) = ((1+r)^2 * r^c) * (r^2)^m`,

after which summability is that of a geometric series of ratio `r^2`.
-/

namespace Work.LinnikAreas

/-- Exact form of the shifted product of two `aSeq` values, landing on a pure
geometric progression of ratio `r ^ 2`. -/
lemma aSeq_mul_aSeq_succ_succ (r : ℝ) (c m : ℕ) :
    aSeq r (m + 1) * aSeq r ((m + 1) + c) = ((1 + r) ^ 2 * r ^ c) * (r ^ 2) ^ m := by
  have h : (m + 1) + c = (m + c) + 1 := by omega
  rw [h, aSeq_succ, aSeq_succ]
  have hpow : r ^ m * r ^ (m + c) = r ^ (2 * m) * r ^ c := by
    rw [← pow_add, ← pow_add, show m + (m + c) = 2 * m + c by omega]
  have key : (1 + r) * r ^ m * ((1 + r) * r ^ (m + c))
      = (1 + r) ^ 2 * (r ^ m * r ^ (m + c)) := by
    ring
  rw [key, hpow, pow_mul]
  ring

theorem summable_aSeq_mul_shift (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (c : ℕ) :
    Summable (fun n : ℕ => aSeq r n * aSeq r (n + c)) := by
  have hsq : ‖(r ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg r)]
    nlinarith
  have hgeom : Summable (fun m : ℕ => ((1 + r) ^ 2 * r ^ c) * (r ^ 2) ^ m) :=
    (summable_geometric_of_norm_lt_one hsq).mul_left _
  have heq : (fun m : ℕ => aSeq r (m + 1) * aSeq r ((m + 1) + c))
      = fun m : ℕ => ((1 + r) ^ 2 * r ^ c) * (r ^ 2) ^ m := by
    funext m
    exact aSeq_mul_aSeq_succ_succ r c m
  exact (summable_nat_add_iff 1).mp (heq ▸ hgeom)

end Work.LinnikAreas
