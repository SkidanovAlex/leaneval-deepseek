import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.ratIvMem` — soundness of the rational interval `ratIv`

`ratIv p q = [⌊p·SC/q⌋, ⌈p·SC/q⌉]` (mantissas at scale `SC = 2^30`) encloses the real number
`p/q`.  This is the basic soundness statement every rational endpoint of the Theorem-C
certificate rests on.
-/

namespace Work.CNum

open Work.ANum

theorem ratIvMem (p : ℤ) {q : ℕ} (hq : 0 < q) :
    (Work.CNum.ratIv p q).Mem ((p : ℝ) / q) := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · -- lower endpoint: `⌊p·SC/q⌋·SC ≤ p/q`
    simp only [ratIv, m2r]
    rw [div_le_div_iff₀ SC_posR hqR]
    have h' : (((Int.ediv (p * SC) (q : ℤ) : ℤ)) : ℝ) * (q : ℝ) ≤ (p : ℝ) * (SC : ℝ) := by
      exact_mod_cast Int.ediv_mul_le (p * SC) hqZ
    simpa using h'
  · -- upper endpoint: `p/q ≤ ⌈p·SC/q⌉/SC`
    simp only [ratIv, m2r]
    rw [div_le_div_iff₀ hqR SC_posR]
    have h2 : (((Int.ediv (-(p * SC)) (q : ℤ) : ℤ)) : ℝ) * (q : ℝ) ≤ -((p : ℝ) * (SC : ℝ)) := by
      have hc : ((Int.ediv (-(p * SC)) (q : ℤ) * (q : ℤ) : ℤ) : ℝ) ≤ ((-(p * SC) : ℤ) : ℝ) := by
        exact_mod_cast Int.ediv_mul_le (-(p * SC)) hqZ
      push_cast at hc
      simpa using hc
    have h4 : ((-(Int.ediv (-(p * SC)) (q : ℤ)) : ℤ) : ℝ) * (q : ℝ)
        = - ((((Int.ediv (-(p * SC)) (q : ℤ) : ℤ)) : ℝ) * (q : ℝ)) := by push_cast; ring
    rw [h4]
    linarith

end Work.CNum
