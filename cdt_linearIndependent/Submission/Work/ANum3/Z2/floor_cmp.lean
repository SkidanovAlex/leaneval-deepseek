import Mathlib
import Submission.Work.Cert.WLDefs

namespace Work.ANum3.Z2

/-- Floor division is above the quotient minus one: `⌊a/b⌋ > a/b - 1` for `0 < b`.
(A local copy, so that this module depends only on `WLDefs`.) -/
private lemma fdiv_gt' (a b : ℤ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) - 1 < ((Work.Cert.fdiv a b : ℤ) : ℝ) := by
  have h : a < (Int.ediv a b + 1) * b := Int.lt_ediv_add_one_mul_self a hb
  have h2 : (a : ℝ) < (((Int.ediv a b : ℤ) : ℝ) + 1) * (b : ℝ) := by exact_mod_cast h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [Work.Cert.fdiv, sub_lt_iff_lt_add, div_lt_iff₀ hbR]
  exact h2

/-- With the (huge) tolerance `ETOL`, twice the floor of `(|p| + |r| + 2)/q` at least compensates
`2 + (|p| + |r|)/q`. -/
lemma floor_cmp (p r q : ℤ) (hq : 0 < q) :
    2 + ((Work.Cert.iabs p + Work.Cert.iabs r : ℤ) : ℝ) / (q : ℝ)
      ≤ 2 * ((Work.Cert.fdiv (Work.Cert.iabs p + Work.Cert.iabs r + 2) q : ℤ) : ℝ) + 4 + (Work.Cert.ETOL : ℝ) := by
  set n : ℤ := Work.Cert.iabs p + Work.Cert.iabs r with hn
  have hn0 : (0 : ℤ) ≤ n := by
    rw [hn]; exact add_nonneg (Work.Cert.iabs_nonneg p) (Work.Cert.iabs_nonneg r)
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hET : (0 : ℝ) ≤ (Work.Cert.ETOL : ℝ) := by norm_num [Work.Cert.ETOL]
  have hA : (((n + 2 : ℤ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
  have hf : ((n + 2 : ℤ) : ℝ) / (q : ℝ) - 1 < ((Work.Cert.fdiv (n + 2) q : ℤ) : ℝ) :=
    fdiv_gt' (n + 2) q hq
  have hkey : (2 : ℝ) + (n : ℝ) / (q : ℝ)
      ≤ 2 * ((((n + 2 : ℤ) : ℝ)) / (q : ℝ) - 1) + 4 + (Work.Cert.ETOL : ℝ) := by
    rw [hA]
    have hmul : (2 + (n : ℝ) / (q : ℝ)) * (q : ℝ)
        ≤ (2 * (((n : ℝ) + 2) / (q : ℝ) - 1) + 4 + (Work.Cert.ETOL : ℝ)) * (q : ℝ) := by
      have hdiff : (2 * (((n : ℝ) + 2) / (q : ℝ) - 1) + 4 + (Work.Cert.ETOL : ℝ)) * (q : ℝ)
          - (2 + (n : ℝ) / (q : ℝ)) * (q : ℝ)
          = (n : ℝ) + 4 + (Work.Cert.ETOL : ℝ) * (q : ℝ) := by
        field_simp
        ring
      have hpos : (0 : ℝ) ≤ (n : ℝ) + 4 + (Work.Cert.ETOL : ℝ) * (q : ℝ) := by
        have hm0 := mul_nonneg hET (le_of_lt hqR); linarith
      linarith
    exact le_of_mul_le_mul_right hmul hqR
  have hfinal : 2 * ((((n + 2 : ℤ) : ℝ)) / (q : ℝ) - 1) + 4 + (Work.Cert.ETOL : ℝ)
      ≤ 2 * ((Work.Cert.fdiv (n + 2) q : ℤ) : ℝ) + 4 + (Work.Cert.ETOL : ℝ) := by linarith
  linarith

end Work.ANum3.Z2
