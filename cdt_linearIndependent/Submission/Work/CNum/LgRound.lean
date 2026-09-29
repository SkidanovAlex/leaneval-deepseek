import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.LgRound` — mantissa rounding lemmas for the logarithm certificate

`Work.CNum.Fx` computes fixed-point logarithms through the outward-rounded integer operations
`mulU`/`mulD` (multiplication by `SC` and rounding up/down) and `divU`/`divD` (division by a
natural and rounding up/down).  All of these are `Int.ediv`-based, so their soundness as
*real* rounding operations reduces to `Int.ediv_mul_le`.

The lemmas here say that `mulU`, `divU` and the raw ceiling division `a ↦ -(-a / b)` never
underestimate the corresponding real operation, and the `D`-variants never overestimate it.
-/

namespace Work.CNum

open Work.ANum

/-- `⌊a·b/SC⌋/SC ≤ (a/SC)·(b/SC)`. -/
lemma m2r_mulD_le (a b : ℤ) : m2r (mulD a b) ≤ m2r a * m2r b := by
  have hSC0 : (0:ℝ) < (SC:ℝ) := by norm_num [Work.ANum.SC]
  have hz := Int.ediv_mul_le (a*b) (b := SC) (by norm_num [Work.ANum.SC] : SC ≠ 0)
  have hR : (((Int.ediv (a*b) SC : ℤ)) : ℝ) * (SC:ℝ) ≤ ((a:ℝ) * (b:ℝ)) := by
    have h2 : (((Int.ediv (a*b) SC * SC : ℤ)) : ℝ) ≤ (((a*b) : ℤ) : ℝ) := by exact_mod_cast hz
    push_cast at h2 ⊢; linarith
  rw [mulD, m2r, m2r, m2r]
  push_cast
  rw [div_mul_div_comm, div_le_div_iff₀ hSC0 (by positivity)]
  nlinarith [hR]

/-- `(a/SC)·(b/SC) ≤ ⌈a·b/SC⌉/SC`. -/
lemma m2r_mulU_ge (a b : ℤ) : m2r a * m2r b ≤ m2r (mulU a b) := by
  have hSC0 : (0:ℝ) < (SC:ℝ) := by norm_num [Work.ANum.SC]
  have hz := Int.ediv_mul_le (-(a*b)) (b := SC) (by norm_num [Work.ANum.SC] : SC ≠ 0)
  have hR : (((Int.ediv (-(a*b)) SC : ℤ)) : ℝ) * (SC:ℝ) ≤ -((a:ℝ) * (b:ℝ)) := by
    have h2 : (((Int.ediv (-(a*b)) SC * SC : ℤ)) : ℝ) ≤ (((-(a*b)) : ℤ) : ℝ) := by
      exact_mod_cast hz
    push_cast at h2 ⊢; linarith
  rw [mulU, m2r, m2r, m2r]
  push_cast
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hSC0]
  nlinarith [hR]

/-- `⌊a/k⌋/SC ≤ (a/SC)/k` for `k > 0`. -/
lemma m2r_divD_le (a : ℤ) (k : ℕ) (hk : 0 < k) : m2r (divD a k) ≤ m2r a / (k:ℝ) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hSC0 : (0:ℝ) < (SC:ℝ) := by norm_num [Work.ANum.SC]
  have hz := Int.ediv_mul_le a (b := (k:ℤ)) (by omega)
  have hR : (((Int.ediv a (k:ℤ) : ℤ)) : ℝ) * (k:ℝ) ≤ ((a:ℝ)) := by
    have h2 : (((Int.ediv a (k:ℤ) * (k:ℤ) : ℤ)) : ℝ) ≤ (((a) : ℤ) : ℝ) := by exact_mod_cast hz
    push_cast at h2 ⊢; linarith
  rw [divD, m2r, m2r]
  push_cast
  rw [div_div, div_le_div_iff₀ hSC0 (by positivity)]
  have h := mul_le_mul_of_nonneg_right hR hSC0.le
  nlinarith [h]

/-- `(a/SC)/k ≤ ⌈a/k⌉/SC` for `k > 0`. -/
lemma m2r_divU_ge (a : ℤ) (k : ℕ) (hk : 0 < k) : m2r a / (k:ℝ) ≤ m2r (divU a k) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hSC0 : (0:ℝ) < (SC:ℝ) := by norm_num [Work.ANum.SC]
  have hz := Int.ediv_mul_le (-a) (b := (k:ℤ)) (by omega)
  have hR : (((Int.ediv (-a) (k:ℤ) : ℤ)) : ℝ) * (k:ℝ) ≤ -((a:ℝ)) := by
    have h2 : (((Int.ediv (-a) (k:ℤ) * (k:ℤ) : ℤ)) : ℝ) ≤ (((-a) : ℤ) : ℝ) := by exact_mod_cast hz
    push_cast at h2 ⊢; linarith
  rw [divU, m2r, m2r]
  push_cast
  rw [div_div, div_le_div_iff₀ (by positivity) hSC0]
  have h := mul_le_mul_of_nonneg_right hR hSC0.le
  nlinarith [h]

/-- `X/(D·SC) ≤ ⌈X/D⌉/SC` (ceiling division never underestimates). -/
lemma m2r_ceilDiv_ge (X D : ℤ) (hD : 0 < D) : (X:ℝ)/(D:ℝ)/SC ≤ m2r (-Int.ediv (-X) D) := by
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hSC0 : (0:ℝ) < (SC:ℝ) := by norm_num [Work.ANum.SC]
  have hz := Int.ediv_mul_le (-X) (b := D) (by omega)
  have hR : (((Int.ediv (-X) D : ℤ)) : ℝ) * ((D:ℝ)) ≤ -((X:ℝ)) := by
    have h2 : (((Int.ediv (-X) D * D : ℤ)) : ℝ) ≤ (((-X) : ℤ) : ℝ) := by exact_mod_cast hz
    push_cast at h2 ⊢; linarith
  rw [m2r]
  push_cast
  rw [div_div, div_le_div_iff₀ (by positivity) hSC0]
  have h := mul_le_mul_of_nonneg_right hR hSC0.le
  nlinarith [h]

/-- `(m2r v)^m ≤ m2r (powM true v m)` for `v ≥ 0`. -/
lemma m2r_powM_ge {v : ℤ} (hv : 0 ≤ v) (m : ℕ) : (m2r v)^m ≤ m2r (powM true v m) := by
  have hv0 : (0:ℝ) ≤ m2r v := by
    rw [m2r]
    exact div_nonneg (by exact_mod_cast hv) (by norm_num [Work.ANum.SC])
  induction m with
  | zero => simp [powM, Work.ANum.m2r_SC]
  | succ m ih =>
      have hstep : m2r (powM true v (m+1)) = m2r (mulU (powM true v m) v) := by
        simp only [powM, if_true]
      rw [hstep, pow_succ]
      exact le_trans (mul_le_mul_of_nonneg_right ih hv0) (m2r_mulU_ge _ _)

end Work.CNum
