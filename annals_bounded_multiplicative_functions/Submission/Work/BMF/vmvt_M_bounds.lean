import Mathlib
import Submission.Work.BMF.vmvt_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The standard choice of the modulus `M = max k (⌈Q^{1/k}⌉ + 1)` satisfies `Q ≤ M^k`
and `1 + Q/M ≤ 2 Q^{1-1/k}`. -/
lemma vmvt_M_bounds (k Q : ℕ) (hk : 2 ≤ k) (hQ : 1 ≤ Q) :
    (Q:ℝ) ≤ (((max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊+1)) : ℕ) : ℝ)^k ∧
    1 + (Q:ℝ)/(((max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊+1)) : ℕ) : ℝ) ≤ 2 * (Q:ℝ)^(1-1/(k:ℝ)) := by
  set x : ℝ := (Q:ℝ)^(1/(k:ℝ)) with hxdef
  set m : ℕ := max k (⌈x⌉₊+1) with hmdef
  have hk1 : 1 ≤ k := by omega
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hQnonneg : (0:ℝ) ≤ (Q:ℝ) := le_of_lt hQpos
  have hxnonneg : 0 ≤ x := by rw [hxdef]; exact Real.rpow_nonneg hQnonneg _
  have hxge1 : 1 ≤ x := by
    rw [hxdef]
    exact Real.one_le_rpow (by exact_mod_cast hQ) (by positivity)
  have hxpow : x ^ k = (Q:ℝ) := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (x := (Q:ℝ)) hQnonneg]
    rw [one_div_mul_cancel hk0, Real.rpow_one]
  have hm_ge_x : x ≤ (m:ℝ) := by
    have h1 : (m:ℝ) = max (k:ℝ) ((⌈x⌉₊ : ℝ) + 1) := by
      rw [hmdef, Nat.cast_max]; push_cast; ring
    rw [h1]
    exact le_trans (Nat.le_ceil x)
      (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _))
  have hmpos : (0:ℝ) < (m:ℝ) := by
    have hm0 : 0 < m := by
      rw [hmdef]
      exact lt_of_lt_of_le (by omega : 0 < k) (le_max_left _ _)
    exact_mod_cast hm0
  refine ⟨?_, ?_⟩
  · rw [← hxpow]
    exact pow_le_pow_left₀ hxnonneg hm_ge_x k
  · have hQm : (Q:ℝ)/(m:ℝ) ≤ x^(k-1) := by
      rw [div_le_iff₀ hmpos, ← hxpow]
      have hsplit : x^k = x^(k-1) * x := by
        conv_lhs => rw [← Nat.sub_add_cancel hk1]
        rw [pow_succ]
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hm_ge_x (pow_nonneg hxnonneg _)
    have hone : 1 ≤ x^(k-1) := one_le_pow₀ hxge1
    have hstep : 1 + (Q:ℝ)/(m:ℝ) ≤ 2 * x^(k-1) := by linarith
    have hxexp : x^(k-1) = (Q:ℝ)^(1 - 1/(k:ℝ)) := by
      rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (x := (Q:ℝ)) hQnonneg]
      congr 1
      rw [Nat.cast_sub hk1]
      field_simp
      ring
    rw [hxexp] at hstep
    exact hstep

end Work.BMF
