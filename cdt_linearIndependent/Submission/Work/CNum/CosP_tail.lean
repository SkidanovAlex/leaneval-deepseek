import Mathlib
import Submission.Work.CNum.cosT_bound

namespace Work.CNum

/-- Splitting the `P = 12` cosine partial sum into the `P = 11` one plus the next term. -/
lemma cosP_succ_11 (x : ℝ) :
    cosP x 12 = cosP x 11 + x ^ 24 / ((Nat.factorial 24 : ℝ)) := by
  rw [cosP, cosP, Finset.sum_range_succ]; norm_num

/-- The `P = 12` Lagrange-remainder bound rewritten with the `24!`-denominator splitting. -/
lemma cosP_tail_aux {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 4) :
    x ^ 25 / ((Nat.factorial 25 : ℝ)) ≤ x ^ 24 / ((Nat.factorial 24 : ℝ)) ∧
    x ^ 24 / ((Nat.factorial 24 : ℝ)) + x ^ 25 / ((Nat.factorial 25 : ℝ))
      ≤ 2 * ((Nat.factorial 24 : ℝ))⁻¹ := by
  have hx1 : x ≤ 1 := by
    have hpi4 : Real.pi / 4 ≤ 1 := by have := Real.pi_lt_four; linarith
    linarith
  have hfac : (Nat.factorial 25 : ℝ) = 25 * (Nat.factorial 24 : ℝ) := by
    rw [show 25 = 24 + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hfac]
    have hx25 : x / 25 ≤ 1 := by linarith
    have key : x ^ 25 / (25 * (Nat.factorial 24 : ℝ))
        = (x ^ 24 / (Nat.factorial 24 : ℝ)) * (x / 25) := by
      field_simp
    rw [key]
    calc (x ^ 24 / (Nat.factorial 24 : ℝ)) * (x / 25)
        ≤ (x ^ 24 / (Nat.factorial 24 : ℝ)) * 1 := by
          apply mul_le_mul_of_nonneg_left hx25; positivity
      _ = x ^ 24 / (Nat.factorial 24 : ℝ) := by ring
  · have hx24 : x ^ 24 ≤ 1 := pow_le_one₀ h0 hx1
    have hx25 : x ^ 25 ≤ 1 := pow_le_one₀ h0 hx1
    have h24p : (0:ℝ) < (Nat.factorial 24 : ℝ) := by positivity
    have h25le : (Nat.factorial 24 : ℝ) ≤ (Nat.factorial 25 : ℝ) := by
      rw [hfac]; nlinarith [h24p]
    have e1 : x ^ 24 / (Nat.factorial 24 : ℝ) ≤ 1 / (Nat.factorial 24 : ℝ) :=
      div_le_div_of_nonneg_right hx24 h24p.le
    have e2 : x ^ 25 / (Nat.factorial 25 : ℝ) ≤ 1 / (Nat.factorial 25 : ℝ) :=
      div_le_div_of_nonneg_right hx25 (by positivity)
    have e3 : 1 / (Nat.factorial 25 : ℝ) ≤ 1 / (Nat.factorial 24 : ℝ) :=
      one_div_le_one_div_of_le h24p h25le
    have h2 : 2 * ((Nat.factorial 24 : ℝ))⁻¹
        = 1 / (Nat.factorial 24 : ℝ) + 1 / (Nat.factorial 24 : ℝ) := by ring
    rw [h2]; linarith

theorem CosP_tail {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 4) :
    cosP x 11 ≤ Real.cos x ∧ Real.cos x ≤ cosP x 11 + 2 * ((Nat.factorial 24 : ℝ))⁻¹ := by
  obtain ⟨hA, hB⟩ := cosP_tail_aux h0 h1
  have hsplit := cosP_succ_11 x
  have hb := cos_bound x h0 12
  norm_num at hb
  obtain ⟨ha1, ha2⟩ := abs_le.mp hb
  constructor
  · rw [hsplit] at ha1; linarith
  · rw [hsplit] at ha2; linarith

end Work.CNum
