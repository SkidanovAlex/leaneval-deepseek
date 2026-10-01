import Mathlib
import Submission.Work.LinnikAreas.TFDefs

namespace Work.LinnikAreas

lemma aSeq_of_one_le (r : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    aSeq r k = (1 + r) * r ^ (k - 1) := by
  cases k with
  | zero => omega
  | succ j => simp [aSeq_succ]

/-- For `0 ≤ r < 1` and any integer shifts `a b`, the sequence
`n ↦ aZ r (n+a) * aZ r (n+b)` (n : ℕ) is summable: for large `n` it equals
`(1+r)^2 * r^{a+b-2} * (r^2)^n`, an eventually geometric sequence with ratio `r^2 < 1`.
(Shifting the index by a large `N` turns `r^{a+b-2}` into a genuine nonnegative natural
power, so `pow_add` applies and no `zpow` is needed.) -/
theorem aZ_mul_summable_ray (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℤ) :
    Summable (fun n : ℕ => aZ r ((n : ℤ) + a) * aZ r ((n : ℤ) + b)) := by
  set N : ℕ := (max (max (1 - a) (1 - b)) 1).toNat with hN
  have hNcast : (N : ℤ) = max (max (1 - a) (1 - b)) 1 := by
    rw [hN]
    exact Int.toNat_of_nonneg (le_trans (by norm_num : (0:ℤ) ≤ 1) (le_max_right _ _))
  have hNa : (1 : ℤ) ≤ (N : ℤ) + a := by
    rw [hNcast]
    have : (1 : ℤ) - a ≤ max (max (1 - a) (1 - b)) 1 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hNb : (1 : ℤ) ≤ (N : ℤ) + b := by
    rw [hNcast]
    have : (1 : ℤ) - b ≤ max (max (1 - a) (1 - b)) 1 :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  obtain ⟨A, hA1, hAc⟩ : ∃ A : ℕ, 1 ≤ A ∧ (A : ℤ) = (N : ℤ) + a := by
    refine ⟨((N : ℤ) + a).toNat, ?_, Int.toNat_of_nonneg (by linarith)⟩
    have : (1 : ℤ) ≤ (((N : ℤ) + a).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]; exact hNa
    exact_mod_cast this
  obtain ⟨B, hB1, hBc⟩ : ∃ B : ℕ, 1 ≤ B ∧ (B : ℤ) = (N : ℤ) + b := by
    refine ⟨((N : ℤ) + b).toNat, ?_, Int.toNat_of_nonneg (by linarith)⟩
    have : (1 : ℤ) ≤ (((N : ℤ) + b).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]; exact hNb
    exact_mod_cast this
  have key : ∀ n : ℕ,
      aZ r (((n + N : ℕ) : ℤ) + a) * aZ r (((n + N : ℕ) : ℤ) + b)
        = ((1 + r) ^ 2 * r ^ (A - 1) * r ^ (B - 1)) * (r ^ 2) ^ n := by
    intro n
    have h1 : ((n + N : ℕ) : ℤ) + a = ((n + A : ℕ) : ℤ) := by push_cast; omega
    have h2 : ((n + N : ℕ) : ℤ) + b = ((n + B : ℕ) : ℤ) := by push_cast; omega
    rw [h1, h2, aZ_ofNat, aZ_ofNat,
      aSeq_of_one_le r (by omega), aSeq_of_one_le r (by omega)]
    rw [show n + A - 1 = n + (A - 1) by omega,
      show n + B - 1 = n + (B - 1) by omega, pow_add, pow_add]
    have hpow : (r ^ 2) ^ n = r ^ n * r ^ n := by
      rw [show r ^ 2 = r * r by ring, mul_pow]
    rw [hpow]
    ring
  have hgeom : Summable (fun n : ℕ => (r ^ 2) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hsum : Summable (fun n : ℕ => ((1 + r) ^ 2 * r ^ (A - 1) * r ^ (B - 1)) * (r ^ 2) ^ n) :=
    hgeom.mul_left _
  have htail : Summable (fun n : ℕ =>
      aZ r (((n + N : ℕ) : ℤ) + a) * aZ r (((n + N : ℕ) : ℤ) + b)) :=
    hsum.congr (fun n => (key n).symm)
  exact (summable_nat_add_iff N).mp htail

end Work.LinnikAreas
