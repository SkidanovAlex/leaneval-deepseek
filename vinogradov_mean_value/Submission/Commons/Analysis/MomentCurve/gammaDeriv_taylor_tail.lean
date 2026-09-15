import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Commons.Analysis.MomentCurve.transversality_det

open scoped BigOperators

namespace Commons.Analysis.MomentCurve

/-- The falling factorial of `n` is bounded by `n!`. -/
private lemma descFactorial_le_factorial (n m : ℕ) : n.descFactorial m ≤ n.factorial := by
  by_cases h : m ≤ n
  · rw [Nat.descFactorial_eq_div h]
    exact Nat.div_le_self _ _
  · rw [not_le] at h
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    exact Nat.zero_le _

/-- Uniform bound on the derivative vectors of the moment curve on the unit disk:
for `|c| ≤ 1` the norm of `gam k c m` is at most `k!`. -/
private lemma gam_norm_le_factorial (k : ℕ) {c : ℝ} (hc : |c| ≤ 1) (m : ℕ) :
    ‖gam k c m‖ ≤ (k.factorial : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
  intro j
  rw [Real.norm_eq_abs, gam_apply, abs_mul]
  have hj : j.val + 1 ≤ k := by have := j.isLt; omega
  have hdesc : (((j.val + 1).descFactorial m : ℕ) : ℝ) ≤ (k.factorial : ℝ) := by
    have h1 : (j.val + 1).descFactorial m ≤ (j.val + 1).factorial :=
      descFactorial_le_factorial _ _
    have h2 : (j.val + 1).factorial ≤ k.factorial := Nat.factorial_le hj
    exact_mod_cast le_trans h1 h2
  have hp : |c ^ (j.val + 1 - m)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg c) hc
  have hd0 : (0 : ℝ) ≤ (((j.val + 1).descFactorial m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
  calc |(((j.val + 1).descFactorial m : ℕ) : ℝ)| * |c ^ (j.val + 1 - m)|
      = (((j.val + 1).descFactorial m : ℕ) : ℝ) * |c ^ (j.val + 1 - m)| := by
        rw [abs_of_nonneg hd0]
    _ ≤ (k.factorial : ℝ) * 1 := mul_le_mul hdesc hp (abs_nonneg _) hk0
    _ = (k.factorial : ℝ) := by ring

theorem gammaDeriv_taylor_tail (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i l : ℕ) (c u : ℝ), i ≤ l → l ≤ k → |c| ≤ 1 → |u| ≤ 1 →
      ‖gam k (c + u) i
          - ∑ j ∈ Finset.Icc i l, (u ^ (j - i) / ((j - i).factorial : ℝ)) • gam k c j‖
        ≤ C * |u| ^ (l + 1 - i) := by
  refine ⟨(k.factorial : ℝ) * ((k : ℝ) + 1) + 1, by positivity, ?_⟩
  intro i l c u hil hlk hc hu
  -- The sum over `Icc i l` reindexed by `e = j - i`, running over `range (l+1-i)`.
  have hS : (∑ j ∈ Finset.Icc i l, (u ^ (j - i) / ((j - i).factorial : ℝ)) • gam k c j)
      = ∑ e ∈ Finset.range (l + 1 - i),
          (u ^ e / (e.factorial : ℝ)) • gam k c (i + e) := by
    rw [show Finset.Icc i l = Finset.Ico i (l + 1) from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun e _ => ?_
    have he : i + e - i = e := by omega
    rw [he]
  -- Taylor expansion of the derivative vector.
  have hgam : gam k (c + u) i
      = ∑ e ∈ Finset.range (k + 1), (u ^ e / (e.factorial : ℝ)) • gam k c (i + e) :=
    gam_add k c u i
  have hsub : Finset.range (l + 1 - i) ⊆ Finset.range (k + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hdiff : gam k (c + u) i
        - ∑ j ∈ Finset.Icc i l, (u ^ (j - i) / ((j - i).factorial : ℝ)) • gam k c j
      = ∑ e ∈ (Finset.range (k + 1)) \ (Finset.range (l + 1 - i)),
          (u ^ e / (e.factorial : ℝ)) • gam k c (i + e) := by
    rw [hS, hgam]
    have key := Finset.sum_sdiff hsub (f := fun e => (u ^ e / (e.factorial : ℝ)) • gam k c (i + e))
    rw [← key]
    abel
  rw [hdiff]
  -- Bound the tail term by term.
  have hnorm : ∀ e : ℕ,
      ‖(u ^ e / (e.factorial : ℝ)) • gam k c (i + e)‖
        = |u| ^ e / (e.factorial : ℝ) * ‖gam k c (i + e)‖ := by
    intro e
    rw [norm_smul]
    congr 1
    simp
  have hterm : ∀ e ∈ (Finset.range (k + 1)) \ (Finset.range (l + 1 - i)),
      ‖(u ^ e / (e.factorial : ℝ)) • gam k c (i + e)‖
        ≤ |u| ^ (l + 1 - i) * (k.factorial : ℝ) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨hek, hem⟩ := he
    rw [Finset.mem_range] at hek hem
    rw [not_lt] at hem
    rw [hnorm e]
    have h1 : |u| ^ e ≤ |u| ^ (l + 1 - i) :=
      pow_le_pow_of_le_one (abs_nonneg u) hu hem
    have h2 : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
    have he1 : (1 : ℝ) ≤ (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
    have h3 : |u| ^ e / (e.factorial : ℝ) ≤ |u| ^ (l + 1 - i) := by
      rw [div_le_iff₀ h2]
      calc |u| ^ e ≤ |u| ^ (l + 1 - i) := h1
        _ = |u| ^ (l + 1 - i) * 1 := by ring
        _ ≤ |u| ^ (l + 1 - i) * (e.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left he1 (pow_nonneg (abs_nonneg u) _)
    exact mul_le_mul h3 (gam_norm_le_factorial k hc (i + e)) (norm_nonneg _)
      (pow_nonneg (abs_nonneg u) _)
  have hcard : ((Finset.range (k + 1)) \ (Finset.range (l + 1 - i))).card ≤ k + 1 := by
    calc ((Finset.range (k + 1)) \ (Finset.range (l + 1 - i))).card
        ≤ (Finset.range (k + 1)).card := Finset.card_le_card Finset.sdiff_subset
      _ = k + 1 := Finset.card_range _
  calc ‖∑ e ∈ (Finset.range (k + 1)) \ (Finset.range (l + 1 - i)),
          (u ^ e / (e.factorial : ℝ)) • gam k c (i + e)‖
      ≤ ∑ e ∈ (Finset.range (k + 1)) \ (Finset.range (l + 1 - i)),
          ‖(u ^ e / (e.factorial : ℝ)) • gam k c (i + e)‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ (Finset.range (k + 1)) \ (Finset.range (l + 1 - i)),
          |u| ^ (l + 1 - i) * (k.factorial : ℝ) := Finset.sum_le_sum hterm
    _ = (((Finset.range (k + 1)) \ (Finset.range (l + 1 - i))).card : ℝ)
          * (|u| ^ (l + 1 - i) * (k.factorial : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k + 1 : ℕ) : ℝ) * (|u| ^ (l + 1 - i) * (k.factorial : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard)
          (mul_nonneg (pow_nonneg (abs_nonneg u) _) (Nat.cast_nonneg _))
    _ = ((k : ℝ) + 1) * (|u| ^ (l + 1 - i) * (k.factorial : ℝ)) := by
        rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by push_cast; ring]
    _ = ((k.factorial : ℝ) * ((k : ℝ) + 1)) * |u| ^ (l + 1 - i) := by ring
    _ ≤ ((k.factorial : ℝ) * ((k : ℝ) + 1) + 1) * |u| ^ (l + 1 - i) := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num))
          (pow_nonneg (abs_nonneg u) _)

end Commons.Analysis.MomentCurve