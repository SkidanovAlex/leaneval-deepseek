import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_Ico_log_div
import Submission.Work.LinnikAreas.Density4.geom_exp_Icc_bound
import Submission.Work.LinnikAreas.Density4.inv_one_sub_exp_neg_one_div_le
import Submission.Work.LinnikAreas.Density4.exp_div_le_log_div

namespace Work.LinnikAreas.Density4

/-- For `X ≥ 1` and `K` with `X ≤ K + 1`, the rescaled exponential tail is at most `1`. -/
lemma tail_aux (X : ℝ) (hX : 1 ≤ X) (K : ℕ) (hK : X ≤ (K:ℝ) + 1) :
    Real.exp (-(((K:ℝ)+1)/X)) / (1 - Real.exp (-(1/X))) / X ≤ 1 := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hexp_le : Real.exp (-(((K:ℝ)+1)/X)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    have h1 : (1:ℝ) ≤ ((K:ℝ)+1)/X := by rw [le_div_iff₀ hXpos]; linarith
    linarith
  have hden : 0 < 1 - Real.exp (-(1/X)) := by
    have hlt : Real.exp (-(1/X)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : (0:ℝ) < 1/X := one_div_pos.mpr hXpos
      linarith
    linarith
  have hinv : 1 / (1 - Real.exp (-(1/X))) ≤ X + 1 := inv_one_sub_exp_neg_one_div_le X hX
  rw [div_le_iff₀ hXpos, one_mul]
  calc Real.exp (-(((K:ℝ)+1)/X)) / (1 - Real.exp (-(1/X)))
      = Real.exp (-(((K:ℝ)+1)/X)) * (1 / (1 - Real.exp (-(1/X)))) := by ring
    _ ≤ Real.exp (-1) * (X + 1) := by
        exact mul_le_mul hexp_le hinv (le_of_lt (one_div_pos.mpr hden))
          (le_of_lt (Real.exp_pos (-1)))
    _ ≤ X := by
        rw [Real.exp_neg]
        rw [inv_mul_le_iff₀ (Real.exp_pos 1)]
        have he : (2:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
        have h2 : X + 1 ≤ 2 * X := by linarith
        have h3 : (2:ℝ) * X ≤ Real.exp 1 * X := mul_le_mul_of_nonneg_right he (le_of_lt hXpos)
        linarith

/-- The rescaled geometric tail `Σ_{K ≤ n ≤ M} e^{-(n+1)/X}/X` is at most `1`. -/
lemma geom_tail_le_one (X : ℝ) (hX : 1 ≤ X) {K : ℕ} (hK : X ≤ (K:ℝ) + 1) (M : ℕ) :
    ∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ)+1)/X)) / X ≤ 1 := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  calc ∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ)+1)/X)) / X
      = (∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ)+1)/X))) / X := (Finset.sum_div _ _ _).symm
    _ ≤ (Real.exp (-(((K:ℝ)+1)/X)) / (1 - Real.exp (-(1/X)))) / X :=
        div_le_div_of_nonneg_right (geom_exp_Icc_bound X hXpos K M) (le_of_lt hXpos)
    _ ≤ 1 := tail_aux X hX K hK

/-- The sum of `e^{-(n+1)/X}/(n+1)` over `a ≤ n ≤ M` is at most `log (X/a) + 1`,
when `1 ≤ a ≤ X`. -/
lemma sum_le_log {X : ℝ} (hX : 1 ≤ X) {a : ℕ} (ha : 1 ≤ a) (haX : (a:ℝ) ≤ X) (M : ℕ) :
    ∑ n ∈ Finset.Icc a M, Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1) ≤ Real.log (X / (a:ℝ)) + 1 := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  set K := Nat.floor X with hKdef
  have haK : a ≤ K := Nat.le_floor haX
  have hKX : (K:ℝ) ≤ X := Nat.floor_le (le_of_lt hXpos)
  have hKle : X ≤ (K:ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one X)
  have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hsum_split : ∑ n ∈ Finset.Icc a M, Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
      = ∑ n ∈ (Finset.Icc a M).filter (fun n => n < K), Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
        + ∑ n ∈ (Finset.Icc a M).filter (fun n => ¬ n < K), Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc a M) (fun n => n < K) _).symm
  have h1 : ∑ n ∈ (Finset.Icc a M).filter (fun n => n < K), Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
      ≤ ∑ n ∈ Finset.Ico a K, Real.log (((n:ℝ)+1)/(n:ℝ)) := by
    calc ∑ n ∈ (Finset.Icc a M).filter (fun n => n < K), Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
        ≤ ∑ n ∈ (Finset.Icc a M).filter (fun n => n < K), Real.log (((n:ℝ)+1)/(n:ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          exact exp_div_le_log_div n (le_trans ha hn.1.1) X hXpos
      _ ≤ ∑ n ∈ Finset.Ico a K, Real.log (((n:ℝ)+1)/(n:ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [Finset.mem_filter, Finset.mem_Icc] at hn
            rw [Finset.mem_Ico]
            exact ⟨hn.1.1, hn.2⟩
          · intro n hn _
            rw [Finset.mem_Ico] at hn
            apply Real.log_nonneg
            have hn1 : 1 ≤ n := le_trans ha hn.1
            have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
            rw [one_le_div hpos]; linarith
  have h2 : ∑ n ∈ (Finset.Icc a M).filter (fun n => ¬ n < K), Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
      ≤ ∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ)+1)/X)) / X := by
    calc ∑ n ∈ (Finset.Icc a M).filter (fun n => ¬ n < K), Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
        ≤ ∑ n ∈ (Finset.Icc a M).filter (fun n => ¬ n < K), Real.exp (-(((n:ℝ)+1)/X)) / X := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          have hnK : (K:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_of_not_gt hn.2)
          have hXn : X ≤ (n:ℝ)+1 := by have := Nat.lt_floor_add_one X; linarith
          exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hXpos hXn
      _ ≤ ∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ)+1)/X)) / X := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [Finset.mem_filter, Finset.mem_Icc] at hn
            rw [Finset.mem_Icc]
            exact ⟨le_of_not_gt hn.2, hn.1.2⟩
          · intro n _ _
            positivity
  have hlog_le : ∑ n ∈ Finset.Ico a K, Real.log (((n:ℝ)+1)/(n:ℝ)) ≤ Real.log (X / (a:ℝ)) := by
    rw [sum_Ico_log_div a K ha haK]
    apply Real.log_le_log
    · have hKpos : (0:ℝ) < (K:ℝ) := by
        have : (1:ℕ) ≤ K := le_trans ha haK
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
      positivity
    · apply div_le_div_of_nonneg_right hKX (le_of_lt hapos)
  have htail : ∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ)+1)/X)) / X ≤ 1 :=
    geom_tail_le_one X hX hKle M
  calc ∑ n ∈ Finset.Icc a M, Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
      = _ := hsum_split
    _ ≤ (∑ n ∈ Finset.Ico a K, Real.log (((n:ℝ)+1)/(n:ℝ)))
          + (∑ n ∈ Finset.Icc K M, Real.exp (-(((n:ℝ)+1)/X)) / X) := add_le_add h1 h2
    _ ≤ Real.log (X / (a:ℝ)) + 1 := add_le_add hlog_le htail

/-- The sum of `e^{-(n+1)/X}/(n+1)` over `a ≤ n ≤ M` is at most `1`, when `1 ≤ X ≤ a`. -/
lemma sum_le_one {X : ℝ} (hX : 1 ≤ X) {a : ℕ} (_ha : 1 ≤ a) (haX : X ≤ (a:ℝ)) (M : ℕ) :
    ∑ n ∈ Finset.Icc a M, Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1) ≤ 1 := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have haK : X ≤ (a:ℝ) + 1 := by linarith
  calc ∑ n ∈ Finset.Icc a M, Real.exp (-(((n:ℝ)+1)/X)) / ((n:ℝ)+1)
      ≤ ∑ n ∈ Finset.Icc a M, Real.exp (-(((n:ℝ)+1)/X)) / X := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Icc] at hn
        have : X ≤ (n:ℝ) := le_trans haX (by exact_mod_cast hn.1)
        exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hXpos (by linarith)
    _ ≤ 1 := geom_tail_le_one X hX haK M

/-- Elementary tail bound: for `1 ≤ V ≤ X`, `Σ_{⌊V⌋<n≤M} e^{-(n+1)/X}/(n+1) ≤ log(X/V) + 2`. -/
theorem sum_exp_div_le {V X : ℝ} (hV : 1 ≤ V) (hVX : V ≤ X) (M : ℕ) :
    ∑ n ∈ Finset.Icc (Nat.floor V + 1) M, Real.exp (-(((n:ℝ) + 1))/X) / ((n:ℝ) + 1)
      ≤ Real.log (X/V) + 2 := by
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hXpos : 0 < X := lt_of_lt_of_le hVpos hVX
  have hX1 : 1 ≤ X := le_trans hV hVX
  set N := Nat.floor V + 1 with hNdef
  have ha1 : 1 ≤ N := by rw [hNdef]; omega
  have hlogV : 0 ≤ Real.log (X/V) := by
    apply Real.log_nonneg
    rw [one_le_div hVpos]; exact hVX
  simp only [neg_div]
  by_cases hM : M < N
  · have hempty : Finset.Icc N M = ∅ := Finset.Icc_eq_empty (not_le.mpr hM)
    rw [hempty]; simp only [Finset.sum_empty]; linarith
  · have hNV : V < (N:ℝ) := by
      rw [hNdef]; push_cast; exact Nat.lt_floor_add_one V
    by_cases hNX : (N:ℝ) ≤ X
    · have hbound := sum_le_log hX1 ha1 hNX M
      have hle : Real.log (X / (N:ℝ)) ≤ Real.log (X / V) := by
        apply Real.log_le_log
        · positivity
        · apply div_le_div_of_nonneg_left (le_of_lt hXpos) hVpos
          linarith
      linarith
    · have hXN : X ≤ (N:ℝ) := le_of_lt (not_le.mp hNX)
      have hbound := sum_le_one hX1 ha1 hXN M
      linarith

end Work.LinnikAreas.Density4
