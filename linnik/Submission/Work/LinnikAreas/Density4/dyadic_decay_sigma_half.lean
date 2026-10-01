import Mathlib
import Submission.Work.LinnikAreas.Density4.block_sum_bound
import Submission.Work.LinnikAreas.Density4.weight_geom_sum_bound
import Submission.Work.LinnikAreas.Density4.ioc_dyadic_decomposition
import Submission.Work.LinnikAreas.Density4.dyadicBlock_facts

namespace Work.LinnikAreas.Density4

/-- Bookkeeping: the `σ_{-1/2}`-weighted sum with a log-power saving is `O(1)` uniformly in `V`. -/
theorem dyadic_decay_sigma_half : ∃ C : ℝ, 0 < C ∧ ∀ (V : ℕ) (A : ℝ), 2 ≤ A →
    (∑ δ ∈ Finset.Icc 1 V, ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
        (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
        (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-A)) ≤ C := by
  refine ⟨72, by norm_num, ?_⟩
  intro V A hA
  rcases Nat.eq_zero_or_pos V with hV | hV
  · subst hV; simp
  obtain ⟨hc0, hcM0, hmono0, hvn⟩ := dyadicBlock_facts V
  have hdecomp := ioc_dyadic_decomposition (fun m : ℕ => Nat.floor ((V : ℝ) / (2 : ℝ) ^ m))
      (V + 1) hcM0 hmono0
      (fun δ => ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-A))
  rw [hc0] at hdecomp
  rw [hdecomp]
  have hinner : ∀ m : ℕ,
      (∑ δ ∈ Finset.Ioc (Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)))
          (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)),
        ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-A)) ≤
      (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) * 6 := by
    intro m
    have hxpos : 0 < Real.log (2 + (2 : ℝ) ^ m) := by
      apply Real.log_pos
      have h2m : (0:ℝ) ≤ (2:ℝ)^m := by positivity
      linarith
    have hblkapp : (∑ δ ∈ Finset.Ioc (Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)))
          (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)),
        ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ 6 := by
      have h2X : (2:ℝ) * ((V : ℝ) / (2 : ℝ) ^ (m + 1)) = (V : ℝ) / (2 : ℝ) ^ m := by
        rw [pow_succ]; field_simp
      have h := block_sum_bound ((V : ℝ) / (2 : ℝ) ^ (m + 1)) (by positivity)
      rwa [h2X] at h
    have hpt : ∀ δ ∈ Finset.Ioc (Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)))
          (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)),
        ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-A) ≤
        (((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) *
          (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) := by
      intro δ hδ
      obtain ⟨hlt, hle⟩ := Finset.mem_Ioc.mp hδ
      have hδge1 : 1 ≤ δ := by omega
      have hVδ : (2:ℝ)^m ≤ (V : ℝ) / (δ : ℝ) := hvn m δ hδge1 hle
      have hlog : Real.log (2 + (2:ℝ)^m) ≤ Real.log (2 + (V:ℝ)/(δ:ℝ)) := by
        apply Real.log_le_log
        · positivity
        · linarith
      have hwle : (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-A) ≤ (Real.log (2 + (2:ℝ)^m)) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos hxpos hlog (by linarith)
      have hGnn : 0 ≤ ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) := by
        apply mul_nonneg
        · apply div_nonneg (by positivity)
          exact Nat.cast_nonneg δ
        · apply Finset.sum_nonneg
          intro d hd
          positivity
      exact mul_le_mul_of_nonneg_left hwle hGnn
    calc (∑ δ ∈ Finset.Ioc (Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)))
            (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)),
          ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
            (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
            (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-A))
        ≤ ∑ δ ∈ Finset.Ioc (Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)))
            (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)),
          (((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
            (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) *
            (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) := Finset.sum_le_sum hpt
      _ = (∑ δ ∈ Finset.Ioc (Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)))
            (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)),
          ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
            (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) *
            (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) := by rw [Finset.sum_mul]
      _ ≤ 6 * (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) :=
            mul_le_mul_of_nonneg_right hblkapp (Real.rpow_pos_of_pos hxpos _).le
      _ = (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) * 6 := by ring
  calc (∑ m ∈ Finset.range (V + 1), ∑ δ ∈ Finset.Ioc (Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)))
            (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)),
          ((ArithmeticFunction.moebius δ : ℝ)^2) / (δ : ℝ) *
            (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
            (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-A))
      ≤ ∑ m ∈ Finset.range (V + 1), (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) * 6 :=
        Finset.sum_le_sum (fun m _ => hinner m)
    _ = (∑ m ∈ Finset.range (V + 1), (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A)) * 6 := by rw [Finset.sum_mul]
    _ ≤ 12 * 6 := mul_le_mul_of_nonneg_right (weight_geom_sum_bound A hA (V + 1)) (by norm_num)
    _ = 72 := by norm_num

end Work.LinnikAreas.Density4
