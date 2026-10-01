import Mathlib
import Submission.Commons.Analysis.Dyadic.invSq_le_dyadic_layer
import Submission.Commons.Analysis.Asymptotics.geom_finset_le

open scoped BigOperators

namespace Work.LinnikAreas

/-- Per-point dyadic layer bound for the inverse-square kernel `1/d²` with `d ≥ 1`:
it is dominated by the weighted dyadic layers `8/4^k` on the events `d ≤ 2^k`, `k ≤ K`,
provided `d ≤ 2^K`. -/
lemma invSq_le_weight_layer {d : ℝ} (hd : 1 ≤ d) (K : ℕ) (hdK : d ≤ (2:ℝ)^K) :
    (1:ℝ)/d^2 ≤ ∑ k ∈ Finset.range (K+1),
      (8/(4:ℝ)^k) * (if d ≤ (2:ℝ)^k then 1 else 0) := by
  have hd0 : (0:ℝ) < d := by linarith
  have h1 : (1:ℝ)/(1+d^2) ≤
      ∑ k ∈ Finset.range (K+1), (if d ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0) :=
    Commons.Analysis.Dyadic.invSq_le_dyadic_layer d (le_of_lt hd0) K hdK
  have h2 : (1:ℝ)/d^2 ≤ 2 * ((1:ℝ)/(1+d^2)) := by
    have hd2 : (0:ℝ) < d^2 := by positivity
    have hh : (1:ℝ)/d^2 ≤ 2/(1+d^2) := by
      rw [div_le_div_iff₀ hd2 (by positivity)]
      nlinarith [hd]
    calc (1:ℝ)/d^2 ≤ 2/(1+d^2) := hh
      _ = 2 * ((1:ℝ)/(1+d^2)) := by ring
  have h3 : 2 * ((1:ℝ)/(1+d^2)) ≤ 2 * (∑ k ∈ Finset.range (K+1),
      (if d ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h4 : 2 * (∑ k ∈ Finset.range (K+1), (if d ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0))
      = ∑ k ∈ Finset.range (K+1), (8/(4:ℝ)^k) * (if d ≤ (2:ℝ)^k then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : d ≤ (2:ℝ)^k
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  linarith [h2, h3, h4.le, h4.ge]

/-- The dyadic geometric series arising from the layer decomposition is bounded by `80 c`. -/
lemma dyadic_series_bound (c : ℝ) (hc : 0 ≤ c) (K : ℕ) :
    ∑ k ∈ Finset.range (K+1),
      ((8:ℝ)/(4:ℝ)^k) * (c * (2:ℝ)^k * (Real.log ((2:ℝ)^k + 2) + 2)) ≤ 80 * c := by
  have hlog : ∀ k : ℕ, Real.log ((2:ℝ)^k + 2) ≤ (k:ℝ) + 2 := by
    intro k
    have hpos : (0:ℝ) < (2:ℝ)^k + 2 := by positivity
    have hpk : (0:ℝ) < (2:ℝ)^k := by positivity
    have hle : (2:ℝ)^k + 2 ≤ (2:ℝ)^(k+2) := by
      have hpow : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by rw [pow_add]; ring
      have h1k : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
      rw [hpow]; linarith
    have h1 := Real.log_le_log hpos hle
    rw [Real.log_pow] at h1
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have hcast : (((k+2 : ℕ)) : ℝ) = (k:ℝ) + 2 := by push_cast; ring
    rw [hcast] at h1
    nlinarith [h1, hlog2, (show (0:ℝ) ≤ (k:ℝ) by positivity)]
  have hterm : ∀ k : ℕ,
      ((8:ℝ)/(4:ℝ)^k) * (c * (2:ℝ)^k * (Real.log ((2:ℝ)^k + 2) + 2))
        ≤ 8 * c * ((1/2:ℝ)^k * ((k:ℝ) + 4)) := by
    intro k
    have hdiv : (2:ℝ)^k / (4:ℝ)^k = (1/2:ℝ)^k := by
      rw [div_eq_iff (pow_ne_zero k (by norm_num : (4:ℝ) ≠ 0)), ← mul_pow]
      norm_num
    have hstep1 : Real.log ((2:ℝ)^k + 2) + 2 ≤ (k:ℝ) + 4 := by linarith [hlog k]
    calc ((8:ℝ)/(4:ℝ)^k) * (c * (2:ℝ)^k * (Real.log ((2:ℝ)^k + 2) + 2))
        = 8 * c * ((2:ℝ)^k/(4:ℝ)^k) * (Real.log ((2:ℝ)^k + 2) + 2) := by
          ring
      _ ≤ 8 * c * ((2:ℝ)^k/(4:ℝ)^k) * ((k:ℝ) + 4) := by
          apply mul_le_mul_of_nonneg_left hstep1
          positivity
      _ = 8 * c * ((1/2:ℝ)^k * ((k:ℝ) + 4)) := by rw [hdiv]; ring
  have hb1 : (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k)) ≤ 2 := by
    have h := Commons.Analysis.Asymptotics.geom_finset_le (r := (1/2:ℝ))
      (by norm_num) (by norm_num) (Finset.range (K+1))
    have h2 : (1:ℝ)/(1-1/2) = 2 := by norm_num
    linarith [h, h2]
  have hb2 : (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k * (k:ℝ))) ≤ 2 := by
    have hch := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ))
      (by norm_num : ‖(1/2:ℝ)‖ < 1)
    have hval : (∑' k : ℕ, (k:ℝ) * (1/2:ℝ)^k) = 2 := by
      have hh := hch.tsum_eq
      rw [show (1/2:ℝ)/(1-(1/2:ℝ))^2 = 2 by norm_num] at hh
      exact hh
    have hsumm : Summable (fun k : ℕ => (k:ℝ) * (1/2:ℝ)^k) := hch.summable
    have h := Summable.sum_le_tsum (Finset.range (K+1))
      (f := fun k : ℕ => (k:ℝ)*(1/2:ℝ)^k) (fun k _ => by positivity) hsumm
    rw [hval] at h
    rw [show (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k * (k:ℝ)))
          = ∑ k ∈ Finset.range (K+1), ((k:ℝ) * (1/2:ℝ)^k) from
        Finset.sum_congr rfl (fun k _ => by ring)]
    exact h
  have hsum : (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k * ((k:ℝ) + 4))) ≤ 10 := by
    have hsplit : (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k * ((k:ℝ) + 4)))
        = (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k * (k:ℝ) + 4 * (1/2:ℝ)^k)) :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith [hb1, hb2]
  calc ∑ k ∈ Finset.range (K+1),
          ((8:ℝ)/(4:ℝ)^k) * (c * (2:ℝ)^k * (Real.log ((2:ℝ)^k + 2) + 2))
      ≤ ∑ k ∈ Finset.range (K+1), 8 * c * ((1/2:ℝ)^k * ((k:ℝ) + 4)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = 8 * c * (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k * ((k:ℝ) + 4))) := by
        rw [Finset.mul_sum]
    _ ≤ 8 * c * 10 := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
    _ = 80 * c := by ring

theorem tail_le_of_ballCount {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℂ → ℝ, (∀ u, 0 ≤ m u) →
      (∀ R : ℝ, 2 ≤ R → ∀ t : Finset ℂ, (∀ u ∈ t, ‖u‖ ≤ R) →
        ∑ u ∈ t, m u ≤ c * R * (Real.log (R + 2) + 2)) →
      ∀ s : Finset ℂ, (∀ u ∈ s, 2 < ‖u‖) → ∑ u ∈ s, m u / ‖u‖ ^ 2 ≤ C := by
  classical
  refine ⟨80 * c + 1, by positivity, ?_⟩
  intro m hmnn hcount s hs
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ u ∈ s, ‖u‖ ≤ (2:ℝ)^K := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ u ∈ s, (‖u‖ + 1))
      (by norm_num : (1:ℝ) < 2)
    refine ⟨K, fun u hu => ?_⟩
    have hle : ‖u‖ + 1 ≤ ∑ v ∈ s, (‖v‖ + 1) :=
      Finset.single_le_sum (f := fun v => ‖v‖ + 1) (fun v _ => by positivity) hu
    linarith
  have hstep : (∑ u ∈ s, m u / ‖u‖ ^ 2)
      ≤ ∑ u ∈ s, m u * (∑ k ∈ Finset.range (K + 1),
            (8/(4:ℝ)^k) * (if ‖u‖ ≤ (2:ℝ)^k then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro u hu
    have hd1 : (1:ℝ) ≤ ‖u‖ := by have := hs u hu; linarith
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ (hmnn u)
    exact invSq_le_weight_layer hd1 K (hK u hu)
  have hswap : (∑ u ∈ s, m u * (∑ k ∈ Finset.range (K + 1),
          (8/(4:ℝ)^k) * (if ‖u‖ ≤ (2:ℝ)^k then 1 else 0)))
      = ∑ k ∈ Finset.range (K + 1), (8/(4:ℝ)^k) *
          ∑ u ∈ s, (if ‖u‖ ≤ (2:ℝ)^k then m u else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hp : ‖u‖ ≤ (2:ℝ)^k
    · rw [if_pos hp, if_pos hp]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have hcountk : ∀ k ∈ Finset.range (K+1),
      (∑ u ∈ s, (if ‖u‖ ≤ (2:ℝ)^k then m u else 0))
        ≤ c * (2:ℝ)^k * (Real.log ((2:ℝ)^k + 2) + 2) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have hempty : s.filter (fun u => ‖u‖ ≤ (2:ℝ)^0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro u hu hle
        have h2 := hs u hu
        simp only [pow_zero] at hle
        linarith
      have hz : (∑ u ∈ s, (if ‖u‖ ≤ (2:ℝ)^0 then m u else 0)) = 0 := by
        rw [← Finset.sum_filter]
        rw [hempty]
        simp
      rw [hz]
      have hnn : (0:ℝ) ≤ c * (2:ℝ)^0 * (Real.log ((2:ℝ)^0 + 2) + 2) := by
        have hlogpos : (0:ℝ) ≤ Real.log ((2:ℝ)^0 + 2) := Real.log_nonneg (by norm_num)
        have h1 : (0:ℝ) ≤ (2:ℝ)^0 := by norm_num
        positivity
      linarith
    · have h2k : (2:ℝ) ≤ (2:ℝ)^k := by
        calc (2:ℝ) = (2:ℝ)^1 := by ring
          _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hpos
      have hmem : ∀ u ∈ s.filter (fun u => ‖u‖ ≤ (2:ℝ)^k), ‖u‖ ≤ (2:ℝ)^k :=
        fun u hu => (Finset.mem_filter.mp hu).2
      have hb := hcount ((2:ℝ)^k) h2k (s.filter (fun u => ‖u‖ ≤ (2:ℝ)^k)) hmem
      rw [Finset.sum_filter] at hb
      exact hb
  calc (∑ u ∈ s, m u / ‖u‖ ^ 2)
      ≤ ∑ u ∈ s, m u * (∑ k ∈ Finset.range (K + 1),
            (8/(4:ℝ)^k) * (if ‖u‖ ≤ (2:ℝ)^k then 1 else 0)) := hstep
    _ = ∑ k ∈ Finset.range (K + 1), (8/(4:ℝ)^k) *
          ∑ u ∈ s, (if ‖u‖ ≤ (2:ℝ)^k then m u else 0) := hswap
    _ ≤ ∑ k ∈ Finset.range (K + 1), (8/(4:ℝ)^k) *
          (c * (2:ℝ)^k * (Real.log ((2:ℝ)^k + 2) + 2)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left (hcountk k hk)
        positivity
    _ ≤ 80 * c := dyadic_series_bound c hc K
    _ ≤ 80 * c + 1 := by linarith

end Work.LinnikAreas
