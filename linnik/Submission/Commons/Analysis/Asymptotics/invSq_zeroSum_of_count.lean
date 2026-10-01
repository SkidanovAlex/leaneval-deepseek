import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Commons.Analysis.Dyadic.invSq_le_dyadic_layer

namespace Commons.Analysis.Asymptotics

open scoped BigOperators

/-- Logarithm split for the dyadic decomposition. -/
private lemma log_add_two_pow_le (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    Real.log (r + (2:ℝ)^k + 2) ≤ Real.log (2 + r) + ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hLpos : 0 < r + (2:ℝ)^k + 2 := by positivity
  have hrr : r ≤ r * (2:ℝ)^(k+1) := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    nlinarith [hr]
  have h2k : (2:ℝ)^k + 2 ≤ (2:ℝ)^(k+2) := by
    have h4 : (2:ℝ)^(k+2) = (2:ℝ)^k * 4 := by
      rw [pow_add]; ring
    have hpk : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    rw [h4]; nlinarith
  have hexp : (2:ℝ)^(k+2) + r * (2:ℝ)^(k+1) = (2 + r) * (2:ℝ)^(k+1) := by
    rw [show (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) by
      rw [show k + 2 = (k+1) + 1 by omega, pow_succ]; ring]
    ring
  have hle : r + (2:ℝ)^k + 2 ≤ (2 + r) * (2:ℝ)^(k+1) := by
    rw [← hexp]; linarith
  have hlog := Real.log_le_log hLpos hle
  have hlog2 : Real.log ((2 + r) * (2:ℝ)^(k+1)) =
      Real.log (2 + r) + ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rwa [hlog2] at hlog

/-- `(4/4^k) * (2^k + 1) = 4 * ((1/2)^k + (1/4)^k)`. -/
private lemma four_div_pow_mul (k : ℕ) :
    ((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1) = 4 * ((1/2:ℝ)^k + (1/4:ℝ)^k) := by
  have hpow2 : (2:ℝ)^k / (4:ℝ)^k = (1/2:ℝ)^k := by
    rw [div_eq_iff (pow_ne_zero k (by norm_num : (4:ℝ) ≠ 0)), ← mul_pow]
    norm_num
  have hpow4 : (1:ℝ) / (4:ℝ)^k = (1/4:ℝ)^k := by rw [one_div_pow]
  calc
    ((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1)
        = 4 * ((2:ℝ)^k / (4:ℝ)^k) + 4 * (1 / (4:ℝ)^k) := by
          field_simp
    _ = 4 * ((1/2:ℝ)^k + (1/4:ℝ)^k) := by rw [hpow2, hpow4]; ring

/-- Elementary bound for the dyadic geometric series. -/
private lemma dyadic_invSq_sum_bound (A l : ℝ) (K : ℕ) (hA : 2 ≤ A) (hl0 : 0 ≤ l) (hl : l ≤ A / 2) :
    (∑ k ∈ Finset.range (K + 1), (4 * ((1 / 2 : ℝ) ^ k + (1 / 4 : ℝ) ^ k)) *
        (A + ((k + 1 : ℕ) : ℝ) * l)) ≤ 64 * A := by
  have h12 : Summable (fun k : ℕ => ((1/2:ℝ)^k)) := summable_geometric_of_abs_lt_one (by norm_num)
  have hb1 : (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k)) ≤ 2 := by
    have h := Summable.sum_le_tsum (Finset.range (K+1)) (f := fun k : ℕ => ((1/2:ℝ)^k))
      (fun i _ => by positivity) h12
    rwa [tsum_geometric_two] at h
  have hch := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1/2:ℝ)) (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have htsum2 : (∑' k : ℕ, ((k+1 : ℕ):ℝ) * (1/2:ℝ)^k) = 4 := by
    have h' := hch.tsum_eq
    rw [show (1:ℝ)/(1-(1/2:ℝ))^(1+1) = 4 by norm_num] at h'
    simpa [Nat.choose_one_right] using h'
  have hsum2 : Summable (fun k : ℕ => ((k+1 : ℕ):ℝ) * (1/2:ℝ)^k) := by
    have := hch.summable; simpa [Nat.choose_one_right] using this
  have hb2 : (∑ k ∈ Finset.range (K+1), ((k+1 : ℕ):ℝ) * (1/2:ℝ)^k) ≤ 4 := by
    have h := Summable.sum_le_tsum (Finset.range (K+1))
      (f := fun k : ℕ => ((k+1 : ℕ):ℝ) * (1/2:ℝ)^k) (fun i _ => by positivity) hsum2
    rwa [htsum2] at h
  have hterm : ∀ k : ℕ, (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (A + ((k+1:ℕ):ℝ)*l)
      ≤ 8*A*(1/2:ℝ)^k + 8*l*(((k+1:ℕ):ℝ)*(1/2:ℝ)^k) := by
    intro k
    have hle : (1/2:ℝ)^k + (1/4:ℝ)^k ≤ 2*(1/2:ℝ)^k := by
      have h42 : (1/4:ℝ)^k ≤ (1/2:ℝ)^k := by
        apply pow_le_pow_left₀ (by norm_num) (by norm_num)
      have h12nn : (0:ℝ) ≤ (1/2:ℝ)^k := by positivity
      linarith
    have hkn : (0:ℝ) ≤ A + ((k+1:ℕ):ℝ)*l := by
      have : 0 ≤ ((k+1:ℕ):ℝ)*l := mul_nonneg (by positivity) hl0
      linarith
    calc
      (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (A + ((k+1:ℕ):ℝ)*l)
          ≤ (4 * (2*(1/2:ℝ)^k)) * (A + ((k+1:ℕ):ℝ)*l) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 4)) hkn
      _ = 8*A*(1/2:ℝ)^k + 8*l*(((k+1:ℕ):ℝ)*(1/2:ℝ)^k) := by ring
  calc
    (∑ k ∈ Finset.range (K+1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (A + ((k+1:ℕ):ℝ)*l))
        ≤ ∑ k ∈ Finset.range (K+1), (8*A*(1/2:ℝ)^k + 8*l*(((k+1:ℕ):ℝ)*(1/2:ℝ)^k)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
    _ = 8*A*(∑ k ∈ Finset.range (K+1), (1/2:ℝ)^k)
          + 8*l*(∑ k ∈ Finset.range (K+1), ((k+1:ℕ):ℝ)*(1/2:ℝ)^k) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
        · rw [Finset.mul_sum]
    _ ≤ 8*A*2 + 8*l*4 := by
        have h1 := mul_le_mul_of_nonneg_left hb1 (by linarith : (0:ℝ) ≤ 8*A)
        have h2 := mul_le_mul_of_nonneg_left hb2 (by linarith : (0:ℝ) ≤ 8*l)
        linarith
    _ ≤ 64*A := by nlinarith [hl, hA]


/-- `u ∈ closedBall s ρ ↔ ‖s - u‖ ≤ ρ`. -/
private lemma mem_closedBall_iff (s u : ℂ) (ρ : ℝ) :
    u ∈ Metric.closedBall s ρ ↔ ‖s - u‖ ≤ ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]

/-- Indicator of a closed ball at `u`, rewritten in terms of `‖s - u‖`. -/
private lemma indicator_closedBall_eq (s u : ℂ) (ρ : ℝ) (m : ℂ → ℝ) :
    Set.indicator (Metric.closedBall s ρ) m u = if ‖s - u‖ ≤ ρ then m u else 0 := by
  classical
  rw [Set.indicator_apply, mem_closedBall_iff]

/-- Dyadic / inverse-square kernel estimate: a nonnegative finitely-supported `m : ℂ → ℝ`
whose ball counts are `≤ c(ρ+1)(log(‖a‖+ρ+2)+q+2)` satisfies
`Σ_u m u/(1+‖s-u‖²) ≤ C(log(2+‖s‖)+q+2)` uniformly in `m`. -/
theorem invSq_zeroSum_of_count {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℂ → ℝ), (∀ u : ℂ, 0 ≤ m u) → Function.HasFiniteSupport m →
      (∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
        (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ) m u)
          ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2)) →
      ∀ s : ℂ, (∑ᶠ u : ℂ, m u * (1 / (1 + ‖s - u‖ ^ 2)))
          ≤ C * (Real.log (2 + ‖s‖) + q + 2) := by
  refine ⟨64 * c + 1, by linarith, ?_⟩
  intro m hnn hfin hcount s
  classical
  set T : Finset ℂ := hfin.toFinset with hT
  have hmemT : ∀ u : ℂ, u ∈ T ↔ m u ≠ 0 := fun u => hfin.mem_toFinset
  set A : ℝ := Real.log (2 + ‖s‖) + q + 2 with hA
  have hA2 : 2 ≤ A := by
    have h1 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
    rw [hA]; linarith
  -- choose a dyadic radius containing the support
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ u ∈ T, ‖s - u‖ ≤ (2:ℝ)^K := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ u ∈ T, (‖s - u‖ + 1)) (by norm_num : (1:ℝ) < 2)
    refine ⟨K, fun u hu => ?_⟩
    have hle : ‖s - u‖ + 1 ≤ ∑ v ∈ T, (‖s - v‖ + 1) :=
      Finset.single_le_sum (f := fun v => ‖s - v‖ + 1) (fun v _ => by positivity) hu
    linarith
  -- reduce the outer finsum to a sum over the support
  have hsupp : Function.support (fun u : ℂ => m u * (1 / (1 + ‖s - u‖ ^ 2))) ⊆ (T : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    exact (hmemT u).mpr (fun h => hu (by rw [h, zero_mul]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  -- per-term dyadic layer bound
  have hstep : (∑ u ∈ T, m u * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ ∑ u ∈ T, m u * (∑ k ∈ Finset.range (K + 1),
            (if ‖s - u‖ ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0)) := by
    apply Finset.sum_le_sum
    intro u hu
    apply mul_le_mul_of_nonneg_left _ (hnn u)
    exact Commons.Analysis.Dyadic.invSq_le_dyadic_layer ‖s - u‖ (norm_nonneg _) K (hK u hu)
  -- interchange the two finite sums
  have hswap : (∑ u ∈ T, m u * (∑ k ∈ Finset.range (K + 1),
          (if ‖s - u‖ ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0)))
      = ∑ k ∈ Finset.range (K + 1), (4 / (4:ℝ)^k) *
          ∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hp : ‖s - u‖ ≤ (2:ℝ)^k
    · rw [if_pos hp, if_pos hp]; ring
    · rw [if_neg hp, if_neg hp]; ring
  -- apply the counting hypothesis on each closed ball
  have hcountk : ∀ k : ℕ, (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
      ≤ c * ((2:ℝ)^k + 1) * (Real.log (‖s‖ + (2:ℝ)^k + 2) + q + 2) := by
    intro k
    have hk1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have h := hcount s ((2:ℝ)^k) hk1
    have hsupp2 : Function.support
        (Set.indicator (Metric.closedBall s ((2:ℝ)^k)) m) ⊆ (T : Set ℂ) := by
      intro u hu
      rw [Function.mem_support, indicator_closedBall_eq] at hu
      by_cases hmem : ‖s - u‖ ≤ (2:ℝ)^k
      · rw [if_pos hmem] at hu; exact (hmemT u).mpr hu
      · rw [if_neg hmem] at hu; exact absurd rfl hu
    rw [finsum_eq_sum_of_support_subset _ hsupp2] at h
    have heq : (∑ u ∈ T, Set.indicator (Metric.closedBall s ((2:ℝ)^k)) m u)
        = ∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      exact indicator_closedBall_eq s u ((2:ℝ)^k) m
    rw [← heq]; exact h
  -- bound each summand of the interchange
  have hNkbounded : ∀ k : ℕ, (4 / (4:ℝ)^k) * (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
      ≤ c * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by
    intro k
    have hN := hcountk k
    have h2 : Real.log (‖s‖ + (2:ℝ)^k + 2) + q + 2 ≤ A + ((k+1:ℕ):ℝ) * Real.log 2 := by
      have hk := log_add_two_pow_le ‖s‖ (norm_nonneg s) k
      rw [hA]; linarith
    have hc2 : (0:ℝ) ≤ c * ((2:ℝ)^k + 1) := mul_nonneg hc (by positivity)
    have hfac : (0:ℝ) ≤ (4:ℝ) / (4:ℝ)^k := by positivity
    have hb : (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
        ≤ c * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2) :=
      (hN.trans (mul_le_mul_of_nonneg_left h2 hc2))
    have h1 := mul_le_mul_of_nonneg_left hb hfac
    calc
      (4 / (4:ℝ)^k) * (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
          ≤ (4 / (4:ℝ)^k) * (c * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := h1
      _ = c * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by
            calc (4 / (4:ℝ)^k) * (c * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2))
                = (c * ((4 / (4:ℝ)^k) * ((2:ℝ)^k + 1))) * (A + ((k+1:ℕ):ℝ) * Real.log 2) := by ring
              _ = (c * (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k))) * (A + ((k+1:ℕ):ℝ) * Real.log 2) := by
                    rw [four_div_pow_mul]
              _ = c * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by ring
  have hlog2A : Real.log 2 ≤ A / 2 := by
    have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  have hmain : (∑ u ∈ T, m u * (1 / (1 + ‖s - u‖ ^ 2))) ≤ (64 * c + 1) * A := by
    calc
      (∑ u ∈ T, m u * (1 / (1 + ‖s - u‖ ^ 2)))
          ≤ ∑ u ∈ T, m u * (∑ k ∈ Finset.range (K + 1),
              (if ‖s - u‖ ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0)) := hstep
      _ = ∑ k ∈ Finset.range (K + 1), (4 / (4:ℝ)^k) *
              ∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0) := hswap
      _ ≤ ∑ k ∈ Finset.range (K + 1), c * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) *
              (A + ((k+1:ℕ):ℝ) * Real.log 2)) := Finset.sum_le_sum (fun k _ => hNkbounded k)
      _ = c * (∑ k ∈ Finset.range (K + 1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) *
              (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by rw [Finset.mul_sum]
      _ ≤ c * (64 * A) := by
            apply mul_le_mul_of_nonneg_left _ hc
            exact dyadic_invSq_sum_bound A (Real.log 2) K hA2 (Real.log_nonneg (by norm_num)) hlog2A
      _ ≤ (64 * c + 1) * A := by
            have hA0 : (0:ℝ) ≤ A := by linarith
            nlinarith [hA0]
  exact hmain

end Commons.Analysis.Asymptotics