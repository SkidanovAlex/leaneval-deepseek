import Mathlib
import Submission.Commons.Analysis.Dyadic.invSq_le_dyadic_layer
import Submission.Commons.Analysis.Asymptotics.geom_finset_le
import Submission.Commons.Analysis.Asymptotics.sum_range_mul_geom_le

/-!
# Uniform dyadic inverse-square zero-sum estimate

`invSq_zeroSum_of_count` converts a ball-count bound
`Σ_{u ∈ B(a,ρ)} m u ≤ c (ρ+1) (log (‖a‖+ρ+2) + q + 2)` (`ρ ≥ 1`) for a nonnegative,
finitely supported `m : ℂ → ℝ` into the inverse-square kernel bound
`Σ_u m u / (1 + ‖s-u‖²) ≤ C (log (2+‖s‖) + q + 2)`, but its constant `C` is stated *after* the
parameter `q`, i.e. it is only a `q`-wise existence statement.  In applications `q` is itself a
quantity varying with the problem (`q = log N` for the completed L-function of a character
`χ mod N`), and one then needs a *single* constant valid for all `q` simultaneously.

This module provides that form, `invSq_zeroSum_of_count_uniform`, with the quantifier order
`∃ C, ∀ q ≥ 0, ∀ m, …`.  The proof is the usual dyadic argument: split around `s` into the
layers `‖s - u‖ ≤ 2^k`, use the per-point bound
`1/(1+d²) ≤ Σ_{k ≤ K} (4/4^k) 1_{d ≤ 2^k}` (`Commons.Analysis.Dyadic.invSq_le_dyadic_layer`),
interchange the two finite sums and apply the counting hypothesis on each ball `B(s, 2^k)`;
the resulting layers are dominated by `8·c·2^{-k}(A + (k+1) log 2)` with `A = log (2+‖s‖) + q + 2`,
which sums to `≤ 32 c A`, and `32 c A ≤ (64 c + 1) A` for `A ≥ 2`.  Since none of the steps
involves `q` except through `A`, the explicit witness `64 c + 1` is independent of `q`, `m` and
`s`.  The elementary pieces of the estimate are exposed as public lemmas
(`log_add_two_pow_le`, `four_div_pow_mul_le`, `geom_layer_sum_bound`, `indicator_closedBall_eq`)
so that other dyadic arguments can reuse them.
-/

open scoped BigOperators

set_option autoImplicit false

namespace Commons.Analysis.Asymptotics

/-- Logarithmic doubling bound for the dyadic layers:
`log (r + 2^k + 2) ≤ log (2 + r) + (k+1)·log 2` for `r ≥ 0`. -/
lemma log_add_two_pow_le (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    Real.log (r + (2:ℝ)^k + 2) ≤ Real.log (2 + r) + ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hpos : 0 < r + (2:ℝ)^k + 2 := by positivity
  have hle : r + (2:ℝ)^k + 2 ≤ (2 + r) * (2:ℝ)^(k+1) := by
    have hpow : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have hr2 : r ≤ r * (2:ℝ)^(k+1) := by
      have h1 : (1:ℝ) ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
      nlinarith
    have h2 : (2:ℝ)^k + 2 ≤ (2:ℝ)^(k+2) := by
      rw [show (2:ℝ)^(k+2) = (2:ℝ)^k * 4 by rw [pow_add]; ring]
      nlinarith
    have hexp : (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) := by
      rw [show k + 2 = (k+1) + 1 by omega, pow_succ]
      ring
    calc r + (2:ℝ)^k + 2 ≤ r * (2:ℝ)^(k+1) + (2:ℝ)^(k+2) := by linarith
      _ = r * (2:ℝ)^(k+1) + 2 * (2:ℝ)^(k+1) := by rw [hexp]
      _ = (2 + r) * (2:ℝ)^(k+1) := by ring
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  simpa using hlog

/-- Layer collapse: `(4/4^k)·(2^k + 1) ≤ 8·(1/2)^k`. -/
lemma four_div_pow_mul_le (k : ℕ) :
    ((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1) ≤ 8 * ((1/2:ℝ)^k) := by
  have hne : ((4:ℝ)^k) ≠ 0 := pow_ne_zero k (by norm_num)
  have h2 : ((2:ℝ)^k) / ((4:ℝ)^k) = ((1/2:ℝ)^k) := by
    rw [div_eq_iff hne, ← mul_pow]
    norm_num
  have h4 : (1:ℝ) / ((4:ℝ)^k) = ((1/4:ℝ)^k) := by rw [one_div_pow]
  have h42 : ((1/4:ℝ)^k) ≤ ((1/2:ℝ)^k) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h3 : ((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1)
      = 4 * (((2:ℝ)^k)/((4:ℝ)^k)) + 4 * (1/((4:ℝ)^k)) := by
    field_simp
  rw [h3, h2, h4]
  have hpk : (0:ℝ) ≤ ((1/2:ℝ)^k) := by positivity
  linarith

/-- The dyadic geometric series of the inverse-square estimate: for `A ≥ 2`, `0 ≤ B ≤ 1` and
every `K`, `∑_{k ≤ K} (1/2)^k (A + (k+1)B) ≤ 4A`. -/
lemma geom_layer_sum_bound (A B : ℝ) (hA : 2 ≤ A) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (K : ℕ) :
    (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k) * (A + ((k+1:ℕ):ℝ) * B)) ≤ 4 * A := by
  have hA0 : 0 ≤ A := by linarith
  have hS1 : (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k)) ≤ 2 := by
    have h := geom_finset_le (r := (1/2:ℝ)) (by norm_num) (by norm_num) (Finset.range (K+1))
    have h2 : (1:ℝ)/(1-(1/2:ℝ)) = 2 := by norm_num
    linarith
  have hS2 : (∑ k ∈ Finset.range (K+1), (k:ℝ) * ((1/2:ℝ)^k)) ≤ 2 := by
    have h := sum_range_mul_geom_le (r := (1/2:ℝ)) (by norm_num) (by norm_num) K
    have h2 : (1/2:ℝ)/(1-(1/2:ℝ))^2 = 2 := by norm_num
    linarith
  have hS3 : (∑ k ∈ Finset.range (K+1), ((k+1:ℕ):ℝ) * ((1/2:ℝ)^k)) ≤ 4 := by
    have hsplit : (∑ k ∈ Finset.range (K+1), ((k+1:ℕ):ℝ) * ((1/2:ℝ)^k))
        = (∑ k ∈ Finset.range (K+1), (k:ℝ) * ((1/2:ℝ)^k))
          + (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    rw [hsplit]
    linarith
  have hsplit2 : (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k) * (A + ((k+1:ℕ):ℝ) * B))
      = A * (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k))
        + B * (∑ k ∈ Finset.range (K+1), ((k+1:ℕ):ℝ) * ((1/2:ℝ)^k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsplit2]
  have h1 : A * (∑ k ∈ Finset.range (K+1), ((1/2:ℝ)^k)) ≤ A * 2 :=
    mul_le_mul_of_nonneg_left hS1 hA0
  have h2 : B * (∑ k ∈ Finset.range (K+1), ((k+1:ℕ):ℝ) * ((1/2:ℝ)^k)) ≤ B * 4 :=
    mul_le_mul_of_nonneg_left hS3 hB0
  have h3 : B * 4 ≤ 2 * A := by nlinarith
  linarith

/-- Indicator of a closed ball rewritten with the distance to the centre, the centre on the
left. -/
lemma indicator_closedBall_eq (s u : ℂ) (ρ : ℝ) (m : ℂ → ℝ) :
    Set.indicator (Metric.closedBall s ρ) m u = if ‖s - u‖ ≤ ρ then m u else 0 := by
  classical
  rw [Set.indicator_apply, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]

/-- **Dyadic inverse-square zero-sum estimate, uniform in `q`.**

If a nonnegative finitely supported `m : ℂ → ℝ` has ball counts bounded by
`c (ρ+1) (log (‖a‖+ρ+2) + q + 2)` for all `ρ ≥ 1`, then
`∑ᶠ u, m u / (1 + ‖s-u‖²) ≤ C (log (2+‖s‖) + q + 2)` where `C` depends only on `c` — not on
`q`, `m` or `s`.  The witness is `64 c + 1`.

This is the form needed when `q` varies with a parameter of the problem (e.g. `q = log N` for
the completed L-function of a character mod `N`): the constant is then absolute.  Compare
`invSq_zeroSum_of_count`, which states the same estimate for a *fixed* `q` and therefore only
yields a `q`-dependent constant. -/
theorem invSq_zeroSum_of_count_uniform {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∀ (m : ℂ → ℝ), (∀ u : ℂ, 0 ≤ m u) →
      Function.HasFiniteSupport m →
      (∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
        (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ) m u)
          ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2)) →
      ∀ s : ℂ, (∑ᶠ u : ℂ, m u * (1 / (1 + ‖s - u‖ ^ 2)))
          ≤ C * (Real.log (2 + ‖s‖) + q + 2) := by
  refine ⟨64 * c + 1, by linarith, ?_⟩
  intro q hq m hnn hfin hcount s
  classical
  set T : Finset ℂ := hfin.toFinset with hT
  have hmemT : ∀ u : ℂ, u ∈ T ↔ m u ≠ 0 := fun u => hfin.mem_toFinset
  set A : ℝ := Real.log (2 + ‖s‖) + q + 2 with hA
  have hA2 : 2 ≤ A := by
    have h1 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
    rw [hA]; linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ u ∈ T, ‖s - u‖ ≤ (2:ℝ)^K := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ u ∈ T, (‖s - u‖ + 1))
      (by norm_num : (1:ℝ) < 2)
    refine ⟨K, fun u hu => ?_⟩
    have hle : ‖s - u‖ + 1 ≤ ∑ v ∈ T, (‖s - v‖ + 1) :=
      Finset.single_le_sum (f := fun v => ‖s - v‖ + 1) (fun v _ => by positivity) hu
    linarith
  have hsupp : Function.support (fun u : ℂ => m u * (1 / (1 + ‖s - u‖ ^ 2))) ⊆ (T : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    exact (hmemT u).mpr (fun h => hu (by rw [h, zero_mul]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hstep : (∑ u ∈ T, m u * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ ∑ u ∈ T, m u * (∑ k ∈ Finset.range (K + 1),
            (if ‖s - u‖ ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0)) := by
    apply Finset.sum_le_sum
    intro u hu
    exact mul_le_mul_of_nonneg_left
      (Commons.Analysis.Dyadic.invSq_le_dyadic_layer ‖s - u‖ (norm_nonneg _) K (hK u hu))
      (hnn u)
  have hswap : (∑ u ∈ T, m u * (∑ k ∈ Finset.range (K + 1),
          (if ‖s - u‖ ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0)))
      = ∑ k ∈ Finset.range (K + 1), (4 / (4:ℝ)^k) *
          ∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro u _
    by_cases hp : ‖s - u‖ ≤ (2:ℝ)^k
    · rw [if_pos hp, if_pos hp]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have hcountk : ∀ k : ℕ, (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
      ≤ c * ((2:ℝ)^k + 1) * (Real.log (‖s‖ + (2:ℝ)^k + 2) + q + 2) := by
    intro k
    have hk1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have h := hcount s ((2:ℝ)^k) hk1
    have hsupp2 : Function.support (Set.indicator (Metric.closedBall s ((2:ℝ)^k)) m)
        ⊆ (T : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      by_cases hmem : u ∈ Metric.closedBall s ((2:ℝ)^k)
      · rw [Set.indicator_of_mem hmem] at hu
        exact (hmemT u).mpr hu
      · rw [Set.indicator_of_notMem hmem] at hu
        exact absurd rfl hu
    rw [finsum_eq_sum_of_support_subset _ hsupp2] at h
    have heq : (∑ u ∈ T, Set.indicator (Metric.closedBall s ((2:ℝ)^k)) m u)
        = ∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0) :=
      Finset.sum_congr rfl (fun u _ => indicator_closedBall_eq s u ((2:ℝ)^k) m)
    rw [← heq]
    exact h
  have hNkb : ∀ k : ℕ, (4 / (4:ℝ)^k) *
        (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
      ≤ c * (((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by
    intro k
    have hN := hcountk k
    have hk := log_add_two_pow_le ‖s‖ (norm_nonneg s) k
    have h2 : Real.log (‖s‖ + (2:ℝ)^k + 2) + q + 2
        ≤ A + ((k+1:ℕ):ℝ) * Real.log 2 := by
      rw [hA]; linarith
    have hc2 : (0:ℝ) ≤ c * ((2:ℝ)^k + 1) := by positivity
    have hb : (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
        ≤ c * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2) :=
      hN.trans (mul_le_mul_of_nonneg_left h2 hc2)
    have hfac : (0:ℝ) ≤ (4:ℝ) / (4:ℝ)^k := by positivity
    have h1 := mul_le_mul_of_nonneg_left hb hfac
    calc (4 / (4:ℝ)^k) * (∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0))
        ≤ (4 / (4:ℝ)^k) * (c * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := h1
      _ = c * (((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by
          ring
  have hlog2_0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2_1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hterm : ∀ k : ℕ, c * (((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1)
        * (A + ((k+1:ℕ):ℝ) * Real.log 2))
      ≤ 8 * c * (((1/2:ℝ)^k) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by
    intro k
    have h1 := four_div_pow_mul_le k
    have hkn : (0:ℝ) ≤ A + ((k+1:ℕ):ℝ) * Real.log 2 := by
      have : (0:ℝ) ≤ ((k+1:ℕ):ℝ) * Real.log 2 := by positivity
      linarith [hA2]
    calc c * (((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1) * (A + ((k+1:ℕ):ℝ) * Real.log 2))
        = c * ((((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1)) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by
          ring
      _ ≤ c * ((8 * ((1/2:ℝ)^k)) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hkn) hc
      _ = 8 * c * (((1/2:ℝ)^k) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by ring
  have hmain : (∑ k ∈ Finset.range (K + 1), c * (((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1)
        * (A + ((k+1:ℕ):ℝ) * Real.log 2))) ≤ 32 * c * A := by
    calc (∑ k ∈ Finset.range (K + 1), c * (((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1)
          * (A + ((k+1:ℕ):ℝ) * Real.log 2)))
        ≤ ∑ k ∈ Finset.range (K + 1),
            8 * c * (((1/2:ℝ)^k) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = 8 * c * (∑ k ∈ Finset.range (K + 1),
            ((1/2:ℝ)^k) * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := by
          rw [Finset.mul_sum]
      _ ≤ 8 * c * (4 * A) := by
          apply mul_le_mul_of_nonneg_left
          · exact geom_layer_sum_bound A (Real.log 2) hA2 hlog2_0 hlog2_1 K
          · positivity
      _ = 32 * c * A := by ring
  calc (∑ u ∈ T, m u * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ ∑ u ∈ T, m u * (∑ k ∈ Finset.range (K + 1),
            (if ‖s - u‖ ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0)) := hstep
    _ = ∑ k ∈ Finset.range (K + 1), (4 / (4:ℝ)^k) *
          ∑ u ∈ T, (if ‖s - u‖ ≤ (2:ℝ)^k then m u else 0) := hswap
    _ ≤ ∑ k ∈ Finset.range (K + 1), c * (((4:ℝ)/(4:ℝ)^k) * ((2:ℝ)^k + 1)
          * (A + ((k+1:ℕ):ℝ) * Real.log 2)) := Finset.sum_le_sum (fun k _ => hNkb k)
    _ ≤ 32 * c * A := hmain
    _ ≤ (64 * c + 1) * A := by nlinarith [hc, hA2]

end Commons.Analysis.Asymptotics
