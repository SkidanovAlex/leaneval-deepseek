import Mathlib

/-!
# Summability of the samples of a Schwartz function against a polynomial weight

For a complex-valued Schwartz function `ψ` on `ℝ`, a positive integer `N` and any
`M : ℕ`, the family of sample values

  `n ↦ ‖ψ (n / N)‖ * (1 + |n|) ^ M`,   `n : ℤ`,

is summable.  This is the elementary "the polynomial weight cannot beat the
Schwartz decay" estimate used when the values of a Schwartz function at the
rescaled integer lattice `(1/N) ℤ` are inserted into a Poisson-summation /
aliasing identity.

The mathematical content is:

* Schwartz decay gives `(1 + |x|) ^ (M + 2) * ‖ψ x‖ ≤ D` for a constant `D ≥ 0`
  (`schwartz_pow_mul_norm_bounded`, an instance of
  `SchwartzMap.one_add_le_sup_seminorm_apply`);
* evaluating at `x = n / N` and using `1 + |n|/N ≥ (1 + |n|) / N` turns this
  into `‖ψ (n/N)‖ * (1 + |n|)^M ≤ D * N^(M+2) / (1 + |n|)^2`;
* for `n ≠ 0` this is at most `D * N^(M+2) * |n|^(-2)`, and `|n|^(-2)` is
  summable over `ℤ` (`Real.summable_abs_int_rpow`); the single exceptional index
  `n = 0` is invisible to summability.

## Main result

* `Work.FunctionalEquations.DensityAux.summableIntGaussian`
-/

open Filter
open scoped SchwartzMap

namespace Work.FunctionalEquations.DensityAux

/-- **Schwartz decay.** For every `k : ℕ` there is `D ≥ 0` with
`(1 + |x|)^k * ‖ψ x‖ ≤ D` for all `x : ℝ`. -/
lemma schwartz_pow_mul_norm_bounded (ψ : SchwartzMap ℝ ℂ) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, (1 + |x|) ^ k * ‖ψ x‖ ≤ D := by
  refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ,
    by positivity, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0))
    (k := k) (n := 0) le_rfl le_rfl ψ x
  simpa [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using h

/-- **Pointwise decay at the samples.**  If `(1 + |x|)^(M+2) ‖ψ x‖ ≤ D` for all
`x`, then for every nonzero `n : ℤ`,

`‖ψ (n / N)‖ * (1 + |n|)^M ≤ D * N^(M+2) * |n|^(-2)`.

The hypothesis `1 ≤ N` is what makes `1 + |n|/N ≥ (1 + |n|)/N` true. -/
lemma norm_sample_mul_pow_le (ψ : SchwartzMap ℝ ℂ) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ x : ℝ, (1 + |x|) ^ (M + 2) * ‖ψ x‖ ≤ D) {n : ℤ} (hn : n ≠ 0) :
    ‖ψ ((n : ℝ) / (N : ℝ))‖ * (1 + |(n : ℝ)|) ^ M ≤
      D * (N : ℝ) ^ (M + 2) * |(n : ℝ)| ^ (-2 : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  set a : ℝ := |(n : ℝ)| with ha_def
  have ha : 0 < a := by rw [ha_def]; exact abs_pos.mpr hnR
  -- the decay bound evaluated at the sample point
  have hDn : (1 + a / (N : ℝ)) ^ (M + 2) * ‖ψ ((n : ℝ) / (N : ℝ))‖ ≤ D := by
    have h1 : |(n : ℝ) / (N : ℝ)| = a / (N : ℝ) := by
      rw [abs_div, abs_of_nonneg hNpos.le, ha_def]
    rw [← h1]
    exact hD _
  have hP : 0 < (1 + a / (N : ℝ)) ^ (M + 2) := by positivity
  have hW : ‖ψ ((n : ℝ) / (N : ℝ))‖ ≤ D / (1 + a / (N : ℝ)) ^ (M + 2) := by
    rw [le_div_iff₀ hP]
    nlinarith [hDn]
  -- the comparison `1 + a/N ≥ (1 + a)/N`
  have hcmp : (1 + a) / (N : ℝ) ≤ 1 + a / (N : ℝ) := by
    rw [div_le_iff₀ hNpos]
    have hmul : (1 + a / (N : ℝ)) * (N : ℝ) = (N : ℝ) + a := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hNpos.ne']
    rw [hmul]
    linarith
  have hdiv : (1 + a) ^ (M + 2) / (N : ℝ) ^ (M + 2) ≤ (1 + a / (N : ℝ)) ^ (M + 2) := by
    have hpow : ((1 + a) / (N : ℝ)) ^ (M + 2) ≤ (1 + a / (N : ℝ)) ^ (M + 2) :=
      pow_le_pow_left₀ (by positivity) hcmp _
    rwa [div_pow] at hpow
  have hNnpow : 0 < (N : ℝ) ^ (M + 2) := by positivity
  have hkey : (1 + a) ^ (M + 2) ≤ (1 + a / (N : ℝ)) ^ (M + 2) * (N : ℝ) ^ (M + 2) := by
    have h := hdiv
    rw [div_le_iff₀ hNnpow] at h
    linarith [h]
  have hQpos : 0 < (1 + a) ^ (M + 2) := by positivity
  have hstep : D / (1 + a / (N : ℝ)) ^ (M + 2) ≤ D * (N : ℝ) ^ (M + 2) / (1 + a) ^ (M + 2) := by
    rw [div_le_div_iff₀ hP hQpos]
    have h2 := mul_le_mul_of_nonneg_left hkey hD0
    nlinarith [h2]
  have hW' : ‖ψ ((n : ℝ) / (N : ℝ))‖ ≤ D * (N : ℝ) ^ (M + 2) / (1 + a) ^ (M + 2) :=
    le_trans hW hstep
  have hmul2 : ‖ψ ((n : ℝ) / (N : ℝ))‖ * (1 + a) ^ M ≤
      (D * (N : ℝ) ^ (M + 2) / (1 + a) ^ (M + 2)) * (1 + a) ^ M :=
    mul_le_mul_of_nonneg_right hW' (by positivity)
  have hMQ : (1 + a) ^ M / (1 + a) ^ (M + 2) = 1 / (1 + a) ^ 2 := by
    rw [pow_add]
    field_simp
  have hfrac : (1 + a) ^ M / (1 + a) ^ (M + 2) ≤ 1 / a ^ 2 := by
    rw [hMQ]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [ha])
  have hfin : (D * (N : ℝ) ^ (M + 2) / (1 + a) ^ (M + 2)) * (1 + a) ^ M ≤
      D * (N : ℝ) ^ (M + 2) * (1 / a ^ 2) := by
    rw [show (D * (N : ℝ) ^ (M + 2) / (1 + a) ^ (M + 2)) * (1 + a) ^ M
        = D * (N : ℝ) ^ (M + 2) * ((1 + a) ^ M / (1 + a) ^ (M + 2)) by
      field_simp]
    exact mul_le_mul_of_nonneg_left hfrac (by positivity)
  have hrpow : (1 : ℝ) / a ^ 2 = a ^ (-2 : ℝ) := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, one_div]
  calc ‖ψ ((n : ℝ) / (N : ℝ))‖ * (1 + a) ^ M
      ≤ (D * (N : ℝ) ^ (M + 2) / (1 + a) ^ (M + 2)) * (1 + a) ^ M := hmul2
    _ ≤ D * (N : ℝ) ^ (M + 2) * (1 / a ^ 2) := hfin
    _ = D * (N : ℝ) ^ (M + 2) * a ^ (-2 : ℝ) := by rw [hrpow]

theorem summableIntGaussian (ψ : SchwartzMap ℝ ℂ) (N : ℕ) (hN : 1 ≤ N) (M : ℕ) :
    Summable (fun n : ℤ => ‖ψ ((n : ℝ) / (N : ℝ))‖ * (1 + |(n : ℝ)|) ^ M) := by
  obtain ⟨D, hD0, hD⟩ := schwartz_pow_mul_norm_bounded ψ (M + 2)
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℤ => D * (N : ℝ) ^ (M + 2) * |(n : ℝ)| ^ (-2 : ℝ)) ?_ ?_
  · exact (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)).mul_left _
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : ℤ)).subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Set.mem_singleton_iff]
    by_contra h0
    refine absurd ?_ hn
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_sample_mul_pow_le ψ hN M hD0 hD h0

end Work.FunctionalEquations.DensityAux
