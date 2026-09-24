import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.periodization_tsum_finsum
import Submission.Work.GM.Affine.periodization_fourier_coeff_alt

/-!
# The periodization identity of GM §9

For `f : ℝ → ℝ` continuous with compact support, `m > 0` and a nonzero integer `m₁`,

`∫ u in (0)..1, (∑'_k f ((m₁ * u + k)/m))^2 = m^2 * ∑'_n ‖Fhat f (n * m)‖^2`.

This is Parseval on the circle for the `1`-periodic periodization
`x ↦ ∑'_k f ((x + k)/m)` of `x ↦ f (x/m)`, whose `n`-th Fourier coefficient is
`m * Fhat f (n * m)`; the parameter `m₁` only enters through the substitution
`x = m₁ u` (`u ↦ m₁ u` preserves the measure on the circle for any nonzero integer `m₁`).

The two `sorry`-free ingredients are delegated:
* `periodization_tsum_finsum` — the periodization is a finite sum on `[0,1]`;
* `periodization_fourier_coeff_alt` — its `n`-th Fourier coefficient.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `1`-periodic periodization `x ↦ ∑'_k f ((x + k)/m)` of `x ↦ f (x/m)`. -/
noncomputable def per (f : ℝ → ℝ) (m : ℝ) (x : ℝ) : ℝ := ∑' k : ℤ, f ((x + (k : ℝ)) / m)

lemma per_periodic (f : ℝ → ℝ) (m : ℝ) : Function.Periodic (per f m) 1 := by
  intro x
  simp only [per]
  have h1 : (∑' k : ℤ, f ((x + 1 + (k : ℝ)) / m))
      = ∑' k : ℤ, f ((x + ((k + 1 : ℤ) : ℝ)) / m) := by
    refine tsum_congr fun k => ?_
    congr 1
    push_cast
    ring
  rw [h1]
  exact Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun j : ℤ => f ((x + (j : ℝ)) / m))

/-- A continuous compactly supported `f` vanishes off some symmetric interval `[-R, R]`. -/
lemma exists_support_bound {f : ℝ → ℝ} (hcs : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : ℝ, R < |y| → f y = 0 := by
  obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max r 0, le_max_right _ _, fun y hy => ?_⟩
  have hyr : r < |y| := lt_of_le_of_lt (le_max_left _ _) hy
  have hmem : y ∉ Metric.closedBall (0 : ℝ) r := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    exact not_le.mpr hyr
  exact Function.notMem_support.mp fun h => hmem (hr (subset_tsupport f h))

/-- On `[0,1]` the periodization `per f m` is a finite sum over the window `[-K, K]`. -/
lemma per_eq_finsum {f : ℝ → ℝ} {m R : ℝ} (hm : 0 < m)
    (hRf : ∀ y : ℝ, R < |y| → f y = 0) {K : ℕ} (hK : m * R + 1 ≤ (K : ℝ)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      per f m x = ∑ j ∈ Finset.range (2 * K + 1), f ((x + ((j : ℤ) - (K : ℤ))) / m) :=
  periodization_tsum_finsum hm hRf hK

/-- The periodization is square integrable on `(0,1]`. -/
lemma per_memLp {f : ℝ → ℝ} (hf : Continuous f) {m R : ℝ} (hm : 0 < m)
    (hRf : ∀ y : ℝ, R < |y| → f y = 0) {K : ℕ} (hK : m * R + 1 ≤ (K : ℝ)) :
    MemLp (fun x => (per f m x : ℂ)) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hfin := per_eq_finsum hm hRf hK
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖((∑ j ∈ Finset.range (2 * K + 1),
        f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ)‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn (by fun_prop)
  have key : MemLp (fun x : ℝ => ((∑ j ∈ Finset.range (2 * K + 1),
      f ((x + ((j : ℤ) - (K : ℤ))) / m) : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MemLp.of_bound (by fun_prop) C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Set.Ioc_subset_Icc_self hx)
  refine (memLp_congr_ae ?_).mpr key
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [hfin x (Set.Ioc_subset_Icc_self hx)]

/-- The `n`-th Fourier coefficient of the periodization is `m * Fhat f (n * m)`. -/
lemma per_fourierCoeff {f : ℝ → ℝ} (hf : Continuous f) {m R : ℝ} (hm : 0 < m)
    (hRf : ∀ y : ℝ, R < |y| → f y = 0) {K : ℕ} (hK : m * R + 1 ≤ (K : ℝ)) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun x => (per f m x : ℂ)) n
      = (m : ℂ) * Fhat f ((n : ℝ) * m) := by
  have hK₂ : m * R ≤ (K : ℝ) := by linarith
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  rw [← periodization_fourier_coeff_alt hf hm hRf hK₂ n]
  refine intervalIntegral.integral_congr fun x hx => ?_
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hx
  rw [smul_eq_mul, fourier_coe_apply, efun]
  congr 1
  · congr 1
    push_cast
    ring
  · rw [per_eq_finsum hm hRf hK x hx']

/-- **Parseval for the periodization**: `∫_0^1 (per f m)^2 = m^2 ∑_n ‖Fhat f (n m)‖^2`. -/
lemma per_integral_sq {f : ℝ → ℝ} (hf : Continuous f) {m R : ℝ} (hm : 0 < m)
    (hRf : ∀ y : ℝ, R < |y| → f y = 0) {K : ℕ} (hK : m * R + 1 ≤ (K : ℝ)) :
    ∫ x in (0 : ℝ)..1, (per f m x) ^ 2 = m ^ 2 * ∑' n : ℤ, ‖Fhat f ((n : ℝ) * m)‖ ^ 2 := by
  have hmem := per_memLp hf hm hRf hK
  have hcoe : ∀ n : ℤ, fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun x => (per f m x : ℂ)) n = (m : ℂ) * Fhat f ((n : ℝ) * m) :=
    fun n => per_fourierCoeff hf hm hRf hK n
  have h1 := tsum_sq_fourierCoeffOn (a := (0 : ℝ)) (b := 1)
    (f := fun x => (per f m x : ℂ)) (by norm_num) hmem
  have h2 : ∀ i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun x => (per f m x : ℂ)) i‖ ^ 2 = m ^ 2 * ‖Fhat f ((i : ℝ) * m)‖ ^ 2 := by
    intro i
    rw [hcoe i, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal,
      ← Complex.normSq_eq_norm_sq]
    ring
  rw [tsum_congr h2, tsum_mul_left] at h1
  rw [h1]
  simp only [sub_zero, inv_one, one_smul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-- `(per f m)^2` is interval integrable over every interval (it is `1`-periodic and
continuous on the period `[0,1]`). -/
lemma per_intervalIntegrable {f : ℝ → ℝ} (hf : Continuous f) {m R : ℝ} (hm : 0 < m)
    (hRf : ∀ y : ℝ, R < |y| → f y = 0) {K : ℕ} (hK : m * R + 1 ≤ (K : ℝ)) :
    ∀ t₁ t₂ : ℝ, IntervalIntegrable (fun u => (per f m u) ^ 2) volume t₁ t₂ := by
  have hfin := per_eq_finsum hm hRf hK
  have hper : Function.Periodic (fun u => (per f m u) ^ 2) 1 := by
    simpa [pow_two, Pi.mul_apply] using (per_periodic f m).mul (per_periodic f m)
  have h01 : IntervalIntegrable (fun u => (per f m u) ^ 2) volume (0 : ℝ) 1 := by
    refine IntervalIntegrable.congr (f := fun x => ((∑ j ∈ Finset.range (2 * K + 1),
      f ((x + ((j : ℤ) - (K : ℤ))) / m)) ^ 2)) ?_
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    show (∑ j ∈ Finset.range (2 * K + 1), f ((x + ((j : ℤ) - (K : ℤ))) / m)) ^ 2
      = (per f m x) ^ 2
    rw [hfin x (Set.Ioc_subset_Icc_self hx)]
  have h01' : IntervalIntegrable (fun u => (per f m u) ^ 2) volume (0 : ℝ) (0 + 1) := by
    simpa using h01
  exact fun t₁ t₂ => hper.intervalIntegrable (t := 0) one_ne_zero h01' t₁ t₂

/-- The substitution `x = m₁ u` with a nonzero integer `m₁` preserves the integral over a
period of a `1`-periodic function. -/
lemma integral_comp_int_periodic {H : ℝ → ℝ} (hH : Function.Periodic H 1)
    (hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable H volume t₁ t₂) {m₁ : ℤ} (hm₁ : m₁ ≠ 0) :
    ∫ u in (0 : ℝ)..1, H ((m₁ : ℝ) * u) = ∫ u in (0 : ℝ)..1, H u := by
  have hc : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁
  rw [intervalIntegral.integral_comp_mul_left H hc]
  have h2 : ∫ x in (0 : ℝ)..(m₁ : ℝ), H x = (m₁ : ℝ) • ∫ x in (0 : ℝ)..1, H x := by
    have h := hH.intervalIntegral_add_zsmul_eq m₁ 0 hint
    simpa [zsmul_eq_mul] using h
  rw [mul_zero, mul_one, h2, inv_smul_smul₀ hc]

theorem periodization_identity {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) {m : ℝ} (hm : 0 < m) (m₁ : ℤ) (hm₁ : m₁ ≠ 0) :
    ∫ u in (0:ℝ)..1, (∑' k : ℤ, f ((m₁ * u + k) / m)) ^ 2 = m ^ 2 * ∑' n : ℤ, ‖Work.GM.Affine.Fhat f ((n : ℝ) * m)‖ ^ 2 := by
  obtain ⟨R, _hR0, hRf⟩ := exists_support_bound hcs
  obtain ⟨K, hK⟩ : ∃ K : ℕ, m * R + 1 ≤ (K : ℝ) := ⟨⌈m * R + 1⌉₊, Nat.le_ceil _⟩
  have hper2 : Function.Periodic (fun u : ℝ => (per f m u) ^ 2) 1 := by
    simpa [pow_two, Pi.mul_apply] using (per_periodic f m).mul (per_periodic f m)
  have hint := per_intervalIntegrable hf hm hRf hK
  have key : ∫ u in (0 : ℝ)..1, (per f m ((m₁ : ℝ) * u)) ^ 2
      = m ^ 2 * ∑' n : ℤ, ‖Fhat f ((n : ℝ) * m)‖ ^ 2 := by
    rw [integral_comp_int_periodic hper2 hint hm₁]
    exact per_integral_sq hf hm hRf hK
  have hfun : (fun u : ℝ => (∑' k : ℤ, f ((m₁ * u + k) / m)) ^ 2)
      = fun u : ℝ => (per f m ((m₁ : ℝ) * u)) ^ 2 := by
    funext u
    simp only [per]
  rw [hfun]
  exact key

end

end Work.GM.Affine
