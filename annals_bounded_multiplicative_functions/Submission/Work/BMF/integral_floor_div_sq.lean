import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory intervalIntegral

/-- `∫_k^{k+1} t⁻² dt = 1/k - 1/(k+1)`, via the antiderivative `t ↦ -t⁻¹`. -/
lemma integral_inv_sq (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in (k : ℝ)..((k : ℝ) + 1), (t ^ 2 : ℝ)⁻¹
      = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  have hderiv : ∀ x ∈ Set.uIcc (k : ℝ) ((k : ℝ) + 1),
      HasDerivAt (fun t : ℝ => -t⁻¹) ((x ^ 2 : ℝ)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1), Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by
      have : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hk) hx.1
      linarith
    convert (hasDerivAt_inv hx0).neg using 1
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2 : ℝ)⁻¹) volume (k : ℝ) ((k : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · exact (continuous_id.pow 2).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1), Set.mem_Icc] at hx
      have : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hk) hx.1
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [one_div]
  ring

/-- On `[k, k+1)` the step function `t ↦ d ⌊t⌋₊ / t²` is a.e. equal to the constant
`d k / t²`; integrating it gives `d k · (1/k - 1/(k+1))`. -/
lemma floor_div_sq_step_val (d : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in (k : ℝ)..((k : ℝ) + 1), d ⌊t⌋₊ / t ^ 2 =
      d k * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
  have hcongr : (∫ t in (k : ℝ)..((k : ℝ) + 1), d ⌊t⌋₊ / t ^ 2)
      = ∫ t in (k : ℝ)..((k : ℝ) + 1), d k / t ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton ((k : ℝ) + 1))
    intro x hx
    simp only [Set.mem_ofPred_eq, not_imp] at hx
    rw [Set.mem_singleton_iff]
    by_contra hxne
    have hxm : x ∈ Set.Ioc (k : ℝ) ((k : ℝ) + 1) := by
      have := hx.1
      rwa [Set.uIoc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at this
    rw [Set.mem_Ioc] at hxm
    have hxIco : x ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1) :=
      ⟨le_of_lt hxm.1, lt_of_le_of_ne hxm.2 hxne⟩
    have hfloor : ⌊x⌋₊ = k := Nat.floor_eq_on_Ico k x hxIco
    exact hx.2 (by rw [hfloor])
  have hsplit : (∫ t in (k : ℝ)..((k : ℝ) + 1), d k / t ^ 2)
      = d k * ∫ t in (k : ℝ)..((k : ℝ) + 1), (t ^ 2 : ℝ)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [div_eq_mul_inv]
  rw [hcongr, hsplit, integral_inv_sq k hk]

/-- The step function `t ↦ d ⌊t⌋₊ / t²` is interval integrable on `[k, k+1]` for `k ≥ 1`. -/
lemma floor_div_sq_step_int (d : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    IntervalIntegrable (fun t : ℝ => d ⌊t⌋₊ / t ^ 2) volume (k : ℝ) ((k : ℝ) + 1) := by
  have hcont : IntervalIntegrable (fun t : ℝ => d k / t ^ 2) volume (k : ℝ) ((k : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuous_const.continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1), Set.mem_Icc] at hx
      have : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hk) hx.1
      positivity
  apply hcont.congr_uIoo
  intro x hx
  rw [Set.uIoo_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1), Set.mem_Ioo] at hx
  have hfloor : ⌊x⌋₊ = k := Nat.floor_eq_on_Ico k x ⟨le_of_lt hx.1, hx.2⟩
  simp only [hfloor]

/-- The interval integral of the step function `t ↦ d ⌊t⌋₊ / t²` over `[1, M]` is the sum of
`d n · (1/n - 1/(n+1))` over `n ∈ [1, M-1]`, since the integrand is constant equal to
`d n / t²` on `[n, n+1)`.

Route: induct on `M` (or split `[1,M]` at each integer point via
`intervalIntegral.integral_add_adjacent_intervals`); on `[M, M+1)` use
`Nat.floor_eq_on_Ico` to rewrite `⌊t⌋₊ = M`, and `integral_deriv_eq_sub` with the antiderivative
`t ↦ -(1/t)` to get `∫_M^{M+1} t⁻² dt = 1/M - 1/(M+1)`. -/
theorem integral_floor_div_sq (d : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∫ t in (1 : ℝ)..(M : ℝ), d ⌊t⌋₊ / t ^ 2 =
      ∑ n ∈ Finset.Icc 1 (M - 1), d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  have key : ∀ M : ℕ, 1 ≤ M →
      IntervalIntegrable (fun t : ℝ => d ⌊t⌋₊ / t ^ 2) volume 1 (M : ℝ) ∧
      (∫ t in (1 : ℝ)..(M : ℝ), d ⌊t⌋₊ / t ^ 2
        = ∑ n ∈ Finset.Icc 1 (M - 1), d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      push_cast
      exact ⟨IntervalIntegrable.refl, by simp⟩
    | succ k hk ih =>
      push_cast
      obtain ⟨ihint, ihval⟩ := ih
      have hkint := floor_div_sq_step_int d k hk
      refine ⟨ihint.trans hkint, ?_⟩
      have hsum : (∑ n ∈ Finset.Icc 1 k, d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
          = (∑ n ∈ Finset.Icc 1 (k - 1), d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
            + d k * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
        conv_lhs => rw [show k = k - 1 + 1 from (Nat.sub_add_cancel hk).symm]
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k - 1 + 1), Nat.sub_add_cancel hk]
      rw [hsum, ← ihval, ← floor_div_sq_step_val d k hk,
        ← intervalIntegral.integral_add_adjacent_intervals ihint hkint]
  exact (key M hM).2

end Work.BMF
