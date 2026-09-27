import Mathlib
import Submission.Work.EKLC6Core.ae_uncrossed_cellsys

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Work.EKLC6Route

/-- **Thin-margin core lemma.**  Suppose `T` preserves the probability measure `μ`, the family
`B ·` is *linearly thin* (`μ (B ε) ≤ c ε` for every `ε > 0`), and `f` is caught by `B` below the
level `r` (`f z ≤ ε < r → z ∈ B ε`).  Then `μ`-a.e. `x` has a positive geometric lower bound
`δ' ρⁿ ≤ f (Tⁿ x)` along its forward orbit.

This is the abstract Borel–Cantelli / first-Borel–Cantelli argument: for each level `m` the set of
points whose orbit dips below `r (1/2)^{m+1} ρⁿ` is contained in `⋃ₙ (Tⁿ)⁻¹ B (r (1/2)^{m+1} ρⁿ)`,
whose `μ`-measure is at most the geometric sum `c · r (1/2)^{m+1} / (1-ρ) = C (1/2)^m`; as `m → ∞`
this tends to `0`.  No measurability of `f` or of the sets `B ε` is required. -/
theorem thin_margin_core {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {T : α → α}
    (hmp : MeasureTheory.MeasurePreserving T μ μ)
    {f : α → ℝ} {B : ℝ → Set α} {c rho r : ℝ}
    (hc : 0 ≤ c) (hrho0 : 0 < rho) (hrho1 : rho < 1) (hr : 0 < r)
    (hthin : ∀ ε : ℝ, 0 < ε → μ (B ε) ≤ ENNReal.ofReal (c * ε))
    (hBsmall : ∀ (z : α) (ε : ℝ), f z ≤ ε → ε < r → z ∈ B ε) :
    ∀ᵐ x ∂μ, ∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ, δ' * rho ^ n ≤ f (T^[n] x) := by
  classical
  -- The preimage/geometric-sum bound: for every scale `a > 0`,
  -- `μ (⋃ₙ (Tⁿ)⁻¹ B (a ρⁿ)) ≤ c a / (1 - ρ)`.
  have hpre : ∀ a : ℝ, 0 < a → μ (⋃ n : ℕ, (T^[n]) ⁻¹' B (a * rho ^ n))
      ≤ ENNReal.ofReal (c * a / (1 - rho)) := by
    intro a ha
    have hbound : ∀ n : ℕ, μ ((T^[n]) ⁻¹' B (a * rho ^ n)) ≤ ENNReal.ofReal (c * a * rho ^ n) := by
      intro n
      have hpos : 0 < a * rho ^ n := by positivity
      have hle := Measure.le_map_apply (μ := μ)
        ((hmp.iterate n).measurable).aemeasurable (B (a * rho ^ n))
      rw [(hmp.iterate n).map_eq] at hle
      have h2 := hthin (a * rho ^ n) hpos
      refine le_trans (le_trans hle h2) ?_
      rw [mul_assoc]
    calc μ (⋃ n : ℕ, (T^[n]) ⁻¹' B (a * rho ^ n))
        ≤ ∑' n : ℕ, μ ((T^[n]) ⁻¹' B (a * rho ^ n)) := measure_iUnion_le _
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (c * a * rho ^ n) := ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (c * a / (1 - rho)) := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
                  ((summable_geometric_of_lt_one hrho0.le hrho1).mul_left (c * a))]
            congr 1
            rw [tsum_mul_left, tsum_geometric_of_lt_one hrho0.le hrho1, div_eq_mul_inv]
  -- The bad set at level `m`: points whose orbit dips below the scale `r (1/2)^{m+1} ρⁿ`.
  have hkey : ∀ m : ℕ, μ {x : α | ¬ (∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ, δ' * rho ^ n ≤ f (T^[n] x))}
      ≤ ENNReal.ofReal (c * r / (2 * (1 - rho)) * (1/2:ℝ)^m) := by
    intro m
    have ha : 0 < r * (1/2:ℝ)^(m+1) := by positivity
    have hsub1 : {x : α | ¬ (∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ, δ' * rho ^ n ≤ f (T^[n] x))}
        ⊆ {x : α | ∃ n : ℕ, f (T^[n] x) < r * (1/2:ℝ)^(m+1) * rho^n} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hx ⟨r * (1/2:ℝ)^(m+1), by positivity, hcon⟩
    have hsub2 : {x : α | ∃ n : ℕ, f (T^[n] x) < r * (1/2:ℝ)^(m+1) * rho^n}
        ⊆ ⋃ n : ℕ, (T^[n]) ⁻¹' B (r * (1/2:ℝ)^(m+1) * rho^n) := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      obtain ⟨n, hn⟩ := hx
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      simp only [Set.mem_preimage]
      refine hBsmall _ _ (le_of_lt hn) ?_
      have h1 : (1/2:ℝ)^(m+1) < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero m)
      have h2 : rho ^ n ≤ 1 := pow_le_one₀ hrho0.le (le_of_lt hrho1)
      have hpos : 0 < r * (1/2:ℝ)^(m+1) := by positivity
      have hle1 : r * (1/2:ℝ)^(m+1) * rho^n ≤ r * (1/2:ℝ)^(m+1) := by
        calc r * (1/2:ℝ)^(m+1) * rho^n ≤ r * (1/2:ℝ)^(m+1) * 1 :=
              mul_le_mul_of_nonneg_left h2 (le_of_lt hpos)
          _ = r * (1/2:ℝ)^(m+1) := by ring
      have hrlt : r * (1/2:ℝ)^(m+1) < r := by
        have := mul_lt_mul_of_pos_left h1 hr
        simpa using this
      linarith
    calc μ {x : α | ¬ (∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ, δ' * rho ^ n ≤ f (T^[n] x))}
        ≤ μ {x : α | ∃ n : ℕ, f (T^[n] x) < r * (1/2:ℝ)^(m+1) * rho^n} := measure_mono hsub1
      _ ≤ μ (⋃ n : ℕ, (T^[n]) ⁻¹' B (r * (1/2:ℝ)^(m+1) * rho^n)) := measure_mono hsub2
      _ ≤ ENNReal.ofReal (c * (r * (1/2:ℝ)^(m+1)) / (1 - rho)) := hpre _ ha
      _ = ENNReal.ofReal (c * r / (2 * (1 - rho)) * (1/2:ℝ)^m) := by
            congr 1
            rw [pow_succ]
            field_simp
  -- The bounding sequence tends to `0`, so the bad set is null.
  have htend : Tendsto (fun m : ℕ => ENNReal.ofReal (c * r / (2 * (1 - rho)) * (1/2:ℝ)^m))
      atTop (𝓝 0) := by
    have hreal : Tendsto (fun m : ℕ => c * r / (2 * (1 - rho)) * (1/2:ℝ)^m) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).const_mul (c * r / (2 * (1 - rho)))
      simpa using h
    have h2 := ENNReal.continuous_ofReal.tendsto 0
    rw [ENNReal.ofReal_zero] at h2
    exact h2.comp hreal
  rw [MeasureTheory.ae_iff]
  exact le_antisymm (ge_of_tendsto' htend hkey) bot_le

end Work.EKLC6Route
