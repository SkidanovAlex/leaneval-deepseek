import Mathlib

open scoped Topology
open Filter

namespace Work.Pert.pert2v2.GatePreimageReBound

-- Purely real threshold lemma: a linear factor times a decaying exponential is eventually ≤ 1.
theorem exists_mul_exp_neg_le (M κ c : ℝ) (hM : 0 < M) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → (t + c) * M * Real.exp (-(κ * t)) ≤ 1 := by
  have hκt : Tendsto (fun t : ℝ => κ * t) atTop atTop := tendsto_id.const_mul_atTop hκ
  -- `x ↦ x * exp (-x)` vanishes at `+∞`, hence so does `t ↦ κ * t * exp (-(κ * t))`.
  have h1 : Tendsto (fun t : ℝ => κ * t * Real.exp (-(κ * t))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hκt
    simpa [Function.comp_def, pow_one] using this
  -- decompose the target function as `(M/κ) • (κt * exp (-κt)) + (M*c) • exp (-κt)`.
  have h2 : Tendsto (fun t : ℝ => (t + c) * M * Real.exp (-(κ * t))) atTop (𝓝 0) := by
    have h3 : Tendsto (fun t : ℝ => Real.exp (-(κ * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hκt
    have h4 := (h1.const_mul (M / κ)).add (h3.const_mul (M * c))
    have heq : (fun t : ℝ => (t + c) * M * Real.exp (-(κ * t)))
        = fun t : ℝ => M / κ * (κ * t * Real.exp (-(κ * t))) + M * c * Real.exp (-(κ * t)) := by
      funext t
      field_simp
    rw [heq]
    simpa using h4
  -- the limit being `0 < 1`, the inequality holds eventually.
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (h2.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)))
  exact ⟨T, fun t ht => hT t ht⟩

end Work.Pert.pert2v2.GatePreimageReBound
