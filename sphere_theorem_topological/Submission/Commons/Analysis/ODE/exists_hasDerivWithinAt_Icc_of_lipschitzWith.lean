import Mathlib.Analysis.ODE.ExistUnique

namespace Commons.Analysis.ODE

open Filter Set Metric
open scoped Topology NNReal

/-- **Local existence for a Lipschitz ODE.**  If `f : E → E` is Lipschitz with constant `L` on a
complete normed space and `x : E`, then for every `t₀ : ℝ` there is `ε > 0` and a curve
`y : ℝ → E` with `y t₀ = x` solving `y' = f ∘ y` on the closed interval `[t₀ - ε, t₀ + ε]`
(with one-sided derivatives at the endpoints). -/
theorem exists_hasDerivWithinAt_Icc_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {L : NNReal} (hf : LipschitzWith L f) (x : E) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ y : ℝ → E, y t₀ = x ∧
      ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
        HasDerivWithinAt y (f (y t)) (Set.Icc (t₀ - ε) (t₀ + ε)) t := by
  classical
  -- A bound on `‖f‖` on the unit ball around `x`.
  set M : ℝ≥0 := ‖f x‖₊ + L with hM
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  -- The time half-width.
  set ε : ℝ := 1 / ((M : ℝ) + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hMε : (M : ℝ) * ε ≤ 1 := by
    rw [hε, mul_one_div, div_le_one hMpos]; linarith
  -- `f` is bounded on `closedBall x 1` by `M`.
  have hb : ∀ y ∈ closedBall x (1 : ℝ≥0), ‖f y‖ ≤ (M : ℝ) := by
    intro y hy
    rw [hM]
    push_cast
    have h1 : ‖f y - f x‖ ≤ (L : ℝ) * ‖y - x‖ := by
      simpa [dist_eq_norm] using hf.dist_le_mul y x
    have h2 : ‖y - x‖ ≤ 1 := by
      rw [mem_closedBall_iff_norm] at hy
      exact_mod_cast hy
    calc ‖f y‖ = ‖(f y - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖f y - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖y - x‖ + ‖f x‖ := by gcongr
      _ ≤ (L : ℝ) * 1 + ‖f x‖ := by gcongr
      _ = ‖f x‖ + (L : ℝ) := by ring
  -- Assemble the Picard–Lindelöf hypotheses.
  have hPL : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, by constructor <;> linarith⟩
      x (1 : ℝ≥0) 0 M L := by
    apply IsPicardLindelof.of_time_independent
    · intro y hy; exact hb y hy
    · exact hf.lipschitzOnWith
    · simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
      simp only [NNReal.coe_one, NNReal.coe_zero, sub_zero]
      exact hMε
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨ε, hεpos, α, hα0, fun t ht => hα t ht⟩

end Commons.Analysis.ODE