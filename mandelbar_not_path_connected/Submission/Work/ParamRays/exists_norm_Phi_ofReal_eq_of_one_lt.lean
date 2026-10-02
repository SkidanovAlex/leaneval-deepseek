import Mathlib
import Submission.Work.ParamRays.RealSlice

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

/-- Every radius `r > 1` is attained by `‖Φ‖` on the real ray `(1/4, ∞)`. -/
theorem exists_norm_Phi_ofReal_eq_of_one_lt (hN : Work.ParamRays.NakaneInput) {r : ℝ}
    (hr : 1 < r) : ∃ x : ℝ, 1 / 4 < x ∧ ‖Work.ParamRays.Phi (x : ℂ)‖ = r := by
  -- `x ↦ ‖Φ (x : ℂ)‖` is continuous on the real ray `(1/4, ∞)`
  have hcont : ContinuousOn (fun x : ℝ => ‖Phi (x : ℂ)‖) (Set.Ioi (1 / 4 : ℝ)) := by
    have h1 : ContinuousOn (fun x : ℝ => (x : ℂ)) (Set.Ioi (1 / 4 : ℝ)) :=
      Complex.continuous_ofReal.continuousOn
    have h2 : ContinuousOn Phi (Mbᶜ) := continuousOn_Phi_compl hN
    exact (h2.comp h1 fun x hx => real_not_mem_Mb_of_one_fourth_lt hx).norm
  -- near the root point `1/4` the modulus is close to `1`, hence below `r`
  obtain ⟨δ, hδpos, hδ⟩ := exists_norm_Phi_lt hN quarter_mem (show (0 : ℝ) < r - 1 by linarith)
  set x₀ : ℝ := 1 / 4 + δ / 2 with hx₀def
  have hx₀ : 1 / 4 < x₀ := by rw [hx₀def]; linarith
  have hdist : dist (x₀ : ℂ) (1 / 4 : ℂ) < δ := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.dist_eq,
      show (x₀ : ℂ) - ((1 / 4 : ℝ) : ℂ) = ((x₀ - 1 / 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs, hx₀def,
      show (1 / 4 + δ / 2 - 1 / 4 : ℝ) = δ / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have hFx₀ : ‖Phi (x₀ : ℂ)‖ < r := by
    have := hδ (x₀ : ℂ) hdist (real_not_mem_Mb_of_one_fourth_lt hx₀)
    linarith
  -- far out the modulus is large, hence above `r`
  obtain ⟨a, ha⟩ := Filter.tendsto_atTop_atTop.mp (tendsto_norm_Phi_ofReal_atTop hN) r
  set x₁ : ℝ := max a (x₀ + 1) with hx₁def
  have hx₀x₁ : x₀ ≤ x₁ := by
    rw [hx₁def]; exact le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)
  have hFx₁ : r ≤ ‖Phi (x₁ : ℂ)‖ := ha x₁ (le_max_left _ _)
  -- the intermediate value theorem on `[x₀, x₁] ⊆ (1/4, ∞)`
  have hsub : Set.Icc x₀ x₁ ⊆ Set.Ioi (1 / 4 : ℝ) := fun x hx => lt_of_lt_of_le hx₀ hx.1
  have hIVT : Set.Icc (‖Phi (x₀ : ℂ)‖) (‖Phi (x₁ : ℂ)‖) ⊆
      (fun x : ℝ => ‖Phi (x : ℂ)‖) '' Set.Icc x₀ x₁ :=
    intermediate_value_Icc hx₀x₁ (hcont.mono hsub)
  have hr_mem : r ∈ Set.Icc (‖Phi (x₀ : ℂ)‖) (‖Phi (x₁ : ℂ)‖) := ⟨le_of_lt hFx₀, hFx₁⟩
  obtain ⟨x, hx, hFx⟩ := hIVT hr_mem
  exact ⟨x, lt_of_lt_of_le hx₀ hx.1, hFx⟩

end Work.ParamRays
