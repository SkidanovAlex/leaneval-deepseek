import Mathlib

namespace Work.FIArea6Road

open Filter

/-- `exp (x/8) / x ^ (2m)` tends to `+∞` as `x → +∞`. -/
lemma tendsto_exp_div_eight_div_pow (m : ℕ) :
    Tendsto (fun x : ℝ => Real.exp (x / 8) / x ^ (2 * m)) atTop atTop := by
  have h := (Real.tendsto_exp_div_pow_atTop (2 * m)).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 8))
  have h2 := h.const_mul_atTop (show (0 : ℝ) < (1 / 8) ^ (2 * m) by positivity)
  refine h2.congr' (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, id_eq]
  rw [div_pow, mul_div_assoc', div_pow]
  field_simp
  ring

/-- `exp (√L/8) / L ^ m` tends to `+∞` as `L → +∞`. -/
lemma tendsto_exp_sqrt_div_pow (m : ℕ) :
    Tendsto (fun L : ℝ => Real.exp (Real.sqrt L / 8) / L ^ m) atTop atTop := by
  have h := (tendsto_exp_div_eight_div_pow m).comp Real.tendsto_sqrt_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  simp only [Function.comp_apply]
  rw [pow_mul, Real.sq_sqrt hL]

theorem PolyExpUltimately (α : ℝ) (m : ℕ) (hα : 0 < α) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ L : ℝ, Λ ≤ L →
      α * L ^ m ≤ Real.exp (L / 2) ∧ α * L ^ m ≤ Real.exp (L / 8) ∧
      α * L ^ m ≤ Real.exp (3 * Real.sqrt L / 4) ∧
      α * L ^ m ≤ Real.exp (Real.sqrt L / 8) := by
  -- The ratio `exp (√L/8) / (α L^m)` tends to `+∞`, hence eventually dominates `1`.
  have hC : Tendsto (fun L : ℝ => Real.exp (Real.sqrt L / 8) / (α * L ^ m)) atTop atTop := by
    have h := (tendsto_exp_sqrt_div_pow m).const_mul_atTop (inv_pos.mpr hα)
    refine h.congr' (Eventually.of_forall fun L => ?_)
    field_simp
  have hbound : ∀ᶠ L in atTop, α * L ^ m ≤ Real.exp (Real.sqrt L / 8) := by
    have h1 : ∀ᶠ L in atTop, (1 : ℝ) ≤ Real.exp (Real.sqrt L / 8) / (α * L ^ m) :=
      hC.eventually (eventually_ge_atTop 1)
    filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with L hL hL1
    have hpos : 0 < α * L ^ m := mul_pos hα (pow_pos (by linarith) m)
    rw [le_div_iff₀ hpos] at hL
    linarith [hL]
  obtain ⟨Λ0, hΛ0⟩ := eventually_atTop.1 hbound
  refine ⟨max 1 Λ0, lt_max_iff.mpr (Or.inl one_pos), fun L hL => ?_⟩
  have hL0 : Λ0 ≤ L := le_trans (le_max_right _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hmain : α * L ^ m ≤ Real.exp (Real.sqrt L / 8) := hΛ0 L hL0
  have hsqrt_nonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsqrt_le : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  refine ⟨?_, ?_, ?_, hmain⟩
  · exact le_trans hmain (Real.exp_le_exp.mpr (by linarith))
  · exact le_trans hmain (Real.exp_le_exp.mpr (by linarith))
  · exact le_trans hmain (Real.exp_le_exp.mpr (by linarith))

end Work.FIArea6Road
