import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

/-- The ratio of a positive strictly decreasing function to a positive strictly
increasing function is strictly decreasing. -/
lemma StrictAntiOn.div_strictMonoOn {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : StrictAntiOn f s) (hg : StrictMonoOn g s)
    (hfpos : ∀ x ∈ s, 0 < f x) (hgpos : ∀ x ∈ s, 0 < g x) :
    StrictAntiOn (fun x => f x / g x) s := by
  intro a ha b hb hab
  have hfab : f b < f a := hf ha hb hab
  have hgab : g a < g b := hg ha hb hab
  have hfb : 0 < f b := hfpos b hb
  have hga : 0 < g a := hgpos a ha
  calc f b / g b < f b / g a := div_lt_div_of_pos_left hfb hga hgab
    _ < f a / g a := div_lt_div_of_pos_right hfab hga

theorem log_one_add_inv_div_log_strictAntiOn :
    StrictAntiOn (fun t : ℝ => Real.log (1 + 1/t)/Real.log t) (Set.Ioi 1) := by
  apply StrictAntiOn.div_strictMonoOn
  · -- the numerator `log (1 + 1/t)` is strictly decreasing on `(1,∞)`
    intro a ha b hb hab
    rw [Set.mem_Ioi] at ha hb
    have h1 : (1 : ℝ) / b < 1 / a := one_div_lt_one_div_of_lt (by linarith) hab
    have h2 : 1 + 1 / b < 1 + 1 / a := by linarith
    have hb0 : (0 : ℝ) < b := by linarith
    have h3 : 0 < 1 + 1 / b := by
      have := one_div_pos.mpr hb0
      linarith
    exact Real.log_lt_log h3 h2
  · -- the denominator `log t` is strictly increasing on `(1,∞)`
    refine Real.strictMonoOn_log.mono ?_
    intro x hx
    rw [Set.mem_Ioi] at hx ⊢
    linarith
  · -- positivity of the numerator
    intro t ht
    rw [Set.mem_Ioi] at ht
    have ht0 : (0 : ℝ) < t := by linarith
    apply Real.log_pos
    have := one_div_pos.mpr ht0
    linarith
  · -- positivity of the denominator
    intro t ht
    rw [Set.mem_Ioi] at ht
    exact Real.log_pos ht

end Commons.Analysis.Real