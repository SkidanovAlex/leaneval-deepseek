import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Filter
open scoped Topology

/-- The indefinite integral of an integrable function is absolutely continuous: on a `(0, δ)`
the integral of `|F|` gets arbitrarily small. -/
theorem near_integral_abs_lt {F : ℝ → ℝ} (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∫ t in Set.Ioo 0 δ, |F t| < ε := by
  -- Truncate `F` to `(0,1)` so that it becomes globally integrable.
  let G : ℝ → ℝ := Set.indicator (Set.Ioo (0:ℝ) 1) F
  have hGint : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).2 hF
  have hGnorm : Integrable (fun x => ‖G x‖) volume := hGint.norm
  -- The intervals `(0, 1/(n+1))` shrink to a null set.
  have hmeas : Tendsto (fun n : ℕ => volume (Set.Ioo (0:ℝ) (1 / ((n:ℝ) + 1)))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [ENNReal.ofReal_zero] at h
    simpa only [Real.volume_Ioo, sub_zero] using h
  -- Absolute continuity of the integral.
  have hlim : Tendsto (fun n : ℕ => ∫ x in Set.Ioo (0:ℝ) (1 / ((n:ℝ) + 1)), ‖G x‖) atTop (𝓝 0) :=
    hGnorm.tendsto_setIntegral_nhds_zero hmeas
  have hev : ∀ᶠ n : ℕ in atTop, (∫ x in Set.Ioo (0:ℝ) (1 / ((n:ℝ) + 1)), ‖G x‖) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- Take `δ = 1/(max N 1 + 1)`, so that automatically `0 < δ < 1`.
  refine ⟨1 / (((max N 1 : ℕ) : ℝ) + 1), ?_, ?_, ?_⟩
  · positivity
  · rw [div_lt_one (by positivity)]
    have h1 : (1:ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
    linarith
  · have hδ1 : 1 / (((max N 1 : ℕ) : ℝ) + 1) ≤ 1 := le_of_lt (by
      rw [div_lt_one (by positivity)]
      have h1 : (1:ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
      linarith)
    have hkey : (∫ x in Set.Ioo (0:ℝ) (1 / (((max N 1 : ℕ) : ℝ) + 1)), ‖G x‖) < ε :=
      hN (max N 1) (le_max_left N 1)
    -- On `(0, δ) ⊆ (0,1)` the truncation is invisible.
    have hcongr : (∫ x in Set.Ioo (0:ℝ) (1 / (((max N 1 : ℕ) : ℝ) + 1)), ‖G x‖)
        = ∫ x in Set.Ioo (0:ℝ) (1 / (((max N 1 : ℕ) : ℝ) + 1)), |F x| := by
      refine setIntegral_congr_fun measurableSet_Ioo ?_
      intro x hx
      have hx1 : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx.1, lt_of_lt_of_le hx.2 hδ1⟩
      change ‖G x‖ = |F x|
      rw [show G x = Set.indicator (Set.Ioo (0:ℝ) 1) F x from rfl,
        Set.indicator_of_mem hx1 F, Real.norm_eq_abs]
    rw [hcongr] at hkey
    exact hkey

end Work.FTS.PhiStar.Honesty
