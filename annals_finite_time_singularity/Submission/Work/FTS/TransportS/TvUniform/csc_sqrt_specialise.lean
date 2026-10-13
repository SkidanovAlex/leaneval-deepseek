import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.TvUniform

theorem csc_sqrt_specialise {f g : ℝ → ℝ} {c θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hf : 0 ≤ f θ) (hg : 0 ≤ g θ) :
    2 * (Real.sin (2 * θ))⁻¹ * Real.sqrt (f θ * g θ)
      = 2 * Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
          * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hs0 : 0 ≤ Real.sin (2 * θ) := le_of_lt hs
  have hA : 0 ≤ f θ * (Real.sin (2 * θ)) ^ (-c) :=
    mul_nonneg hf (Real.rpow_nonneg hs0 _)
  have hsq : Real.sqrt ((Real.sin (2 * θ)) ^ (-2 : ℝ)) = (Real.sin (2 * θ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs0 (-2) (1/2),
      show (-2:ℝ) * (1/2) = -1 by norm_num, Real.rpow_neg_one]
  have hprod : (f θ * (Real.sin (2 * θ)) ^ (-c)) * (g θ * (Real.sin (2 * θ)) ^ (c - 2))
      = (f θ * g θ) * (Real.sin (2 * θ)) ^ (-2 : ℝ) := by
    have h1 : (f θ * (Real.sin (2 * θ)) ^ (-c)) * (g θ * (Real.sin (2 * θ)) ^ (c - 2))
        = (f θ * g θ) * ((Real.sin (2 * θ)) ^ (-c) * (Real.sin (2 * θ)) ^ (c - 2)) := by
      ring
    rw [h1, ← Real.rpow_add hs (-c) (c - 2),
      show -c + (c - 2) = (-2:ℝ) by ring]
  have hR : 2 * Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
        * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2))
      = 2 * (Real.sqrt (f θ * g θ) * (Real.sin (2 * θ))⁻¹) := by
    calc 2 * Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
            * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2))
        = 2 * (Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
            * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2))) := by ring
      _ = 2 * Real.sqrt ((f θ * (Real.sin (2 * θ)) ^ (-c))
            * (g θ * (Real.sin (2 * θ)) ^ (c - 2))) := by
            rw [← Real.sqrt_mul hA (g θ * (Real.sin (2 * θ)) ^ (c - 2))]
      _ = 2 * Real.sqrt ((f θ * g θ) * (Real.sin (2 * θ)) ^ (-2 : ℝ)) := by rw [hprod]
      _ = 2 * (Real.sqrt (f θ * g θ) * Real.sqrt ((Real.sin (2 * θ)) ^ (-2 : ℝ))) := by
            rw [Real.sqrt_mul (mul_nonneg hf hg) ((Real.sin (2 * θ)) ^ (-2 : ℝ))]
      _ = 2 * (Real.sqrt (f θ * g θ) * (Real.sin (2 * θ))⁻¹) := by rw [hsq]
  rw [hR]
  ring

end Work.FTS.TransportS.TvUniform
