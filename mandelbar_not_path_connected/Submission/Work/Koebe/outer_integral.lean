import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory

namespace Work.Koebe

/-- For a curve parametrized by `r ↦ r` the "outer" part of the area integral
contributes `π · conj ζ`.  Concretely, for `‖ζ‖ < Λ`,
`∫_{0}^{Λ} r · [r < ‖ζ‖] · (2π/ζ) dr = π · conj ζ`. -/
theorem outer_integral (Λ : ℝ) (ζ : ℂ) (h : ‖ζ‖ < Λ) :
    ∫ r in Set.Ioo (0:ℝ) Λ, (r:ℂ) * (if r < ‖ζ‖ then 2 * Real.pi / ζ else 0)
      = (Real.pi : ℂ) * (starRingEnd ℂ ζ) := by
  -- The scalar integral `∫_{0}^{‖ζ‖} r dr` equals `‖ζ‖²/2`.
  have hkey : ∫ r in Set.Ioo (0:ℝ) ‖ζ‖, (r:ℂ) = ((‖ζ‖^2/2 : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (norm_nonneg ζ)]
    rw [intervalIntegral.integral_ofReal]
    rw [integral_id]
    norm_num
  -- On `(0, Λ)` the support condition `r < ‖ζ‖` selects exactly the interval `(0, ‖ζ‖)`.
  have hset : Set.Ioo (0:ℝ) Λ ∩ Set.Iio ‖ζ‖ = Set.Ioo (0:ℝ) ‖ζ‖ := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, lt_trans h3 h⟩, h3⟩
  -- Final algebra: `(‖ζ‖²/2) · (2π/ζ) = π · conj ζ`.
  have halg : ((‖ζ‖^2/2 : ℝ) : ℂ) * (2 * (Real.pi:ℂ) / ζ)
      = (Real.pi:ℂ) * (starRingEnd ℂ) ζ := by
    by_cases hz : ζ = 0
    · subst hz; simp
    · have h1 : ((‖ζ‖^2 : ℝ) : ℂ) = ζ * (starRingEnd ℂ) ζ := by
        rw [Complex.sq_norm, ← Complex.mul_conj]
      have h2 : ((‖ζ‖^2/2 : ℝ) : ℂ) = ((‖ζ‖^2 : ℝ) : ℂ) / 2 := by push_cast; ring
      rw [h2, h1]
      field_simp
  calc
    ∫ r in Set.Ioo (0:ℝ) Λ, (r:ℂ) * (if r < ‖ζ‖ then 2 * Real.pi / ζ else 0)
        = ∫ r in Set.Ioo (0:ℝ) Λ,
            (Set.Iio ‖ζ‖).indicator (fun r => (r:ℂ) * (2 * Real.pi / ζ)) r := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          intro r _
          by_cases hc : r < ‖ζ‖ <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_Iio, hc]
    _ = ∫ r in Set.Ioo (0:ℝ) Λ ∩ Set.Iio ‖ζ‖, (r:ℂ) * (2 * Real.pi / ζ) := by
          rw [MeasureTheory.setIntegral_indicator measurableSet_Iio]
    _ = ∫ r in Set.Ioo (0:ℝ) ‖ζ‖, (r:ℂ) * (2 * Real.pi / ζ) := by rw [hset]
    _ = (∫ r in Set.Ioo (0:ℝ) ‖ζ‖, (r:ℂ)) * (2 * Real.pi / ζ) := by
          rw [MeasureTheory.integral_mul_const]
    _ = ((‖ζ‖^2/2 : ℝ) : ℂ) * (2 * Real.pi / ζ) := by rw [hkey]
    _ = (Real.pi : ℂ) * (starRingEnd ℂ ζ) := halg

end Work.Koebe
