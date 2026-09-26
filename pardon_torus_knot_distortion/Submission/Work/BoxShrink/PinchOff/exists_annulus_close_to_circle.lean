import Mathlib

set_option linter.style.haveILetI false

namespace Work.BoxShrink.PinchOff

open Set Metric

/-- Given a map `h` on the closed unit disc which is continuous on the annulus
`{z | r ≤ ‖z‖}` and maps the unit circle into `C`, every sufficiently thin
collar `{z | t ≤ ‖z‖ ≤ 1}` around the unit circle is mapped into an arbitrarily
small neighbourhood of `C`. -/
theorem exists_annulus_close_to_circle {X : Type*} [PseudoMetricSpace X]
    (h : Metric.closedBall (0 : ℂ) 1 → X) (C : Set X) (r : ℝ) (hr : r < 1)
    (hh : ContinuousOn h {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖})
    (hC : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → h z ∈ C) :
    ∀ ρ > 0, ∃ t, r ≤ t ∧ t < 1 ∧
      ∀ z : Metric.closedBall (0 : ℂ) 1, t ≤ ‖(z : ℂ)‖ → ‖(z : ℂ)‖ ≤ 1 →
        ∃ c ∈ C, dist (h z) c < ρ := by
  intro ρ hρ
  -- The annulus on which `h` is continuous.
  set A : Set (Metric.closedBall (0 : ℂ) 1) := {z | r ≤ ‖(z : ℂ)‖} with hAdef
  -- The disc is compact, so `A`, being closed, is compact.
  haveI : CompactSpace (Metric.closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  have hAclosed : IsClosed A := by
    rw [hAdef]
    exact IsClosed.preimage (continuous_subtype_val.norm) isClosed_Ici
  have hAcompact : IsCompact A := hAclosed.isCompact
  -- Heine–Cantor: `h` is uniformly continuous on `A`.
  have hunif : UniformContinuousOn h A := hAcompact.uniformContinuousOn_of_continuous hh
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδpos, hδ⟩ := hunif ρ hρ
  -- We take the collar of width `δ/2`, keeping it inside `r ≤ ‖z‖` and away
  -- from the origin.
  refine ⟨max (max r (1 - δ / 2)) (1 / 2), ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · apply max_lt
    · exact max_lt hr (by linarith)
    · norm_num
  · intro z hzt hzle
    have hzge : (1 : ℝ) / 2 ≤ ‖(z : ℂ)‖ := le_trans (le_max_right _ _) hzt
    have hzpos : 0 < ‖(z : ℂ)‖ := lt_of_lt_of_le (by norm_num) hzge
    have hcne : (((‖(z : ℂ)‖ : ℝ)) : ℂ) ≠ 0 := by
      simp [Complex.ofReal_eq_zero, ne_of_gt hzpos]
    -- The radial projection of `z` to the unit circle.
    have hz'le : ‖(z : ℂ) / (((‖(z : ℂ)‖ : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (ne_of_gt hzpos)]
    let z' : Metric.closedBall (0 : ℂ) 1 :=
      ⟨(z : ℂ) / (((‖(z : ℂ)‖ : ℝ)) : ℂ), by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hz'le⟩
    have hz'norm : ‖((z' : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
      show ‖(z : ℂ) / (((‖(z : ℂ)‖ : ℝ)) : ℂ)‖ = 1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (ne_of_gt hzpos)]
    -- The distance from `z` to its radial projection is `1 - ‖z‖`.
    have hdistval : dist ((z : Metric.closedBall (0 : ℂ) 1) : ℂ)
        ((z' : Metric.closedBall (0 : ℂ) 1) : ℂ) = 1 - ‖(z : ℂ)‖ := by
      show dist ((z : ℂ)) ((z : ℂ) / (((‖(z : ℂ)‖ : ℝ)) : ℂ)) = 1 - ‖(z : ℂ)‖
      rw [dist_eq_norm]
      rw [show (z : ℂ) - (z : ℂ) / (((‖(z : ℂ)‖ : ℝ)) : ℂ)
            = (z : ℂ) * (((((‖(z : ℂ)‖ : ℝ)) : ℂ) - 1) / (((‖(z : ℂ)‖ : ℝ)) : ℂ)) by
          field_simp]
      rw [norm_mul, norm_div]
      rw [show ‖((((‖(z : ℂ)‖ : ℝ)) : ℂ) - 1)‖ = 1 - ‖(z : ℂ)‖ by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (by linarith)]
          ring]
      rw [show ‖(((‖(z : ℂ)‖ : ℝ)) : ℂ)‖ = ‖(z : ℂ)‖ by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]]
      field_simp
    refine ⟨h z', hC z' hz'norm, hδ z ?_ z' ?_ ?_⟩
    · rw [hAdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hzt
    · rw [hAdef]
      show r ≤ ‖((z' : Metric.closedBall (0 : ℂ) 1) : ℂ)‖
      rw [hz'norm]; exact le_of_lt hr
    · rw [Subtype.dist_eq, hdistval]
      have hb : 1 - ‖(z : ℂ)‖ ≤ δ / 2 := by
        have : 1 - δ / 2 ≤ ‖(z : ℂ)‖ :=
          le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hzt
        linarith
      linarith

end Work.BoxShrink.PinchOff
