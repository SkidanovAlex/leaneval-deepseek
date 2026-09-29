import Mathlib

namespace Work.Haupt

/-- The contour integral `∮ t in C(0,ρ), t^(-(n+1)) * f t` is independent of the radius `ρ > 0`,
for `f` complex differentiable on the punctured plane `{t ≠ 0}`. This is the Cauchy–Goursat
theorem for the annulus: the integrand `t ↦ t^(-(n+1)) * f t` is holomorphic on `ℂ \ {0}`, hence
`C(0,ρ)` and `C(0,ρ')` are homologous in `ℂ \ {0}` and the integrals agree. -/
theorem circleIntegral_independent_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {t : ℂ | t ≠ 0}) (n : ℤ) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') :
    (∮ t in C(0, ρ), t ^ (-(n + 1)) * f t) = (∮ t in C(0, ρ'), t ^ (-(n + 1)) * f t) := by
  -- Reduce to Cauchy–Goursat on the annulus `{r ≤ ‖z‖ ≤ R}` for a single pair `r ≤ R`.
  have key : ∀ {r R : ℝ}, 0 < r → r ≤ R →
      (∮ t in C(0, R), t ^ (-(n + 1)) * f t) = (∮ t in C(0, r), t ^ (-(n + 1)) * f t) := by
    intro r R hr hrR
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := 0) (r := r)
      (R := R) hr hrR (s := ∅) Set.countable_empty ?_ ?_
    · -- Continuity of the integrand on the closed annulus.
      refine ((continuousOn_zpow₀ (-(n + 1))).mul hf.continuousOn).mono ?_
      rintro z ⟨hzR, hzr⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      simp only [Metric.mem_closedBall, dist_zero_right, norm_zero] at hzR
      simp only [Metric.mem_ball, dist_zero_right, norm_zero] at hzr
      linarith
    · -- Complex differentiability of the integrand on the open annulus.
      rintro z ⟨⟨hzR, hzr⟩, -⟩
      simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hzR hzr
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp only [norm_zero] at hzr
        linarith
      refine (differentiableAt_zpow.mpr (Or.inl hz0)).mul (hf.differentiableAt ?_)
      rw [show {t : ℂ | t ≠ 0} = ({0} : Set ℂ)ᶜ from by ext; simp]
      exact IsOpen.mem_nhds isOpen_compl_singleton (by simpa using hz0)
  rcases le_total ρ ρ' with hle | hle
  · exact (key hρ hle).symm
  · exact key hρ' hle

end Work.Haupt
