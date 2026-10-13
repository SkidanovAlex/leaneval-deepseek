import Mathlib

namespace Work.WilE4.CAD

/-- A continuous function that does not vanish on a compact set is bounded below by a positive
constant.  Here the compact set is the circle `Metric.sphere c R`: for `R < 0` it is empty (take
`m = 1`), and for `R ≥ 0` the norm `‖p.eval ·‖` attains its minimum at some point `z₀` of the
sphere, which is positive because `p` has no zero there. -/
theorem exists_pos_le_norm_on_sphere (p : Polynomial ℂ) (c : ℂ) (R : ℝ)
    (hno : ∀ z : ℂ, dist z c = R → p.eval z ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℂ, dist z c = R → m ≤ ‖p.eval z‖ := by
  rcases lt_or_ge R 0 with hR | hR
  · -- the sphere of negative radius is empty, so any positive `m` works
    refine ⟨1, one_pos, fun z hz => ?_⟩
    have h1 : (0 : ℝ) ≤ dist z c := dist_nonneg
    rw [hz] at h1
    exact absurd h1 (not_le.mpr hR)
  · -- the sphere is compact and nonempty; the norm attains its minimum there
    have hne : (Metric.sphere c R).Nonempty := by
      refine ⟨c + (R : ℂ), Metric.mem_sphere.mpr ?_⟩
      rw [dist_eq_norm]
      have h2 : c + (R : ℂ) - c = (R : ℂ) := by ring
      rw [h2, Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs,
        abs_of_nonneg hR]
    obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere c R).exists_isMinOn hne
      ((Polynomial.continuous p).norm.continuousOn)
    exact ⟨‖p.eval z0‖, norm_pos_iff.mpr (hno z0 (Metric.mem_sphere.mp hz0)),
      fun z hz => hmin (Metric.mem_sphere.mpr hz)⟩

end Work.WilE4.CAD
