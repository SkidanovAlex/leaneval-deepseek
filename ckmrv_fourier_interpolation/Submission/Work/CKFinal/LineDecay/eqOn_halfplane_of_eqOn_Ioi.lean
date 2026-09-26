import Mathlib

open scoped Topology

namespace Work.CKFinal.LineDecay

/-- **Identity principle on the half-plane `{z : ℂ | -π < z.re}`.**  Two functions holomorphic on
that (open, convex, hence preconnected) half-plane which agree on the real ray `(2π, ∞)` agree on
the whole half-plane.

Proved from `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` with `z₀ = ↑(4π)`: the zero set of
`F - G` contains `↑s` for every real `s > 2π`, and these points accumulate at `↑(4π)` from the left
(`s = 4π - ε/2` for small `ε > 0`), so the agreement holds frequently in `𝓝[≠] (↑(4π))`. -/
theorem eqOn_halfplane_of_eqOn_Ioi (F G : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | -(Real.pi) < z.re})
    (hG : AnalyticOnNhd ℂ G {z : ℂ | -(Real.pi) < z.re})
    (h : ∀ s : ℝ, 2 * Real.pi < s → F (s : ℂ) = G (s : ℂ)) :
    ∀ z : ℂ, -(Real.pi) < z.re → F z = G z := by
  -- The half-plane is convex, hence preconnected.
  have hU : IsPreconnected {z : ℂ | -(Real.pi) < z.re} := by
    have hc : Convex ℝ (Complex.re ⁻¹' Set.Ioi (-(Real.pi))) :=
      (convex_Ioi (-(Real.pi))).linear_preimage (Complex.reCLM.toLinearMap : ℂ →ₗ[ℝ] ℝ)
    have hthis : {z : ℂ | -(Real.pi) < z.re} = Complex.re ⁻¹' Set.Ioi (-(Real.pi)) := by
      ext z; simp
    rw [hthis]
    exact hc.isPreconnected
  -- The base point `↑(4π)` lies in the half-plane.
  have h0 : ((4 * Real.pi : ℝ) : ℂ) ∈ {z : ℂ | -(Real.pi) < z.re} := by
    show -(Real.pi) < ((4 * Real.pi : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith [Real.pi_pos]
  -- `F` and `G` agree frequently at `↑(4π)` (coming from the left along the real axis).
  have hfreq : ∃ᶠ z in 𝓝[≠] ((4 * Real.pi : ℝ) : ℂ), F z = G z := by
    refine (mem_closure_ne_iff_frequently_within
      (z := ((4 * Real.pi : ℝ) : ℂ)) (s := {w : ℂ | F w = G w})).mp ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (ε / 2) Real.pi with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) Real.pi_pos
    have hδlt : δ < ε := by
      have hle : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
      linarith
    have hδpi : δ ≤ Real.pi := by rw [hδdef]; exact min_le_right _ _
    refine ⟨((4 * Real.pi - δ : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · -- agreement on the point `4π - δ > 2π`
      exact h (4 * Real.pi - δ) (by linarith [hδpi, Real.pi_pos])
    · -- the point is different from `↑(4π)`
      simp only [Set.mem_singleton_iff]
      intro hcontra
      have h2 : 4 * Real.pi - δ = 4 * Real.pi := Complex.ofReal_injective hcontra
      linarith [hδpos]
    · -- and it is within distance `ε` of `↑(4π)`
      rw [Complex.dist_eq]
      have hsub : ((4 * Real.pi : ℝ) : ℂ) - (((4 * Real.pi - δ : ℝ)) : ℂ)
          = ((4 * Real.pi - (4 * Real.pi - δ) : ℝ) : ℂ) :=
        (Complex.ofReal_sub (4 * Real.pi) (4 * Real.pi - δ)).symm
      rw [hsub, Complex.norm_real, Real.norm_eq_abs]
      have h3 : |4 * Real.pi - (4 * Real.pi - δ)| = δ := by
        rw [show 4 * Real.pi - (4 * Real.pi - δ) = δ by ring, abs_of_pos hδpos]
      rw [h3]
      exact hδlt
  intro z hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hF hG hU h0 hfreq hz

end Work.CKFinal.LineDecay
