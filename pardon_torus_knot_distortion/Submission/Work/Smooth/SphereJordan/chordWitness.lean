import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The chord witness: a point off all chord rays has winding number equal to the chord index

Let `γ : ℝ → ℂ` be a continuous `2π`-periodic curve whose chord loop `t ↦ γ t - γ (t + π)` never
vanishes, and let `z ∉ γ`.  If `z` is not on any of the *outward chord rays*

`R t = {γ t + μ (γ t - γ (t + π)) : μ ≥ 0}`,

then the straight-line homotopy `H (t,s) = γ (2πt) - ((1-s) γ (2πt+π) + s z)` avoids `0`, so by
homotopy invariance of the index (`loopIndex_eq_of_homotopy`) the winding number of `γ` about `z`
equals the index of the chord loop.  Combined with `windNumber_ne_zero_of_antiperiodic` applied to
the chord curve (which is anti-periodic), this reduces the "at least two components" step of the
Jordan curve theorem to the geometric existence of a point off all outward chord rays.
-/

noncomputable section

open Set
open Classical

namespace Work.Smooth.SphereJordan

/-- **The chord witness.**  A point off all the outward chord rays has winding number equal to the
index of the chord loop. -/
theorem windNumber_eq_loopIndex_chord_of_avoids_rays {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z : ℂ} (hβ : ∀ t : ℝ, γ t ≠ γ (t + Real.pi))
    (hz : ∀ t : ℝ, γ t ≠ z)
    (hav : ∀ (t : ℝ) (μ : ℝ), 0 ≤ μ → z ≠ γ t + μ * (γ t - γ (t + Real.pi))) :
    windNumber γ hγ z
      = loopIndex (curveLoop (fun t => γ t - γ (t + Real.pi))
          (hγ.sub (hγ.comp (continuous_id.add continuous_const)))) := by
  have hcont : Continuous fun t : ℝ => γ t - γ (t + Real.pi) :=
    hγ.sub (hγ.comp (continuous_id.add continuous_const))
  -- `hav` restated for the ray out of `γ (t + π)`, which is the form produced by the homotopy
  have hav' : ∀ (t : ℝ) (τ : ℝ), 1 ≤ τ → z ≠ γ (t + Real.pi) + τ * (γ t - γ (t + Real.pi)) := by
    intro t τ hτ
    have hkey : γ (t + Real.pi) + τ * (γ t - γ (t + Real.pi))
        = γ t + (((τ - 1 : ℝ)) : ℂ) * (γ t - γ (t + Real.pi)) := by push_cast; ring
    rw [hkey]
    exact hav t (τ - 1) (by linarith)
  set c₀ : C(unitInterval, ℂ) := curveLoop (fun t => γ t - γ (t + Real.pi)) hcont with hc0
  set c₁ : C(unitInterval, ℂ) := curveLoop (fun t => γ t - z) (hγ.sub continuous_const) with hc1
  have h₀ : ∀ t : unitInterval, c₀ t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + Real.pi) ≠ 0
    intro h
    exact hβ _ (sub_eq_zero.mp h)
  have h₁ : ∀ t : unitInterval, c₁ t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - z ≠ 0
    exact sub_ne_zero.mpr (hz _)
  set H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => γ (2 * Real.pi * (p.1 : ℝ))
        - ((1 - (p.2 : ℝ)) * γ (2 * Real.pi * (p.1 : ℝ) + Real.pi) + (p.2 : ℝ) * z),
      by fun_prop⟩ with hH
  have hHne : ∀ p, H p ≠ 0 := by
    rintro ⟨t, s⟩
    show γ (2 * Real.pi * (t : ℝ))
      - ((1 - (s : ℝ)) * γ (2 * Real.pi * (t : ℝ) + Real.pi) + (s : ℝ) * z) ≠ 0
    intro h0
    have h1 : γ (2 * Real.pi * (t : ℝ))
        = (1 - (s : ℝ)) * γ (2 * Real.pi * (t : ℝ) + Real.pi) + (s : ℝ) * z :=
      sub_eq_zero.mp h0
    rcases eq_or_lt_of_le s.2.1 with hs | hs
    · rw [← hs] at h1
      have h2 : γ (2 * Real.pi * (t : ℝ)) = γ (2 * Real.pi * (t : ℝ) + Real.pi) := by
        rw [h1]
        push_cast
        ring
      exact hβ _ h2
    · have hz' : z = γ (2 * Real.pi * (t : ℝ) + Real.pi)
          + (((s : ℝ)⁻¹ : ℝ) : ℂ)
            * (γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + Real.pi)) := by
        have hsne : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs : (s : ℝ) ≠ 0)
        rw [Complex.ofReal_inv, h1]
        field_simp
        ring_nf
      exact hav' _ _ (one_le_inv₀ hs |>.mpr s.2.2) hz'
  have hH0 : ∀ t : unitInterval, H (t, 0) = c₀ t := by
    intro t
    show γ (2 * Real.pi * (t : ℝ))
      - ((1 - ((0 : unitInterval) : ℝ)) * γ (2 * Real.pi * (t : ℝ) + Real.pi)
        + ((0 : unitInterval) : ℝ) * z)
      = γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + Real.pi)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
    push_cast
    ring
  have hH1 : ∀ t : unitInterval, H (t, 1) = c₁ t := by
    intro t
    show γ (2 * Real.pi * (t : ℝ))
      - ((1 - ((1 : unitInterval) : ℝ)) * γ (2 * Real.pi * (t : ℝ) + Real.pi)
        + ((1 : unitInterval) : ℝ) * z)
      = γ (2 * Real.pi * (t : ℝ)) - z
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    push_cast
    ring
  have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
    intro s
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ))
      - ((1 - (s : ℝ)) * γ (2 * Real.pi * ((0 : unitInterval) : ℝ) + Real.pi) + (s : ℝ) * z)
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ))
      - ((1 - (s : ℝ)) * γ (2 * Real.pi * ((1 : unitInterval) : ℝ) + Real.pi) + (s : ℝ) * z)
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero]
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one]
    have hb : γ (2 * Real.pi * ((0 : unitInterval) : ℝ))
        = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) := by
      rw [h0, h1]
      simpa only [zero_add] using (hper 0).symm
    have ha : γ (2 * Real.pi * ((0 : unitInterval) : ℝ) + Real.pi)
        = γ (2 * Real.pi * ((1 : unitInterval) : ℝ) + Real.pi) := by
      rw [h0, h1]
      have h := hper Real.pi
      rw [show Real.pi + 2 * Real.pi = 2 * Real.pi + Real.pi by ring] at h
      rw [zero_add]
      exact h.symm
    rw [hb, ha]
  have key : loopIndex c₀ = loopIndex c₁ := loopIndex_eq_of_homotopy h₀ h₁ H hHne hH0 hH1 hHloop
  have hc0' : loopIndex c₀ = loopIndex (curveLoop (fun t => γ t - γ (t + Real.pi)) hcont) := rfl
  have hc1' : loopIndex c₁ = windNumber γ hγ z := rfl
  rw [← hc1', ← hc0']
  exact key.symm

end Work.Smooth.SphereJordan
