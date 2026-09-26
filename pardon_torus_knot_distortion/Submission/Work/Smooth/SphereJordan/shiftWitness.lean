import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy
import Submission.Work.Smooth.SphereJordan.loopIndex_shift_ne_zero

/-!
# The shifted chord witness

This is the general-`θ` form of `windNumber_eq_loopIndex_chord_of_avoids_rays`: for a curve `γ` whose
*shifted* chord loop `t ↦ γ t - γ (t + θ)` never vanishes, any point `z` off all the shifted chord
rays `{γ t + μ (γ t - γ (t + θ)) : μ ≥ 0}` has winding number about `z` equal to the index of the
shifted chord loop.

The shift matters: at `θ = π` the outward chord rays can sweep the whole bounded component (the
two-turn spiral band of `JORDAN_NOTES.md`), while for small `θ` the rays are close to the tangent
rays and leave uncovered points.  Since `loopIndex_shift_ne_zero` shows that *every* shifted chord
loop of a Jordan curve is essential, any certificate of this shape yields a point with non-zero
winding number.
-/

noncomputable section

open Set
open Classical

namespace Work.Smooth.SphereJordan

/-- **The shifted chord witness.**  A point off all the `θ`-shifted chord rays has winding number
equal to the index of the shifted chord loop. -/
theorem windNumber_eq_loopIndex_shift_of_avoids_rays {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z : ℂ} {θ : ℝ}
    (hβ : ∀ t : ℝ, γ t ≠ γ (t + θ)) (hz : ∀ t : ℝ, γ t ≠ z)
    (hav : ∀ (t : ℝ) (μ : ℝ), 0 ≤ μ → z ≠ γ t + μ * (γ t - γ (t + θ))) :
    windNumber γ hγ z
      = loopIndex (curveLoop (fun t => γ t - γ (t + θ))
          (hγ.sub (hγ.comp (continuous_id.add continuous_const)))) := by
  have hcont : Continuous fun t : ℝ => γ t - γ (t + θ) :=
    hγ.sub (hγ.comp (continuous_id.add continuous_const))
  -- `hav` restated for the ray out of `γ (t + θ)`, the form produced by the homotopy
  have hav' : ∀ (t : ℝ) (τ : ℝ), 1 ≤ τ → z ≠ γ (t + θ) + τ * (γ t - γ (t + θ)) := by
    intro t τ hτ
    have hkey : γ (t + θ) + τ * (γ t - γ (t + θ))
        = γ t + (((τ - 1 : ℝ)) : ℂ) * (γ t - γ (t + θ)) := by push_cast; ring
    rw [hkey]
    exact hav t (τ - 1) (by linarith)
  set c₀ : C(unitInterval, ℂ) := curveLoop (fun t => γ t - γ (t + θ)) hcont with hc0
  set c₁ : C(unitInterval, ℂ) := curveLoop (fun t => γ t - z) (hγ.sub continuous_const) with hc1
  have h₀ : ∀ t : unitInterval, c₀ t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + θ) ≠ 0
    intro h
    exact hβ _ (sub_eq_zero.mp h)
  have h₁ : ∀ t : unitInterval, c₁ t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - z ≠ 0
    exact sub_ne_zero.mpr (hz _)
  set H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => γ (2 * Real.pi * (p.1 : ℝ))
        - ((1 - (p.2 : ℝ)) * γ (2 * Real.pi * (p.1 : ℝ) + θ) + (p.2 : ℝ) * z),
      by fun_prop⟩ with hH
  have hHne : ∀ p, H p ≠ 0 := by
    rintro ⟨t, s⟩
    show γ (2 * Real.pi * (t : ℝ))
      - ((1 - (s : ℝ)) * γ (2 * Real.pi * (t : ℝ) + θ) + (s : ℝ) * z) ≠ 0
    intro h0
    have h1 : γ (2 * Real.pi * (t : ℝ))
        = (1 - (s : ℝ)) * γ (2 * Real.pi * (t : ℝ) + θ) + (s : ℝ) * z :=
      sub_eq_zero.mp h0
    rcases eq_or_lt_of_le s.2.1 with hs | hs
    · rw [← hs] at h1
      have h2 : γ (2 * Real.pi * (t : ℝ)) = γ (2 * Real.pi * (t : ℝ) + θ) := by
        rw [h1]
        push_cast
        ring
      exact hβ _ h2
    · have hsne : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs : (s : ℝ) ≠ 0)
      have hz' : z = γ (2 * Real.pi * (t : ℝ) + θ)
          + (((s : ℝ)⁻¹ : ℝ) : ℂ)
            * (γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + θ)) := by
        rw [Complex.ofReal_inv, h1]
        field_simp
        ring_nf
      exact hav' _ _ (one_le_inv₀ hs |>.mpr s.2.2) hz'
  have hH0 : ∀ t : unitInterval, H (t, 0) = c₀ t := by
    intro t
    show γ (2 * Real.pi * (t : ℝ))
      - ((1 - ((0 : unitInterval) : ℝ)) * γ (2 * Real.pi * (t : ℝ) + θ)
        + ((0 : unitInterval) : ℝ) * z)
      = γ (2 * Real.pi * (t : ℝ)) - γ (2 * Real.pi * (t : ℝ) + θ)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
    push_cast
    ring
  have hH1 : ∀ t : unitInterval, H (t, 1) = c₁ t := by
    intro t
    show γ (2 * Real.pi * (t : ℝ))
      - ((1 - ((1 : unitInterval) : ℝ)) * γ (2 * Real.pi * (t : ℝ) + θ)
        + ((1 : unitInterval) : ℝ) * z)
      = γ (2 * Real.pi * (t : ℝ)) - z
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    push_cast
    ring
  have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
    intro s
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ))
      - ((1 - (s : ℝ)) * γ (2 * Real.pi * ((0 : unitInterval) : ℝ) + θ) + (s : ℝ) * z)
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ))
      - ((1 - (s : ℝ)) * γ (2 * Real.pi * ((1 : unitInterval) : ℝ) + θ) + (s : ℝ) * z)
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero]
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one]
    have hb : γ (2 * Real.pi * ((0 : unitInterval) : ℝ))
        = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) := by
      rw [h0, h1]
      simpa only [zero_add] using (hper 0).symm
    have ha : γ (2 * Real.pi * ((0 : unitInterval) : ℝ) + θ)
        = γ (2 * Real.pi * ((1 : unitInterval) : ℝ) + θ) := by
      rw [h0, h1]
      have h := hper θ
      rw [show θ + 2 * Real.pi = 2 * Real.pi + θ by ring] at h
      rw [zero_add]
      exact h.symm
    rw [hb, ha]
  have key : loopIndex c₀ = loopIndex c₁ := loopIndex_eq_of_homotopy h₀ h₁ H hHne hH0 hH1 hHloop
  have hc0' : loopIndex c₀ = loopIndex (curveLoop (fun t => γ t - γ (t + θ)) hcont) := rfl
  have hc1' : loopIndex c₁ = windNumber γ hγ z := rfl
  rw [← hc1', ← hc0']
  exact key.symm

/-- **Any shifted certificate yields a point of non-zero winding number.**

`loopIndex_shift_ne_zero` says every shifted chord loop of a Jordan curve is essential, so the
equality of `windNumber_eq_loopIndex_shift_of_avoids_rays` immediately gives non-vanishing. -/
theorem windNumber_ne_zero_of_off_shifted_rays {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {z : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hβ : ∀ t : ℝ, γ t ≠ γ (t + θ)) (hz : ∀ t : ℝ, γ t ≠ z)
    (hav : ∀ (t : ℝ) (μ : ℝ), 0 ≤ μ → z ≠ γ t + μ * (γ t - γ (t + θ))) :
    windNumber γ hγ z ≠ 0 := by
  rw [windNumber_eq_loopIndex_shift_of_avoids_rays hγ hper hβ hz hav]
  exact Work.Smooth.SphereJordan.loopIndex_shift_ne_zero hγ hper hinj hθ0 hθ2

/-- **The witness, from a shifted certificate.**

Given a point `z` off all the `θ`-shifted chord rays (for some `0 < θ < 2π` for which the shifted
chord loop is known to be nowhere vanishing), the winding number of `γ` about `z` is non-zero.
This reduces the existence of a point of non-zero winding number for a plane Jordan curve to the
geometric existence of such a certificate. -/
theorem exists_windNumber_ne_zero_of_shifted_certificate {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hcert : ∃ (z : ℂ) (θ : ℝ), 0 < θ ∧ θ < 2 * Real.pi ∧ (∀ t : ℝ, γ t ≠ γ (t + θ)) ∧
      ∀ (t : ℝ) (μ : ℝ), 0 ≤ μ → z ≠ γ t + μ * (γ t - γ (t + θ))) :
    ∃ z : ℂ, (∀ t : ℝ, γ t ≠ z) ∧ windNumber γ hγ z ≠ 0 := by
  obtain ⟨z, θ, hθ0, hθ2, hβ, hav⟩ := hcert
  have hz : ∀ t : ℝ, γ t ≠ z := fun t h =>
    hav t 0 le_rfl (by simpa [h] using h.symm)
  exact ⟨z, hz, windNumber_ne_zero_of_off_shifted_rays hγ hper hinj hθ0 hθ2 hβ hz hav⟩

end Work.Smooth.SphereJordan
