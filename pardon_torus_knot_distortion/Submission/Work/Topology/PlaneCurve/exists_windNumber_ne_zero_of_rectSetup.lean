import Mathlib
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy
import Submission.Work.Topology.PlaneCurve.windNumber_ne_zero_of_normalized

/-!
# A point of the imaginary axis with non-zero winding number (normalised rectangle setup)

For a continuous `2π`-periodic curve `γ : ℝ → ℂ` injective on one period, whose trace lies in the
open rectangle `rectR` apart from the two points `±1` which it contains, there is a point `z` of
the imaginary axis which is off the trace and whose winding number `windNumber γ hγ z` is
non-zero.

## Reduction

Everything geometric is done in `Work.Topology.PlaneCurve.windNumber_ne_zero_of_normalized`, the
same statement for a curve additionally normalised by `γ 0 = -1`.  Here we only transfer that
statement along a translation of the parameter: the loop `t ↦ γ (t + s) - z` is homotopic to
`t ↦ γ t - z` through the closed loops `t ↦ γ (2π t + u s) - z` (`u ∈ [0,1]`), all of which avoid
`0` as soon as `z ∉ range γ`, so the winding number is unchanged.
-/

namespace Work.Topology.PlaneCurve

open Set

/-- **Translating the parameter does not change the winding number.**  If `z` is off the trace of
`γ` then `windNumber γ z = windNumber (fun t => γ (t + s)) z`. -/
theorem windNumber_shift {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (s : ℝ) {z : ℂ} (hz : ∀ t : ℝ, γ t ≠ z) :
    Work.Smooth.SphereJordan.windNumber γ hγ z =
      Work.Smooth.SphereJordan.windNumber (fun t : ℝ => γ (t + s))
        (hγ.comp (continuous_id.add continuous_const)) z := by
  have hγs : Continuous fun t : ℝ => γ (t + s) := hγ.comp (continuous_id.add continuous_const)
  set c₀ : C(unitInterval, ℂ) := Work.Smooth.SphereJordan.curveLoop (fun t => γ t - z)
    (hγ.sub continuous_const) with hc₀
  set c₁ : C(unitInterval, ℂ) := Work.Smooth.SphereJordan.curveLoop (fun t => γ (t + s) - z)
    (hγs.sub continuous_const) with hc₁
  have hc₀_apply : ∀ t : unitInterval, c₀ t = γ (2 * Real.pi * (t : ℝ)) - z := fun t => rfl
  have hc₁_apply : ∀ t : unitInterval, c₁ t = γ (2 * Real.pi * (t : ℝ) + s) - z := fun t => rfl
  -- the homotopy of closed loops
  set H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => γ (2 * Real.pi * (p.1 : ℝ) + (p.2 : ℝ) * s) - z, by fun_prop⟩ with hH
  have hH_apply : ∀ p : unitInterval × unitInterval,
      H p = γ (2 * Real.pi * (p.1 : ℝ) + (p.2 : ℝ) * s) - z := fun p => rfl
  have hHne : ∀ p : unitInterval × unitInterval, H p ≠ 0 := by
    intro p
    rw [hH_apply]
    exact sub_ne_zero.mpr (hz _)
  have hH0 : ∀ t : unitInterval, H (t, 0) = c₀ t := by
    intro t
    rw [hH_apply, hc₀_apply]
    norm_num
  have hH1 : ∀ t : unitInterval, H (t, 1) = c₁ t := by
    intro t
    rw [hH_apply, hc₁_apply]
    norm_num
  have hHloop : ∀ u : unitInterval, H (0, u) = H (1, u) := by
    intro u
    rw [hH_apply, hH_apply]
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
    rw [h0, h1, zero_add]
    congr 1
    rw [add_comm (2 * Real.pi) ((u : ℝ) * s)]
    exact (hper ((u : ℝ) * s)).symm
  have hne0 : ∀ t : unitInterval, c₀ t ≠ 0 := by
    intro t; rw [hc₀_apply]; exact sub_ne_zero.mpr (hz _)
  have hne1 : ∀ t : unitInterval, c₁ t ≠ 0 := by
    intro t; rw [hc₁_apply]; exact sub_ne_zero.mpr (hz _)
  have hmain := Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy hne0 hne1 H hHne hH0 hH1 hHloop
  exact hmain

/-- **A point of the imaginary axis of non-zero winding number, in the rectangle setup.** -/
theorem exists_windNumber_ne_zero_of_rectSetup {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ t : ℝ, γ t ∈ Work.Topology.PlaneCurve.rectR ∨ γ t = -1 ∨ γ t = 1)
    (hm1 : ∃ t : ℝ, γ t = -1) (h1 : ∃ t : ℝ, γ t = 1) :
    ∃ z : ℂ, z.re = 0 ∧ (∀ t : ℝ, γ t ≠ z) ∧
      Work.Smooth.SphereJordan.windNumber γ hγ z ≠ 0 := by
  obtain ⟨s, hs⟩ := hm1
  set γ' : ℝ → ℂ := fun t => γ (t + s) with hγ'def
  have hγ' : Continuous γ' := hγ.comp (continuous_id.add continuous_const)
  have hper' : Function.Periodic γ' (2 * Real.pi) := by
    intro t
    show γ (t + 2 * Real.pi + s) = γ (t + s)
    rw [show t + 2 * Real.pi + s = (t + s) + 2 * Real.pi by ring, hper]
  have hsub' : ∀ w ∈ Set.range γ', w ∈ Work.Topology.PlaneCurve.rectR ∨ w = -1 ∨ w = 1 := by
    rintro w ⟨t, rfl⟩
    exact hsub (t + s)
  have hzero' : γ' 0 = -1 := by
    show γ (0 + s) = -1
    rw [zero_add]; exact hs
  obtain ⟨t1, ht1⟩ := h1
  have h1' : (1 : ℂ) ∈ Set.range γ' := ⟨t1 - s, by
    show γ (t1 - s + s) = 1
    rw [sub_add_cancel]; exact ht1⟩
  have hinj' : Set.InjOn γ' (Set.Ico 0 (2 * Real.pi)) := by
    intro u hu v hv huv
    have huv' : γ (u + s) = γ (v + s) := huv
    obtain ⟨k, hk⟩ :=
      Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hper hinj huv'
    have h2 : (k : ℝ) * (2 * Real.pi) = (u + s) - (v + s) := by linarith [hk]
    have h3 : |u - v| < 2 * Real.pi := by
      rw [abs_lt]
      exact ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
    have hk0 : k = 0 := by
      by_contra hkne
      have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hkne
      have h5 : 2 * Real.pi ≤ |(u + s) - (v + s)| := by
        rw [← h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        nlinarith [h4, Real.pi_pos]
      rw [show (u + s) - (v + s) = u - v by ring] at h5
      linarith
    rw [hk0] at h2
    simp only [Int.cast_zero, zero_mul] at h2
    linarith
  obtain ⟨z, hzre, hzne', hzw⟩ :=
    Work.Topology.PlaneCurve.windNumber_ne_zero_of_normalized hγ' hper' hinj' hsub' hzero' h1'
  refine ⟨z, hzre, ?_, ?_⟩
  · intro t ht
    exact hzne' (t - s) (by
      show γ (t - s + s) = z
      rw [sub_add_cancel]; exact ht)
  · have hzne : ∀ t : ℝ, γ t ≠ z := fun t ht => (by
      exact hzne' (t - s) (by show γ (t - s + s) = z; rw [sub_add_cancel]; exact ht))
    have hshift := Work.Topology.PlaneCurve.windNumber_shift hγ hper s hzne
    rw [hshift]
    exact hzw

end Work.Topology.PlaneCurve
