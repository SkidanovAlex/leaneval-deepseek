import Mathlib
import Submission.Work.Analysis.Abel.abel_self_convolution

namespace Commons.Analysis.Radon

open MeasureTheory
open scoped Interval Topology

/-!
# The `d = 3` spherical-Radon inversion, reduced to the Abel bridge

The classical inversion of the rotation-invariant spherical Radon transform in dimension `3` is

`G u = (2/π) d/du ∫_0^u c f c / √(u² - c²) dc`, where `f c = ∫_0^c G s / √(c² - s²) ds`.

The proof is the standard two-step reduction to the Abel transform:

* with `h t = G (√t) / √t`, the inner transform is `f c = (1/2) ∫_0^{c²} h t / √(c²-t) dt`;
* the outer transform is `(1/2) ∫_0^{u²} f (√x) / √(u²-x) dx = (1/4) A (A h) (u²)`;
* the Abel self-convolution `A (A h) = π ∫ h` (proved in the commons as
  `Commons.Analysis.Abel.abel_self_convolution`) turns this into `(π/4) ∫_0^{u²} h`;
* differentiating gives `(π/2) G u`, hence the constant `2/π`.

The two `sqrt` substitutions are the remaining bookkeeping. -/

lemma hemisphere_inner_sqrt_substitution {G : ℝ → ℝ} (c : ℝ) (hc : 0 < c) :
    (∫ s in (0:ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2))
      = (1/2) * ∫ t in (0:ℝ)..(c ^ 2), (G (Real.sqrt t) / Real.sqrt t) / Real.sqrt (c ^ 2 - t) := by
  let g : ℝ → ℝ := fun u => G u / Real.sqrt (c ^ 2 - u ^ 2)
  let f' : ℝ → ℝ := fun t => 1 / (2 * Real.sqrt t)
  have hf : ContinuousOn Real.sqrt (Set.uIcc (0:ℝ) (c ^ 2)) := Real.continuous_sqrt.continuousOn
  have hff' : ∀ x ∈ Set.Ioo (min (0:ℝ) (c ^ 2)) (max (0:ℝ) (c ^ 2)),
      HasDerivAt Real.sqrt (f' x) x := by
    intro x hx
    have hmin : min (0:ℝ) (c ^ 2) = 0 := min_eq_left (by positivity)
    have hx' : 0 < x := by simpa [hmin] using hx.1
    have hxn : x ≠ 0 := ne_of_gt hx'
    simpa [f'] using Real.hasDerivAt_sqrt hxn
  have hf' : ∀ x ∈ Set.Ioo (min (0:ℝ) (c ^ 2)) (max (0:ℝ) (c ^ 2)), 0 ≤ f' x := by
    intro x hx
    have hmin : min (0:ℝ) (c ^ 2) = 0 := min_eq_left (by positivity)
    have hx' : 0 < x := by simpa [hmin] using hx.1
    dsimp [f']
    positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := Real.sqrt) (f' := f') (g := g) (a := (0:ℝ)) (b := c ^ 2) hf hff' hf'
  have hsqrt_c : Real.sqrt (c ^ 2) = c := Real.sqrt_sq hc.le
  have hsqrt_0 : Real.sqrt (0:ℝ) = 0 := Real.sqrt_zero
  rw [hsqrt_0, hsqrt_c] at hsub
  have hcongr : (∫ t in (0:ℝ)..(c ^ 2), (G (Real.sqrt t) / Real.sqrt t) / Real.sqrt (c ^ 2 - t))
      = 2 * ∫ t in (0:ℝ)..(c ^ 2), (g (Real.sqrt t)) * f' t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ c ^ 2)] at ht
    dsimp [g, f']
    by_cases ht0 : t = 0
    · subst t
      simp
    · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht_pos
      have htsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.1
      rw [htsq]
      field_simp [hsqrt_pos.ne']
  rw [← hsub]
  rw [hcongr]
  ring_nf
  rfl


lemma hemisphere_outer_sqrt_substitution {f : ℝ → ℝ} (u : ℝ) (hu : 0 < u) :
    (∫ c in (0:ℝ)..u, c * f c / Real.sqrt (u ^ 2 - c ^ 2))
      = (1/2) * ∫ x in (0:ℝ)..(u ^ 2), f (Real.sqrt x) / Real.sqrt (u ^ 2 - x) := by
  let g : ℝ → ℝ := fun c => c * f c / Real.sqrt (u ^ 2 - c ^ 2)
  let f' : ℝ → ℝ := fun x => 1 / (2 * Real.sqrt x)
  have hf : ContinuousOn Real.sqrt (Set.uIcc (0:ℝ) (u ^ 2)) := Real.continuous_sqrt.continuousOn
  have hff' : ∀ x ∈ Set.Ioo (min (0:ℝ) (u ^ 2)) (max (0:ℝ) (u ^ 2)),
      HasDerivAt Real.sqrt (f' x) x := by
    intro x hx
    have hmin : min (0:ℝ) (u ^ 2) = 0 := min_eq_left (by positivity)
    have hx' : 0 < x := by simpa [hmin] using hx.1
    have hxn : x ≠ 0 := ne_of_gt hx'
    simpa [f'] using Real.hasDerivAt_sqrt hxn
  have hf' : ∀ x ∈ Set.Ioo (min (0:ℝ) (u ^ 2)) (max (0:ℝ) (u ^ 2)), 0 ≤ f' x := by
    intro x hx
    have hmin : min (0:ℝ) (u ^ 2) = 0 := min_eq_left (by positivity)
    have hx' : 0 < x := by simpa [hmin] using hx.1
    dsimp [f']
    positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := Real.sqrt) (f' := f') (g := g) (a := (0:ℝ)) (b := u ^ 2) hf hff' hf'
  have hsqrt_u : Real.sqrt (u ^ 2) = u := Real.sqrt_sq hu.le
  have hsqrt_0 : Real.sqrt (0:ℝ) = 0 := Real.sqrt_zero
  rw [hsqrt_0, hsqrt_u] at hsub
  -- hsub : ∫ x in 0..u², (g ∘ sqrt) x * f' x = ∫ c in 0..u, g c
  rw [← hsub]
  have hcongr : (∫ x in (0:ℝ)..(u ^ 2), f (Real.sqrt x) / Real.sqrt (u ^ 2 - x))
      = 2 * ∫ x in (0:ℝ)..(u ^ 2), (g (Real.sqrt x)) * f' x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hxmem
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ u ^ 2)] at hxmem
    have hx_pos : 0 < x := hxmem.1
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
    have hxsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_pos.le
    dsimp [g, f']
    rw [hxsq]
    field_simp [hsqrt_pos.ne']
  rw [hcongr]
  ring_nf
  rfl


end Commons.Analysis.Radon
