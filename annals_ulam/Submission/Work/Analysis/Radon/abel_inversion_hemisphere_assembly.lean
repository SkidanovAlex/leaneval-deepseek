import Mathlib
import Submission.Work.Analysis.Abel.abel_inversion
import Submission.Work.Analysis.Radon.integrableOn_abel_kernel_singular
import Submission.Work.Analysis.Radon.deriv_integral_sq
import Submission.Work.Analysis.Radon.abel_inversion_hemisphere_proof

open MeasureTheory Filter
open scoped Interval Topology

namespace Commons.Analysis.Radon

/-- The outer Abel transform equals `(π/4) ∫_0^{u²} G(√t)/√t`. -/
lemma hemisphere_outer_eq_pi_quarter {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Icc (0:ℝ) 1))
    {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    (∫ c in (0:ℝ)..u, c * (∫ s in (0:ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)) /
        Real.sqrt (u ^ 2 - c ^ 2))
      = (Real.pi / 4) * ∫ t in (0:ℝ)..(u ^ 2), G (Real.sqrt t) / Real.sqrt t := by
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := hu.2
  let f : ℝ → ℝ := fun c => ∫ s in (0:ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)
  let h : ℝ → ℝ := fun t => G (Real.sqrt t) / Real.sqrt t
  have houter := hemisphere_outer_sqrt_substitution (f := f) u hu0
  have hpoint : ∀ x ∈ Set.uIcc (0:ℝ) (u ^ 2),
      f (Real.sqrt x) / Real.sqrt (u ^ 2 - x) =
        (1/2) * ((Real.sqrt (u ^ 2 - x))⁻¹ * (∫ t in (0:ℝ)..x, h t / Real.sqrt (x - t))) := by
    intro x hx
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ u ^ 2)] at hx
    by_cases hx0 : x = 0
    · subst x
      simp [f, h]
    · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hsub := hemisphere_inner_sqrt_substitution (G := G) (Real.sqrt x) (Real.sqrt_pos.2 hx_pos)
      have hsub' : (∫ s in (0:ℝ)..Real.sqrt x, G s / Real.sqrt (x - s ^ 2))
          = (1/2) * ∫ t in (0:ℝ)..x, (G (Real.sqrt t) / Real.sqrt t) / Real.sqrt (x - t) := by
        simpa [Real.sq_sqrt hx_pos.le] using hsub
      dsimp [f, h]
      rw [Real.sq_sqrt hx_pos.le]
      rw [hsub']
      ring
  have hcongr : (∫ x in (0:ℝ)..(u ^ 2), f (Real.sqrt x) / Real.sqrt (u ^ 2 - x))
      = (1/2) * ∫ x in (0:ℝ)..(u ^ 2),
          (Real.sqrt (u ^ 2 - x))⁻¹ * (∫ t in (0:ℝ)..x, h t / Real.sqrt (x - t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    exact hpoint x hx
  have hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (u ^ 2 - p.2))⁻¹ * h p.1 else 0)
      (Set.uIoc 0 (u ^ 2) ×ˢ Set.uIoc 0 (u ^ 2)) := by
    simpa [h] using integrableOn_abel_kernel_singular (G := G) (x := u ^ 2)
      (by positivity) (by nlinarith) hG
  have habel := Commons.Analysis.Abel.abel_self_convolution_of_integrable (g := h) (x := u ^ 2)
    (by positivity) hint
  have hdouble : (∫ x in (0:ℝ)..(u ^ 2),
        (Real.sqrt (u ^ 2 - x))⁻¹ * (∫ t in (0:ℝ)..x, h t / Real.sqrt (x - t)))
      = (∫ x in (0:ℝ)..(u ^ 2),
        (Real.sqrt (u ^ 2 - x))⁻¹ * (∫ t in (0:ℝ)..x, (Real.sqrt (x - t))⁻¹ * h t)) := by
    congr 1
    ext x
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  calc
    (∫ c in (0:ℝ)..u, c * (∫ s in (0:ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)) /
        Real.sqrt (u ^ 2 - c ^ 2))
        = (1/2) * ∫ x in (0:ℝ)..(u ^ 2), f (Real.sqrt x) / Real.sqrt (u ^ 2 - x) := houter
    _ = (1/2) * ((1/2) * ∫ x in (0:ℝ)..(u ^ 2),
          (Real.sqrt (u ^ 2 - x))⁻¹ * (∫ t in (0:ℝ)..x, h t / Real.sqrt (x - t))) := by
          rw [hcongr]
    _ = (1/4) * ∫ x in (0:ℝ)..(u ^ 2),
          (Real.sqrt (u ^ 2 - x))⁻¹ * (∫ t in (0:ℝ)..x, h t / Real.sqrt (x - t)) := by ring
    _ = (1/4) * (Real.pi * ∫ t in (0:ℝ)..(u ^ 2), h t) := by rw [hdouble, habel]
    _ = (Real.pi / 4) * ∫ t in (0:ℝ)..(u ^ 2), G (Real.sqrt t) / Real.sqrt t := by
          dsimp [h]
          ring

/-- **Inversion of the rotation-invariant spherical Radon transform (Abel form, `d = 3`).** -/
lemma abel_inversion_hemisphere_final {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Icc (0:ℝ) 1))
    {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    G u = (2 / Real.pi) * deriv (fun u : ℝ =>
      ∫ c in (0:ℝ)..u, c * (∫ s in (0:ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)) /
        Real.sqrt (u ^ 2 - c ^ 2)) u := by
  have hu0 : 0 < u := hu.1
  have hEq : (fun u : ℝ => ∫ c in (0:ℝ)..u,
        c * (∫ s in (0:ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)) /
          Real.sqrt (u ^ 2 - c ^ 2))
      =ᶠ[𝓝 u] (fun u : ℝ => (Real.pi / 4) *
        ∫ t in (0:ℝ)..(u ^ 2), G (Real.sqrt t) / Real.sqrt t) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    exact hemisphere_outer_eq_pi_quarter hG hv
  have hderiv_inner : HasDerivAt (fun u : ℝ =>
      ∫ t in (0:ℝ)..(u ^ 2), G (Real.sqrt t) / Real.sqrt t)
      (G u / u * (2 * u)) u := hasDerivAt_integral_sqrt_profile hG hu
  have hderiv : deriv (fun u : ℝ => ∫ c in (0:ℝ)..u,
        c * (∫ s in (0:ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)) /
          Real.sqrt (u ^ 2 - c ^ 2)) u
      = (Real.pi / 4) * (G u / u * (2 * u)) := by
    rw [hEq.deriv_eq]
    exact (hderiv_inner.const_mul (Real.pi / 4)).deriv
  rw [hderiv]
  field_simp [ne_of_gt hu0]
  ring

end Commons.Analysis.Radon
