import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongPersist

theorem hasDerivAt_wip_family (ρ : Work.FTS.Galerkin.Fn) (u v : ℝ → Work.FTS.Galerkin.Fn)
    (udot vdot : Work.FTS.Galerkin.Fn) (bound : ℝ × ℝ → ℝ) {τ : ℝ} {U : Set ℝ}
    (hU : U ∈ nhds τ)
    (hmeas : ∀ᶠ s in nhds τ, MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u τ p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hint₁ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => udot p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hint₂ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u τ p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => udot p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2
        + u τ p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hbound : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ∀ s ∈ U, ‖udot p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2
        + u s p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2‖ ≤ bound p)
    (hboundint : MeasureTheory.Integrable bound
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hderiv : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ∀ s ∈ U, HasDerivAt (fun t => u t p.1 p.2 * v t p.1 p.2 * ρ p.1 p.2)
        (udot p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2
          + u s p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2) s) :
    HasDerivAt (fun s => Work.Coercivity.wip ρ (u s) (v s))
      (Work.Coercivity.wip ρ udot (v τ) + Work.Coercivity.wip ρ (u τ) vdot) τ := by
  -- Differentiate under the integral sign on the quadrant, viewed as the product of the two
  -- restricted one-dimensional measures.
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (F := fun s (p : ℝ × ℝ) => u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2)
    (F' := fun s (p : ℝ × ℝ) => udot p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2
      + u s p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2)
    (bound := bound) (s := U) (x₀ := τ) hU hmeas hint hmeas' hbound hboundint hderiv
  obtain ⟨hF'int, hderiv_int⟩ := hmain
  -- Any parameter `s` in a sufficiently small ball around `τ` gives an integrable integrand:
  -- the mean value theorem turns the uniform derivative bound into a bound on the integrand
  -- itself, and the value at `τ` is integrable by hypothesis.
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hτmem : τ ∈ Metric.ball τ ε := Metric.mem_ball_self hε
  have key : ∀ s ∈ Metric.ball τ ε,
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) →
      MeasureTheory.Integrable
        (fun p : ℝ × ℝ => u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    intro s hs hms
    have hMVT : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        ‖u τ p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2
          - u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2‖ ≤ bound p * ‖s - τ‖ := by
      filter_upwards [hderiv, hbound] with p hd hb
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := Metric.ball τ ε)
        (f := fun t => u t p.1 p.2 * v t p.1 p.2 * ρ p.1 p.2)
        (f' := fun t => udot p.1 p.2 * v t p.1 p.2 * ρ p.1 p.2
          + u t p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2)
        (C := bound p)
        (fun x hx => (hd x (hεU hx)).hasDerivWithinAt)
        (fun x hx => hb x (hεU hx))
        (convex_ball τ ε) hτmem hs
      calc ‖u τ p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2
            - u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2‖
          = ‖u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2
            - u τ p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2‖ := norm_sub_rev _ _
        _ ≤ bound p * ‖s - τ‖ := hmvt
    exact integrable_of_norm_sub_le hms hint (hboundint.mul_const _) hMVT
  -- Fubini: near `τ` the iterated integral `wip` is the integral against the product measure.
  have hA : Work.Coercivity.wip ρ udot (v τ)
      = ∫ p : ℝ × ℝ, udot p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip]
    exact MeasureTheory.integral_integral hint₁
  have hB : Work.Coercivity.wip ρ (u τ) vdot
      = ∫ p : ℝ × ℝ, u τ p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip]
    exact MeasureTheory.integral_integral hint₂
  have hFub : ∀ᶠ s in nhds τ,
      Work.Coercivity.wip ρ (u s) (v s)
        = ∫ p : ℝ × ℝ, u s p.1 p.2 * v s p.1 p.2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    filter_upwards [hmeas, Metric.ball_mem_nhds τ hε] with s hms hs
    have hFs := key s hs hms
    rw [Work.Coercivity.wip]
    exact MeasureTheory.integral_integral hFs
  have hcongr := hderiv_int.congr_of_eventuallyEq hFub
  have hval : (∫ p : ℝ × ℝ, udot p.1 p.2 * v τ p.1 p.2 * ρ p.1 p.2
        + u τ p.1 p.2 * vdot p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = Work.Coercivity.wip ρ udot (v τ) + Work.Coercivity.wip ρ (u τ) vdot := by
    rw [MeasureTheory.integral_add hint₁ hint₂, ← hA, ← hB]
  rw [hval] at hcongr
  exact hcongr

end Work.FTS.StrongPersist
