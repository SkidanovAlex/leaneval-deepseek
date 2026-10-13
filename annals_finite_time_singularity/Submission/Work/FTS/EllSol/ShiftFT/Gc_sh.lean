import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The shifted operator applied to the truncation `Gc`

`Work.FTS.EllSol.ShiftFT.Gc N b u` is the particular solution of the shifted equation
`L_b G = chi N · (L_b u)`, where `L_b u = ∂_t u - b·u` and `chi N` is the smooth cutoff of
`Work.FTS.EllSol.Trunc`.  This file verifies the defining identity in the first variable:

`∂_t (Gc N b u) - b·(Gc N b u) = chi N t · (∂_t u - b·u)`.

It is a direct instance of the fundamental theorem of calculus: with
`Gc N b u t θ = chi N t · u t θ + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds`
the derivative of the integral is `- e^{-bt} (chi N)'(t) u t θ`, whose product with the
prefactor `e^{bt}` cancels the `(chi N)'`-term produced by the product rule; what survives is
exactly `chi N t · (∂_t u - b·u)` together with the `b·e^{bt}·∫`-term which cancels against the
`b·Gc` on the left.
-/

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

theorem Gc_sh (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ
        - b * Work.FTS.EllSol.ShiftFT.Gc N b u t θ
      = Work.FTS.EllSol.Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ) := by
  intro t θ hθ
  -- smoothness of the cutoff and its derivative
  have hchi2 : ContDiff ℝ 2 (Work.FTS.EllSol.Trunc.chi N) :=
    Work.FTS.EllSol.Trunc.chi_contDiff 2 N
  have hchiD : DifferentiableAt ℝ (Work.FTS.EllSol.Trunc.chi N) t :=
    hchi2.differentiable (by norm_num) t
  have hchic : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    hchi2.continuous_deriv (by norm_num)
  -- the `θ`-slice of `u` is `C²` on `ℝ`, hence differentiable and continuous
  have hmap : Set.MapsTo (fun s : ℝ => (s, θ)) Set.univ
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
  have hpair : ContDiffOn ℝ 2 (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  have hslice : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) Set.univ := by
    have h := hu.comp hpair hmap
    simpa [Function.comp_def, Function.uncurry] using h
  have hsliceDiff : DifferentiableAt ℝ (fun s : ℝ => u s θ) t :=
    (hslice.differentiableOn (by norm_num)).differentiableAt (by simp)
  have hsliceC : Continuous (fun s : ℝ => u s θ) := continuousOn_univ.mp hslice.continuousOn
  have hslice_deriv : HasDerivAt (fun s : ℝ => u s θ) (deriv (fun s : ℝ => u s θ) t) t :=
    hsliceDiff.hasDerivAt
  -- product rule for the cutoff term
  have hFd : HasDerivAt (fun s : ℝ => Work.FTS.EllSol.Trunc.chi N s * u s θ)
      (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
        + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t) t :=
    hchiD.hasDerivAt.mul hslice_deriv
  -- the exponential prefactor
  have hexpD : HasDerivAt (fun s : ℝ => Real.exp (b * s)) (b * Real.exp (b * t)) t := by
    have h : HasDerivAt (fun s : ℝ => b * s) b t := by
      have h' := (hasDerivAt_id t).const_mul b
      simpa using h'
    simpa [mul_comm] using h.exp
  -- continuity of the integrand
  have hint_cont : Continuous (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
    have h1 : Continuous (fun s : ℝ => Real.exp (-(b * s))) := by fun_prop
    exact (h1.mul hchic).mul hsliceC
  -- fundamental theorem of calculus for the lower limit
  have hH : HasDerivAt (fun v : ℝ => ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      (-(Real.exp (-(b * t)) * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)) t :=
    intervalIntegral.integral_hasDerivAt_left (hint_cont.intervalIntegrable t (2 * N))
      (hint_cont.stronglyMeasurableAtFilter volume (𝓝 t)) hint_cont.continuousAt
  have hEHd : HasDerivAt (fun v : ℝ => Real.exp (b * v) * ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      (b * Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
        + Real.exp (b * t) * (-(Real.exp (-(b * t))
            * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ))) t :=
    hexpD.mul hH
  have hsumd : HasDerivAt (fun v : ℝ => Work.FTS.EllSol.Trunc.chi N v * u v θ
        + Real.exp (b * v) * ∫ s in v..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      ((deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t)
        + (b * Real.exp (b * t) * (∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
          + Real.exp (b * t) * (-(Real.exp (-(b * t))
              * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)))) t :=
    hFd.add hEHd
  have hderiv : deriv (fun v : ℝ => Gc N b u v θ) t
      = (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t)
        + (b * Real.exp (b * t) * (∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
          + Real.exp (b * t) * (-(Real.exp (-(b * t))
              * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ))) := hsumd.deriv
  have hGct : Gc N b u t θ = Work.FTS.EllSol.Trunc.chi N t * u t θ
      + Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := rfl
  have hexpneg : Real.exp (b * t) * Real.exp (-(b * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  change deriv (fun v : ℝ => Gc N b u v θ) t - b * Gc N b u t θ
      = Work.FTS.EllSol.Trunc.chi N t * (deriv (fun s : ℝ => u s θ) t - b * u t θ)
  rw [hderiv, hGct]
  linear_combination (-(deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)) * hexpneg

end Work.FTS.EllSol.ShiftFT
