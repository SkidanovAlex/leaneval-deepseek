import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.Gc_sh
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcJHasDeriv
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcSliceData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

theorem gcDeriv (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Gc N b u) t θ
        = Work.FTS.EllSol.Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ) + b * Gc N b u t θ)
    ∧ (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.Spaces.pz (Gc N b u)) t θ
        = deriv (Work.FTS.EllSol.Trunc.chi N) t * Work.Spaces.pz u t θ
          + Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pz (Work.Spaces.pz u) t θ
          + b ^ 2 * Gc N b u t θ - b ^ 2 * Work.FTS.EllSol.Trunc.chi N t * u t θ
          - b * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s => Gc N b u s θ))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s => Work.Spaces.pz (Gc N b u) s θ)) := by
  -- the `t`-slices of `u` and of `∂_t u` are differentiable everywhere
  have hsliceDAt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      DifferentiableAt ℝ (fun s : ℝ => u s θ) t :=
    fun θ hθ t => ((gcSliceData u hu).1 θ hθ).differentiableAt
  have hpzSliceDAt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.pz u s θ) t :=
    fun θ hθ t => ((gcSliceData u hu).2 θ hθ).differentiableAt
  -- the fundamental theorem of calculus for the lower limit of the integral in `Gc`
  have hJd := gcJHasDeriv N b u hu
  -- the derivative of the exponential-times-integral factor
  have hFHas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Real.exp (b * s) * ∫ y in s..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
        (b * (Real.exp (b * t) * ∫ y in t..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
          - deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ) t := by
    intro θ hθ t
    have hexpD : HasDerivAt (fun s : ℝ => Real.exp (b * s)) (b * Real.exp (b * t)) t := by
      have h : HasDerivAt (fun s : ℝ => b * s) b t := by
        simpa using (hasDerivAt_id t).const_mul b
      simpa [mul_comm] using h.exp
    have hmain := hexpD.mul (hJd θ hθ t)
    refine hmain.congr_deriv ?_
    have hee : Real.exp (b * t) * Real.exp (-(b * t)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [show Real.exp (b * t)
          * (-(Real.exp (-(b * t)) * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ))
        = -(Real.exp (b * t) * Real.exp (-(b * t)))
            * (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ) from by ring]
    rw [hee]
    ring
  -- the pointwise identity `∂_t (Gc) = χ·∂_t u + b·e^{bt}∫…` (from `Gc_sh`)
  have hE1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ s : ℝ,
      Work.Spaces.pz (Gc N b u) s θ
        = Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ
          + b * (Real.exp (b * s) * ∫ y in s..(2 * N),
              Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ) := by
    intro θ hθ s
    have h := Gc_sh N b u hu s θ hθ
    have hG : Gc N b u s θ = Work.FTS.EllSol.Trunc.chi N s * u s θ
        + Real.exp (b * s) * ∫ y in s..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ := rfl
    rw [hG] at h
    linear_combination h
  -- the derivative of the `t`-slice of `Gc`
  have hGHas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Gc N b u s θ)
        (Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pz u t θ
          + b * (Real.exp (b * t) * ∫ y in t..(2 * N),
              Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)) t := by
    intro θ hθ t
    have hchiD : DifferentiableAt ℝ (Work.FTS.EllSol.Trunc.chi N) t :=
      (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable (by norm_num) t
    have h1 : HasDerivAt (fun s : ℝ => Work.FTS.EllSol.Trunc.chi N s * u s θ)
        (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t) t :=
      hchiD.hasDerivAt.mul (hsliceDAt θ hθ t).hasDerivAt
    have hsum := h1.add (hFHas θ hθ t)
    refine hsum.congr_deriv ?_
    rw [show deriv (fun s : ℝ => u s θ) t = Work.Spaces.pz u t θ from rfl]
    ring
  -- the derivative of the `t`-slice of `∂_t Gc`
  have hPzHas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Work.Spaces.pz (Gc N b u) s θ)
        (deriv (Work.FTS.EllSol.Trunc.chi N) t * Work.Spaces.pz u t θ
          + Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pz (Work.Spaces.pz u) t θ
          + b ^ 2 * Gc N b u t θ - b ^ 2 * Work.FTS.EllSol.Trunc.chi N t * u t θ
          - b * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ) t := by
    intro θ hθ t
    have hchiD : DifferentiableAt ℝ (Work.FTS.EllSol.Trunc.chi N) t :=
      (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable (by norm_num) t
    have h1 : HasDerivAt (fun s : ℝ =>
          Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ)
        (deriv (Work.FTS.EllSol.Trunc.chi N) t * Work.Spaces.pz u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => Work.Spaces.pz u s θ) t) t :=
      hchiD.hasDerivAt.mul (hpzSliceDAt θ hθ t).hasDerivAt
    have hsum := h1.add ((hFHas θ hθ t).const_mul b)
    have heq : (fun s : ℝ => Work.Spaces.pz (Gc N b u) s θ)
        =ᶠ[𝓝 t] ((fun s : ℝ => Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ)
            + fun y : ℝ => b * (Real.exp (b * y) * ∫ x in y..(2 * N),
                Real.exp (-(b * x)) * deriv (Work.FTS.EllSol.Trunc.chi N) x * u x θ)) := by
      filter_upwards with s
      exact hE1 θ hθ s
    refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [show deriv (fun s : ℝ => Work.Spaces.pz u s θ) t
        = Work.Spaces.pz (Work.Spaces.pz u) t θ from rfl]
    rw [show Gc N b u t θ = Work.FTS.EllSol.Trunc.chi N t * u t θ
        + Real.exp (b * t) * ∫ y in t..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ from rfl]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the first-order identity
    intro t θ hθ
    have h := Gc_sh N b u hu t θ hθ
    linear_combination h
  · -- the second-order identity
    intro t θ hθ
    exact (hPzHas θ hθ t).deriv
  · -- differentiability of the `t`-slice of `Gc`
    intro θ hθ t
    exact (hGHas θ hθ t).differentiableAt
  · -- differentiability of the `t`-slice of `∂_t Gc`
    intro θ hθ t
    exact (hPzHas θ hθ t).differentiableAt

end

end Work.FTS.EllSol.ShiftFT.Aux2
