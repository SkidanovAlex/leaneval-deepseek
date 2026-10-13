/-
Copyright: work module for the Elgindi finite-time singularity project.

Curried partial derivatives as Fréchet derivatives, and smoothness of the curried
partial derivatives of a smooth two-variable function.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The `z`-partial derivative is the Fréchet derivative in the direction `(1,0)`. -/
theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv

/-- The `θ`-partial derivative is the Fréchet derivative in the direction `(0,1)`. -/
theorem pth_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  exact (h.hasFDerivAt.comp_hasDerivAt θ hcurve).deriv

theorem differentiableAt_curry_left {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    DifferentiableAt ℝ (fun z' => G z' θ) z := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).differentiableAt

theorem differentiableAt_curry_right {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  exact (h.hasFDerivAt.comp_hasDerivAt θ hcurve).differentiableAt

/-- The `z`-partial of a function smooth on an open set is smooth on that set. -/
theorem contDiffOn_uncurry_pz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (pz G)) V := by
  have hchain : ∀ p ∈ V, pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact pz_eq_fderiv ((h.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ⊤ (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ⊤) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ ⊤
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a function smooth on an open set is smooth on that set. -/
theorem contDiffOn_uncurry_pth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (pth G)) V := by
  have hchain : ∀ p ∈ V, pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact pth_eq_fderiv ((h.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ⊤ (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ⊤) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ ⊤
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- Smoothness of the curried partials and the identification with the Fréchet derivative,
packaged as a single statement. -/
theorem CurrySmooth (G : ℝ → ℝ → ℝ) (V : Set (ℝ × ℝ)) (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    (∀ p ∈ V, pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0)) ∧
    (∀ p ∈ V, pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1)) ∧
    ContDiffOn ℝ ⊤ (Function.uncurry (pz G)) V ∧
    ContDiffOn ℝ ⊤ (Function.uncurry (pth G)) V :=
  ⟨fun p hp => pz_eq_fderiv ((h.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds hp)),
   fun p hp => pth_eq_fderiv ((h.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds hp)),
   contDiffOn_uncurry_pz hV h, contDiffOn_uncurry_pth hV h⟩

end Work.Spaces
