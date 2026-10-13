/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `C^∞` (non-analytic) slice class of the angular Poincaré estimate

The estimates of §'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

are stated for data which are `C^∞` — *not* analytic.  In this Mathlib the order type of
`ContDiff` is `ℕ∞ω = WithTop ℕ∞`, whose top element `⊤ = ω` is the **analytic** order
(`Mathlib/Analysis/Calculus/ContDiff/Defs.lean`), while `∞ = ((⊤ : ℕ∞) : ℕ∞ω)` is honest
`C^∞`.  Writing `⊤` where smoothness is meant therefore silently asks for analyticity: the
trap recorded in `Submission/Work/Stability/Cutoff.lean` and
`Submission/Work/FTS/EllipticEst/zHardyCutDefs.lean`.  In particular the class
`Work.FTS.EllipticEst.SliceSmooth u = ContDiffOn ℝ ⊤ u (Ioo (-1) (π/2+1))` of the
one-dimensional slice estimates is *analyticity*, hence unusable for the slices of a merely
`C^∞` datum.

This module fixes the honest `C^∞` replacement

* `SliceSmoothO u` — `u` is `C^∞` on `(-1, π/2 + 1)`, i.e. on a neighbourhood of the closed
  angular interval `Iθ = [0, π/2]`;

together with the basic API: it is the class of the `_open` versions of the slice estimates
(`ThetaU.slice_f_bound_open`, `ThetaU.slice_d_bound_open`), and it is what the angular slices
of the `C^∞`-on-the-half-strip data `SmoothOpenθ f` (the class defined in
`Submission.Work.FTS.EllipticEst.ThetaU.Defs`) are.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.ThetaU.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `C^∞` order and the half-strip -/

/-- The *smooth* order `∞` of `ContDiff`, as opposed to the analytic order `⊤ = ω`. -/
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem smoothOrder_eq : smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) := rfl

/-- The half-strip `(0,∞) × (-1, π/2 + 1)` on which the data of the angular Poincaré estimate
are `C^∞`.  Its `θ`-range contains the closed angular interval `Iθ` in its interior, which is
what makes the one-dimensional slice estimates (FTC, Rolle, vanishing of the boundary terms)
available. -/
def halfStrip : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_halfStrip : IsOpen halfStrip := isOpen_Ioi.prod isOpen_Ioo

theorem mem_halfStrip {z θ : ℝ} :
    (z, θ) ∈ halfStrip ↔ 0 < z ∧ -1 < θ ∧ θ < Real.pi / 2 + 1 := Iff.rfl

theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## The class `SliceSmoothO` -/

/-- `u` is `C^∞` on the neighbourhood `(-1, π/2 + 1)` of the closed angular interval `Iθ`.
This is the class of the one-dimensional slice estimates, weakened from the analytic
`Work.FTS.EllipticEst.SliceSmooth` to honest `C^∞`. -/
abbrev SliceSmoothO (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ smoothOrder u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))

/-- `SliceSmoothO` is the `∀ n : ℕ, ContDiffOn ℝ n …` shape. -/
theorem sliceSmoothO_iff (u : ℝ → ℝ) :
    SliceSmoothO u ↔ ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  contDiffOn_infty

theorem SliceSmoothO.of_le {u : ℝ → ℝ} (h : SliceSmoothO u) (n : ℕ) :
    ContDiffOn ℝ n u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  contDiffOn_infty.mp h n

theorem SliceSmoothO.mono {u : ℝ → ℝ} (h : SliceSmoothO u) {s : Set ℝ}
    (hs : s ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) : ContDiffOn ℝ smoothOrder u s :=
  ContDiffOn.mono h hs

/-- The analytic class `SliceSmooth` implies the `C^∞` class `SliceSmoothO` (the converse
fails: a bump function is `C^∞` but not analytic on any neighbourhood of its support). -/
theorem SliceSmoothO.of_sliceSmooth {u : ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SliceSmooth u) : SliceSmoothO u :=
  h.of_le le_top

theorem SliceSmoothO.continuousOn_Iθ {u : ℝ → ℝ} (h : SliceSmoothO u) :
    ContinuousOn u Work.Spaces.Iθ := h.continuousOn.mono Iθ_subset_Ioo

/-! ## Slices of `SmoothOpenθ` data -/

/-- The angular slice of a `C^∞`-on-the-half-strip function at a level `z > 0` is
`SliceSmoothO`. -/
theorem SmoothOpenθ.sliceSmoothO {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) {z : ℝ} (hz : 0 < z) :
    SliceSmoothO (fun θ => f z θ) := by
  have hf : ContDiffOn ℝ smoothOrder (Function.uncurry f) halfStrip :=
    contDiffOn_infty.mpr h
  have hp : ContDiffOn ℝ smoothOrder (fun θ : ℝ => (z, θ))
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hcomp := hf.comp hp (fun θ hθ => ⟨hz, hθ⟩)
  simpa only [Function.uncurry, Function.comp_def, SliceSmoothO] using hcomp

/-- `SmoothOpenθ` restricted to the open quadrant (the class of the existing open-quadrant
API, e.g. of `DthIter_DzIter_eq_mixed_open`). -/
theorem SmoothOpenθ.to_quad {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => ContDiffOn.mono (h n) (fun p hp =>
    ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩)

/-- The uncurried iterate `D_z^j f` of a `SmoothOpenθ` datum is again `C^∞` on the half-strip. -/
theorem SmoothOpenθ.DzIter {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (j : ℕ) :
    SmoothOpenθ (Work.Spaces.DzIter j f) := by
  have hf : ContDiffOn ℝ smoothOrder (Function.uncurry f) halfStrip :=
    contDiffOn_infty.mpr h
  intro n
  exact (Work.FTS.LocData.contDiffOn_DzIter isOpen_halfStrip hf j).of_le (by norm_num)

/-- The uncurried iterate `D_θ^i f` of a `SmoothOpenθ` datum is again `C^∞` on the half-strip. -/
theorem SmoothOpenθ.DthIter {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (i : ℕ) :
    SmoothOpenθ (Work.Spaces.DthIter i f) := by
  have hf : ContDiffOn ℝ smoothOrder (Function.uncurry f) halfStrip :=
    contDiffOn_infty.mpr h
  intro n
  exact (Work.FTS.LocData.contDiffOn_DthIter isOpen_halfStrip hf i).of_le (by norm_num)

/-- The uncurried iterate `∂_θ^m f` of a `SmoothOpenθ` datum is again `C^∞` on the half-strip. -/
theorem SmoothOpenθ.pthIter {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (m : ℕ) :
    SmoothOpenθ (Work.Spaces.pthIter m f) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      have hf : ContDiffOn ℝ smoothOrder (Function.uncurry (Work.Spaces.pthIter m f))
          halfStrip := contDiffOn_infty.mpr ih
      intro n
      exact (Work.FTS.LocData.contDiffOn_pth isOpen_halfStrip hf).of_le (by norm_num)

/-- The uncurried iterate `D_z^j D_θ^i f` of a `SmoothOpenθ` datum is `C^∞` on the half-strip. -/
theorem SmoothOpenθ.mixed {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (j i : ℕ) :
    SmoothOpenθ (Work.Spaces.mixed j i f) := (h.DthIter i).DzIter j

/-- Continuity of the angular slices `θ ↦ D_z^j f z θ` on the closed angular interval. -/
theorem SmoothOpenθ.continuousOn_slice_DzIter {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (j : ℕ)
    {z : ℝ} (hz : 0 < z) : ContinuousOn (fun θ => Work.Spaces.DzIter j f z θ) Work.Spaces.Iθ :=
  (h.DzIter j).sliceSmoothO hz |>.continuousOn_Iθ

/-- Continuity of the angular slices `θ ↦ D_z^j D_θ^i f z θ` on the closed angular interval. -/
theorem SmoothOpenθ.continuousOn_slice_mixed {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (j i : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.mixed j i f z θ) Work.Spaces.Iθ :=
  (h.mixed j i).sliceSmoothO hz |>.continuousOn_Iθ

end Work.FTS.EllipticEst.ThetaU
