/-
# `Work.SolutionDelivery.Slices` — the vorticity boxes and the Biot–Savart dictionary

This module derives, from the input package `ConstructedSolution α`, the *vorticity-level*
statements consumed by the assembly:

* the Biot–Savart dictionary `∇×(u·t) = ω(·,t)` (`Work.LWP.vorticity_biotSavart` through the
  slicewise identity `u(·,t) = BS(ω(·,t))`);
* the integrability of the vorticity slices (bounded functions with compact support);
* the support, boundedness and measurability boxes of `ω` and `∂ₜω` on the physical window
  `window T = [-1,T+1]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Datum
import Submission.Work.SolutionDelivery.Integrable.integrable_of_support_subset_closedBall
import Submission.Work.SolutionDelivery.Measurable.aestronglyMeasurable_of_contOn_closedBall
import Submission.Work.SolutionDelivery.Measurable.slicesMeasurable_of_core
import Submission.Work.SolutionDelivery.Measurable.slicesMeasurable_timeDeriv_of_core
import Submission.Work.SolutionDelivery.Vorticity.vorticity_eq_of_bsSlice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

variable {α : NNReal}

namespace ConstructedSolution

variable (C : ConstructedSolution α)

/-- **The slices of `ω` are measurable.** -/
theorem slicesMeasurable :
    Work.StabilityFar.SlicesMeasurable C.ω C.T :=
  Measurable.slicesMeasurable_of_core (ρ := C.R + 1) (R := C.R) (T := C.T)
    (le_of_lt (lt_add_one C.R)) C.hωcore.1 C.hSupp

/-- **The slices of `∂ₜω` are measurable.**  Restriction of the `extWindow` version
(`Work.SolutionDelivery.Measurable.slicesMeasurable_timeDeriv_of_core`) to the physical window. -/
theorem slicesMeasurable_timeDeriv :
    Work.StabilityFar.SlicesMeasurable (timeDeriv C.ω) C.T := by
  have hcont : ContDiffOn ℝ 1 C.ω.uncurry (Work.StabilityFar.coreRegion (C.R + 1) ×ˢ extWindow C.T) :=
    C.hωcore.1
  have hdc := Measurable.hasDerivAt_timeDeriv_slice_of_core (ρ := C.R + 1) (R := C.R)
    (T := C.T) (le_of_lt (lt_add_one C.R)) hcont C.hSupp
  have hmeas := Measurable.aestronglyMeasurable_slice_of_core_extWindow (ρ := C.R + 1) (R := C.R)
    (T := C.T) (le_of_lt (lt_add_one C.R)) hcont C.hSupp
  intro t ht
  rw [Work.StabilityFar.mem_window] at ht
  have htext : t ∈ extWindow C.T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set ε : ℝ := min 1 (min (t + 2) (C.T + 2 - t)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min one_pos (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  have hε1 : ε ≤ t + 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ C.T + 2 - t := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Set.Ioo (t - ε) (t + ε) ⊆ extWindow C.T := by
    intro s hs
    exact ⟨by linarith [hs.1, hε1], by linarith [hs.2, hε2]⟩
  exact Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice hεpos
    (fun s hs y => hdc s (hsub hs) y) (fun s hs => hmeas s (hsub hs))

/-- **The vorticity slices are integrable**: they are measurable, bounded by `M` and supported in
the ball of radius `R`. -/
theorem slices_integrable :
    ∀ t ∈ Work.StabilityFar.window C.T, Integrable (fun y : R3 => C.ω y t) :=
  fun t ht => Integrable.integrable_of_support_subset_closedBall (R := C.R) (M := C.M)
    ((C.slicesMeasurable t ht)) (fun y hy => C.hSupp_window t ht y hy)
    (fun y => C.hBdd_window t ht y)

/-- **The vorticity slices are bounded as a function** (the form consumed by the Biot–Savart
law). -/
theorem slices_isBoundedFun :
    ∀ t ∈ Work.StabilityFar.window C.T, IsBoundedFun (fun y : R3 => C.ω y t) :=
  fun t ht => Work.LWP.isBoundedFun_of_norm_le (C.hBdd_window t ht)

/-- **The Biot–Savart dictionary**: the vorticity of the constructed velocity is the field `ω`
that the construction uses to build it. -/
theorem vorticity_eq :
    ∀ t ∈ Work.StabilityFar.window C.T,
      ∀ x : R3, vorticity (fun y => C.u y t) x = C.ω x t :=
  Vorticity.vorticity_eq_of_bsSlice C.lwp.law C.bsSlice C.slices_integrable
    C.slices_isBoundedFun
    (fun t ht => C.hDivω t (C.window_subset ht))

/-- The vorticity slices are supported in `B(0,R)`. -/
theorem vorticity_supported :
    ∀ t ∈ Work.StabilityFar.window C.T,
      ∀ x : R3, vorticity (fun y => C.u y t) x ≠ 0 → x ∈ Metric.closedBall 0 C.R :=
  fun t ht x hx => C.hSupp_window t ht x (by rwa [C.vorticity_eq t ht x] at hx)

/-- The vorticity slices are bounded by `M`. -/
theorem vorticity_bounded :
    ∀ t ∈ Work.StabilityFar.window C.T, ∀ x : R3, ‖vorticity (fun y => C.u y t) x‖ ≤ C.M :=
  fun t ht x => by rw [C.vorticity_eq t ht x]; exact C.hBdd_window t ht x

/-- The vorticity sup-norm is honest (`BddAbove`) at every time of `[0,T)`. -/
theorem bddAbove_vorticity {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    BddAbove (Set.range (fun x : R3 => ‖vorticity (fun y => C.u y t) x‖)) :=
  ⟨C.M, by
    rintro _ ⟨x, rfl⟩
    exact C.vorticity_bounded t (Work.StabilityFar.Ico_subset_window C.hT.le ht) x⟩

end ConstructedSolution

end Work.SolutionDelivery
