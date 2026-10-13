/-
# `Work.SolutionDelivery.BKM` — the BKM divergence and the `St5` lower bound

The last two fields of `Work.StabilityFar.AssemblyInputs`:

* `bkmIntegrable` — the interval-integrability of `t ↦ ‖ω(·,t)‖_∞`, obtained from the **continuity**
  of that function, which follows from the joint continuity of `(x,t) ↦ ∇×(u·t) x` on the compact
  strip `B(0,R) × [-1,T+1]` (slices are supported in `B(0,R)`, so the supremum over `ℝ³` is the
  supremum over the ball, and the supremum over a compact set of a jointly continuous family is
  continuous — `Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall`);
* `linfLower` — `St5`'s lower bound `c/(T*-t) ≤ ‖ω(·,t)‖_∞` with `c = c₀α/2`, from the
  self-similar ansatz `Work.SolutionDelivery.ConstructedSolution.hansatz` through
  `Work.StabilityFar.vortLinfLower_of_ansatz`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.SolutionDelivery.HolderInputs
import Submission.Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall
import Submission.Work.SolutionDelivery.Sup.ciSup_norm_vorticity_eq_ciSup_closedBall
import Submission.Work.SolutionDelivery.Measurable.continuousOn_vorticity_of_contDiffOn

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

/-- The vorticity sup-norm function of the constructed solution is continuous on the window. -/
theorem continuousOn_vortLInf :
    ContinuousOn (Work.LWP.vortLInf C.u) (Set.Icc (-1) (C.T + 1)) := by
  have hcont : ContinuousOn (fun p : R3 × ℝ => ‖vorticity (fun y => C.u y p.2) p.1‖)
      (Metric.closedBall 0 C.R ×ˢ Set.Icc (-1) (C.T + 1)) :=
    (Measurable.continuousOn_vorticity_of_contDiffOn (T := C.T) (R := C.R) C.smooth).norm
  have hsup := Sup.continuousOn_ciSup_closedBall
    (F := fun x t => ‖vorticity (fun y => C.u y t) x‖)
    (R := C.R) (a := -1) (b := C.T + 1) C.hR.le hcont
  refine hsup.congr fun t ht => ?_
  exact Sup.ciSup_norm_vorticity_eq_ciSup_closedBall (u := C.u) (R := C.R) (t := t) (M := C.M)
    C.hR.le (fun x => C.vorticity_bounded t ht x) (fun x => C.vorticity_supported t ht x)

/-- **`bkmIntegrable` of `AssemblyInputs`.** -/
theorem bkmIntegrable :
    ∀ t ∈ Set.Ico 0 C.T, IntervalIntegrable (Work.LWP.vortLInf C.u) volume 0 t := by
  intro t ht
  refine (C.continuousOn_vortLInf.mono ?_).intervalIntegrable
  rw [Set.uIcc_of_le ht.1]
  intro s hs
  exact ⟨by linarith [hs.1], by linarith [hs.2, ht.2.le]⟩

/-- **`VortLinfLower` of `AssemblyInputs` (`St5`'s input).** -/
theorem linfLower (hα : 0 < (α : ℝ)) :
    Work.StabilityFar.VortLinfLower C.u C.T (C.c₀ * (α : ℝ) / 2) :=
  Work.StabilityFar.vortLinfLower_of_ansatz (u := C.u) (T := C.T) (c₀ := C.c₀) (α := (α : ℝ))
    (lam := C.lam) C.hlam_pos C.hlam_le C.hc₀ hα (fun t ht => C.bddAbove_vorticity ht)
    (fun t ht => by
      obtain ⟨x, hx⟩ := C.hansatz t ht
      refine ⟨x, ?_⟩
      rw [C.vorticity_eq t (Work.StabilityFar.Ico_subset_window C.hT.le ht) x]
      exact hx)

end ConstructedSolution

end Work.SolutionDelivery
