import Mathlib
import Submission.Work.Core.Std
import Submission.Work.NN.Core.Defs

/-!
# The flat case

The case `A = 0` (i.e. `J = stdOf T`, a constant complex structure) is unconditional: the standard
coordinate functions are `stdOf T`-holomorphic and their differential is the invertible
`tupleDeriv T`.  This is stage (i) of the analytic core.
-/

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff Topology

namespace Work.NN.Core

variable {n : ℕ}

/-- **The flat case of the analytic core.**  For the standard structure `stdOf T` transported by
`T`, the standard coordinates form an independent holomorphic frame on all of `ℝ^{2n}`. -/
theorem isHolomorphicFrame_stdOf (T : E n ≃L[ℝ] F n) :
    IsHolomorphicFrame (stdOf T) univ (fun j y => zcoord T j y) := by
  refine ⟨fun j => (contDiff_zcoord T j).contDiffOn, fun j => isJHolomorphicOn_zcoord T j univ, ?_⟩
  intro y _
  simpa using bijective_fderiv_zcoord_tuple T y

/-- The flat case in the presence of a `FlatSolver` on `P`: the correction produced by the
contraction vanishes identically when `J = stdOf T`. -/
theorem exists_frame_stdOf (T : E n ≃L[ℝ] F n) {P : Set (E n)} :
    ∃ v : Fin n → E n → ℂ,
      (∀ j, ∀ y ∈ P,
        dbar (stdOf T) (v j) y = dbarPert (perturbation (stdOf T) T) (zcoord T j) y) ∧
      IsHolomorphicFrame (stdOf T) P (fun j y => zcoord T j y - v j y) := by
  refine ⟨fun _ _ => 0, ?_, ?_⟩
  · intro j y hy
    have h1 : dbar (stdOf T) (fun _ : E n => (0 : ℂ)) y = 0 := dbar_const _ _ _
    have h2 : dbarPert (perturbation (stdOf T) T) (zcoord T j) y = 0 := by
      have hA : perturbation (stdOf T) T y = 0 := by simp [perturbation]
      ext v
      simp [dbarPert, hA]
    rw [h1, h2]
  · have h : (fun j y => zcoord T j y - (fun _ _ => (0 : ℂ)) j y) = (fun j y => zcoord T j y) := by
      funext j y
      simp
    rw [h]
    refine ⟨fun j => ((isHolomorphicFrame_stdOf T).contDiff j).mono (subset_univ P), ?_, ?_⟩
    · intro j y _
      exact (isHolomorphicFrame_stdOf T).holomorphic j y (mem_univ y)
    · intro y _
      exact (isHolomorphicFrame_stdOf T).bijective y (mem_univ y)

end Work.NN.Core
