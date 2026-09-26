import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Bridge

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.BoxGeneric.PlaneTransverse

/-- The plane `{y | y i = u}` cut with the surface is the level set of the coordinate function. -/
theorem plane_inter_carrier_eq_levelSet (ψ : Submission.Diffeo) (i : Fin 3) (u : ℝ) :
    ({y : R3 | y i = u} ∩ (Work.Smooth.Morse.torus ψ).carrier) =
      Work.Smooth.Morse.levelSet ψ (fun y : R3 => y i) u := by
  rw [Work.Smooth.Morse.levelSet]
  exact Set.inter_comm _ _

theorem ae_transverseSphere_coord {ψ : Submission.Diffeo} (hS : Work.Smooth.BoxGeneric.SardCoord ψ) (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) (i : Fin 3) : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ) {y : LeanEval.KnotTheory.PardonDistortion.R3 | y i = u} := by
  filter_upwards [hS i] with u hu
  have hg : Continuous (fun y : R3 => y i) := by fun_prop
  have hg1 : ContDiff ℝ 1 (fun y : R3 => y i) := by fun_prop
  have hcomp : IsCompact ({y : R3 | y i = u} ∩ (Work.Smooth.Morse.torus ψ).carrier) := by
    rw [plane_inter_carrier_eq_levelSet]
    exact Work.Smooth.Morse.Surface.isCompact_levelSet ψ hg u
  have harc : Work.Smooth.Morse.IsLocalArc ψ
      ({y : R3 | y i = u} ∩ (Work.Smooth.Morse.torus ψ).carrier) := by
    rw [plane_inter_carrier_eq_levelSet]
    exact Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue ψ hg1 hu
  exact transverseSphere_of_compact_isLocalArc hclass hcomp harc

end Work.Smooth.BoxGeneric.PlaneTransverse
