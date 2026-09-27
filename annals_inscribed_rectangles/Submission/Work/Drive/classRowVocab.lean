import Mathlib
import Submission.Work.Drive.classRows
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.hendL012Row
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.linCommonPoint

/-!
# The row vocabulary of the ends clause, in the *transported* form

`Work.Drive.exists_classRowFamily` needs the seven class-level rows of the lead's §3 table
(`NOTES_LEAD_hodd_blockT6.md`) for the design's triple

> `P̂ k (t) = planeClassMap (fun y => chartPert (blk k t) (rotPresentation Q (designAngles a c' k) y))`

against the three *linear disk models* of a linear family `Φ k` — in the form in which the producers
supply them, namely with the `k`-th model **transported** by `classEquiv (blk k t)`:

> `lin_k (t) = planeClassMap (diskPlane (linPlaneChart ((Φ k).trans (classEquiv (blk k t))) cl hcl))`.

The reason for the transport is recorded in `HENDL012_ROW_STATUS.md` §0, §2: the only genericity
available for the mixed rows comes from the *sweep* families `sweepChartFam`, which perturb all three
blocks by their own parameter, and

> `planeClassMap (chartPert τ (diskPlane (linPlaneChart Φ cl hcl)))`
>   `= planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv τ)) cl hcl))`

(`Work.Drive.planeClassMap_chartPert_diskPlane_linPlaneChart`).

This module only fixes the vocabulary, so that the row producers and the assembly share one
definition.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.projCharted

noncomputable section

/-- The design's `k`-th perturbed rotated chart of `Q` at the angle `u`, as a *capped* presentation. -/
def designPertPlane (Q : ℂ → CappingSpace) (u : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12))
    (k : Fin 3) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun y => chartPert ((blk k) t) (rotPresentation Q u y)

/-- Its class map (the first argument of `Work.Drive.classTripleSet` at the design's triple). -/
def designPertClass (Q : ℂ → CappingSpace) (u : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12))
    (k : Fin 3) : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
  planeClassMap (designPertPlane Q u t k)

/-- The class map of the **transported linear disk model** of `Φ` at the class `τ` and the level
`cl`: the `k`-th linear model of the ends clause, in the form the sweep genericity produces. -/
def linTransClass (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ : Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
  planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv τ)) cl hcl))

/-- The three angles of the design's triple, as real rotations, for the documentation of the rows. -/
def designRowAngles (a c' : UnitAddCircle) : Fin 3 → UnitAddCircle := designAngles a c'

/-- **The four rows of the design's own triple and of the *sweep* families**: the pair row of `P̂₁P̂₂`,
the end-triple row of the design's own triple, and the two end-triple rows in which one or two of the
three slots are (transported) linear models.  These are the rows produced by the parametrised-Sard
genericity of the *radial sweeps* (the bridge `Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted`
applied to the sweep families of `Work.Drive.exists_classRows345_design` and of
`Work.Drive.pairReg_blockPlane_of_loopBoxData`). -/
def DesignRowsSweepAt (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  PairReg (designPertClass Q (designAngles a c' 1) t 1)
      (designPertClass Q (designAngles a c' 2) t 2) ∧
  EndTripleReg (designPertClass Q (designAngles a c' 0) t 0)
      (designPertClass Q (designAngles a c' 1) t 1)
      (designPertClass Q (designAngles a c' 2) t 2) ∧
  EndTripleReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
      (designPertClass Q (designAngles a c' 1) t 1)
      (designPertClass Q (designAngles a c' 2) t 2) ∧
  EndTripleReg (linTransClass (Φ 1) ((blk 1) t) cl hcl)
      (linTransClass (Φ 0) ((blk 0) t) cl hcl)
      (designPertClass Q (designAngles a c' 2) t 2)

/-- **The remaining rows, which involve only *linear* models and the last design block**: the pair rows
`lin₀(t) P̂₂` and `lin₀(t) lin₁(t)`, the all-linear end-triple row, and the general-position clauses
`hrank`/`hgen` of the transported linear family.  These are the rows whose genericity is *elementary*
(the class maps of linear plane charts are projective planes, so the conditions are those of three
projective planes in general position). -/
def DesignRowsLinAt (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
      (designPertClass Q (designAngles a c' 2) t 2) ∧
  PairReg (linTransClass (Φ 0) ((blk 0) t) cl hcl)
      (linTransClass (Φ 1) ((blk 1) t) cl hcl) ∧
  EndTripleReg (linTransClass (Φ 2) ((blk 2) t) cl hcl)
      (linTransClass (Φ 0) ((blk 0) t) cl hcl)
      (linTransClass (Φ 1) ((blk 1) t) cl hcl) ∧
  (∃ hrank : Module.finrank ℝ
      ↥(⨅ k : Fin 3, linSub ((Φ k).trans (classEquiv ((blk k) t)))) = 1,
    ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart ((Φ k).trans (classEquiv ((blk k) t))) cl hcl z
        ≠ linCommonPt (fun k => (Φ k).trans (classEquiv ((blk k) t))) cl hcl hrank)

/-- **The nine class-level clauses of the ends clause at one parameter `t`**, in the transported form.
This is the conjunction that the linearisation of the design's triple consumes: the four sweep rows
(`DesignRowsSweepAt`) and the five linear rows (`DesignRowsLinAt`). -/
def DesignRowsAt (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  DesignRowsSweepAt Q a c' Φ cl hcl t ∧ DesignRowsLinAt Q a c' Φ cl hcl t

end

end Work.Drive
