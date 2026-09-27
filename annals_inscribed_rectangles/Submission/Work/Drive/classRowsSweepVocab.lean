import Mathlib
import Submission.Work.Drive.hdenseOneT
import Submission.Work.Drive.loopBoxData_sweep
import Submission.Work.Drive.boxRegDefs

/-!
# The vocabulary of the sweep-row open-dense producer

`Work.Drive.classRowsSweep_openDense` needs two kinds of statement about the design's *sweep* rows
(`Work.Drive.DesignRowsSweepAt`, `Drive/classRowVocab.lean`) on an open set of parameters dense at every
point of the closed unit ball:

* **openness** of the box-restricted class-level rows (`Work.Drive.BoxPairReg`,
  `Work.Drive.BoxEndTripleReg`) in a jointly smooth family of *plane presentations*;
* **density**, i.e. a producer of the pair row's `Work.Drive.LoopBoxData` for an arbitrary fixed loop.

This module only fixes the vocabulary so that the delegated producers and the assembly agree on it: the
two smoothness predicates are *definitions* (so that statements about them can be written without the
local `ChartedSpace CappingSpace` / `ChartedSpace (Projectivization ℝ (Eucl 3))` instances).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **Smoothness of a single plane presentation** (a `2`-chain).  Stated as a definition so that
statements about it can be written without the local `ChartedSpace CappingSpace` instance. -/
def SmoothPlane₂ (A : EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) A

/-- **Joint smoothness of a parametrised family of plane presentations**, in the form used by the
class-row producers (`Work.Drive.IsSmoothFam₂` is the same definition with the parameter space named). -/
abbrev SmoothPlaneFam {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  IsSmoothFam₂ A

end

end Work.Drive
