import Mathlib
import Submission.Work.StemsB.SerreSphereDefs
import Submission.Work.StemsB.RadialRetraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sup-norm collar of the sphere model

For the sphere case of the Serre exact sequence one needs a pair in the model
`SphModel n = OnePoint ℝⁿ` which is a *disc pair* `(Dⁿ, Sⁿ⁻¹)` in the weak sense that both
component maps of a pair map onto `(Iⁿ, ∂Iⁿ)` are homotopy equivalences.  The Euclidean-norm
pieces of `Submission/Work/StemsB/SphLoopModel.lean` and `SerreSphereDefs.lean` are not quite of
that shape: the "shell" `sphLoopThick ∩ sphLoopBig` is a *spherical* shell, which is not a collar
of the cube boundary `sphLoopBdry n = {|v|_∞ = 1}`.

This file introduces the **sup-norm** version: the outer piece

  `sphLoopOuter n = {∞} ∪ {↑v | ∃ i, 1/2 < |v i|}`  (the complement of the closed cube `|v|_∞ ≤ 1/2`)

whose intersection with the inner cube `sphLoopBig n = {|v|_∞ < 3/2}` is the **collar**

  `sphLoopCollar n = sphLoopOuter n ∩ sphLoopBig n = {1/2 < |v|_∞ < 3/2}`,

which *is* a neighbourhood of the cube boundary, and which is mapped onto the boundary by the
sup-norm normalisation `v ↦ v / coordSup n v` (with the continuous extension `v ↦ v / max (1/2)
(coordSup n v)` on all of the inner cube).  The two pieces still cover the model, since the
complement of the outer piece is the closed cube `|v|_∞ ≤ 1/2`, contained in the inner cube.

`Work.StemsB.sphLoopCollar_main` is the resulting relative Künneth statement, the exact analogue of
`Work.StemsB.cubePair_main` for the pair `(sphLoopBig n, sphLoopCollar n)`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- The **sup-norm outer piece** `{∞} ∪ {|v|_∞ > 1/2}`: the complement of the closed cube of
sup-norm radius `1/2` (so it is open), containing both `∞` and the whole outer disc
`sphLoopOut n`. -/
def sphLoopOuter (n : ℕ) : Set (SphModel n) :=
  {x | x = OnePoint.infty ∨ ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ ∃ i, (1 / 2 : ℝ) < |v i|}

/-- The **collar** `1/2 < |v|_∞ < 3/2` of the cube boundary, i.e. the intersection of the sup-norm
outer piece with the inner cube. -/
def sphLoopCollar (n : ℕ) : Set (SphModel n) := sphLoopOuter n ∩ sphLoopBig n

/-- The collar inside the product `sphLoopBig n × Y`. -/
def sphLoopCollarProd (n : ℕ) (Y : Type) : Set (↥(sphLoopBig n) × Y) :=
  {x | (x.1 : SphModel n) ∈ sphLoopCollar n}

end

end Work.StemsB
