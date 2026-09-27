import Mathlib
import Submission.Work.Drive.refTripleOneT
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.sweepTripleGeneric

/-!
# The vocabulary of the `hn2` node's missing class-parity input

The node `Work.Drive.hn2_refTripleAt_producerHuv` produces `Work.Drive.RefTripleAt` at a small
parameter `t : ℝ¹²`.  Everything of `RefTripleAt` *except* its class-parity clause
(`Odd (classTripleSet …).ncard`) is produced by
`Work.Drive.exists_refTripleGenericity_wall` (`Drive/hn2Clause6Sard.lean`), which takes as input an
open set `A` of parameters that is dense at every point of the closed unit ball and whose points are
required (by the caller) to carry the class-parity clause.

This module fixes that interface as a predicate, so that the missing producer can be stated — and
proved — independently of the node's file.

* `Work.Drive.PosBlocks t` — the three perturbation blocks of `t` have a *positive* level coordinate
  `(blk k t) 0 > 0` (the direction in which the chart perturbation *increases* levels — the regime in
  which the parametrised Sard of the sweep families has its richness, cf. `threeBlock_dense_point`).
* `Work.Drive.RefParityFamily Q R u v A` — `A` is open, **dense at every point of the closed unit ball
  whose blocks are positive**, and at every point of `A` the class-triple set of the perturbed
  reference triple `![rotPresentation Q u, rotPresentation Q v, R]` has **odd** cardinality.

The last conjunct is the `hodd` chapter of Hugelmeyer's proof in the `hn2` configuration: the mod-`2`
degree of the triple intersection of the three class `2`-chains.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **`Meet3Hyp` of the sweeps** of a triple `P` of plane presentations, at the perturbation
parameter `t` — bundled so that statements mentioning it do not have to resolve the
charted-space instances of `CappingSpace` at the use site. -/
def SweepMeet3 (Q : ℂ → CappingSpace)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  Meet3Hyp CappingSpace (sweepChartFam P Ξ c t)

/-- **The three perturbation blocks of `t` point in the level-increasing direction**: the `0`-th
coordinate of each block is positive.  This is the regime in which the chart perturbations scale the
levels *up*, i.e. in which the parametrised Sard of the sweep families is rich and the
`threeBlock_dense_point` argument lives. -/
def PosBlocks (t : EuclideanSpace ℝ (Fin 12)) : Prop := ∀ k : Fin 3, 0 < (blk k t) 0

/-- **The class-parity family of the `hn2` reference triple** at a plane `R`.  `A` is open, dense at
every point of the closed unit ball with positive blocks (the region that `threeBlock_dense_point`
consumes), and at every one of its points the perturbed reference triple
`![rotPresentation Q u, rotPresentation Q v, R]` has an odd number of class triples. -/
def RefParityFamily (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A : Set (EuclideanSpace ℝ (Fin 12))) : Prop :=
  IsOpen A ∧
    (∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 → PosBlocks s →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ) ∧
    (∀ t ∈ A, Odd (classTripleSet
      (fun k z => chartPert (blk k t) (refTriple Q R u v k z))).ncard)

end

end Work.Drive
