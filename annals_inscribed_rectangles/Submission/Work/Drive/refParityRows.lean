import Mathlib
import Submission.Work.Drive.refTripleLocalAssembly
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.analyticDensity
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.refPlaneLinearization
import Submission.Work.Drive.linCommonPoint

/-!
# The row vocabulary of the `refParityFamily` assembly

The node `Work.Drive.refParityFamily` reduces the class parity of the *reference triple*
`refTriple Q (refPlanePres φ lam hlam) u v` to seven class-level rows, at a parameter
`t : 𝔼¹²`, for the **per-block transported** linear family `k ↦ (linBase A k).trans (classEquiv (blk k t))`
(the transports are forced by the producers: `exists_classRows345_design` transports slot `0` by
`blk 0 t` and slot `1` by `blk 1 t`, and the reference block's model is `linBase A 2` transported by
`blk 2 t`).

* `refPertBlock Q R u v t k` — the perturbed block `chartPert (blk k t) ∘ refTriple Q R u v k`;
* `linRowModel A t k` — the `k`-th transported linear model at the level `1`;
* `RefRows Q u v φ lam hlam A t` — the six rows that are *not* implied by the general position of the
  linear family: the three `PairReg` rows (`hpairL0L1`, `hpairL0P2`, `hpair12`) and the three
  `EndTripleReg` rows (`hend012`, `hendL012`, `hendL10P2`).  The remaining row `hendLLL` and the two
  clauses `hrank`/`hgen` are the hypotheses of `Work.Drive.refGeneralPosition_openDense` and are kept
  separate (the assembly needs `hrank` as an *input* of `linCommonPt`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The perturbed block of the reference triple**: `chartPert (blk k t) ∘ refTriple k`. -/
def refPertBlock (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun y => chartPert (blk k t) (refTriple Q R u v k y)

/-- **The `k`-th transported linear model** of the assembly, at the level `1`. -/
def linRowModel (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) :
    EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
  linTransClass (linBase A k) (blk k t) 1 one_pos

/-- **The six `PairReg`/`EndTripleReg` rows of the assembly** (`hpairL0L1`, `hpairL0P2`, `hpair12`,
`hend012`, `hendL012`, `hendL10P2`) at the parameter `t`, for the reference triple
`refTriple Q (refPlanePres φ lam hlam) u v` and the per-block transported linear family
`k ↦ (linBase A k).trans (classEquiv (blk k t))`. -/
def RefRows (Q : ℂ → CappingSpace) (u v : UnitAddCircle) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (lam : ℝ) (hlam : 0 < lam) (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  PairReg (linRowModel A t 0) (linRowModel A t 1) ∧
  PairReg (linRowModel A t 0)
    (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2)) ∧
  PairReg (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 1))
    (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2)) ∧
  EndTripleReg (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 0))
    (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 1))
    (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2)) ∧
  EndTripleReg (linRowModel A t 0)
    (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 1))
    (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2)) ∧
  EndTripleReg (linRowModel A t 1) (linRowModel A t 0)
    (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2))

/-- **`hrank` and `hgen` of the per-block transported `linBase`-family** at the parameter `t`. -/
def RefGP (A : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  ∃ hrank : Module.finrank ℝ ↥(⨅ k : Fin 3,
      linSub ((linBase A k).trans (classEquiv (blk k t)))) = 1,
    ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart ((linBase A k).trans (classEquiv (blk k t))) 1 one_pos z
        ≠ linCommonPt (fun k => (linBase A k).trans (classEquiv (blk k t))) 1 one_pos hrank

end

end Work.Drive
