import Mathlib
import Submission.Work.Drive.refTripleMixedFactors
import Submission.Work.Drive.refTripleBlockT6

/-!
# Clause `6` of the `hn2` reference-triple producer, with the hypotheses the components actually use

`Work.Drive.refTripleAt_blockT6At` (`Drive/hn2_refTripleAt_producer.lean`) is stated with `hlev`,
`hmeet` and the two `GoodAt`s, but its six conjuncts are assembled from three sources that need
*other* data:

* the two `Odd (topBdryMeet ·) ↔ …` conjuncts: the transport `T6` at the two configuration blocks,
  i.e. `Work.Drive.refTriple_topBdryMeet_zero_iff` and `Work.Drive.refTriple_topBdryMeet_zero_iff_block1`
  (`Drive/refTripleBlockT6.lean`), which consume the `T6GenAtDBox` bundles, the geometric disjointness
  and the strict level bands at each block (all provided on disk by `refTripleRows.lean` §7–§9 and
  `refTripleLevelBand.lean`);
* the two identifications `coreSideCount = CntAt`: `Work.Drive.refTriple_blockIdent` (proved);
* the two **mixed factors** `(F1)`: `Work.Drive.refTriple_mixedFactors_at`
  (`Drive/refTripleMixedFactors.lean`), i.e. the box form of the mixed factors, from the parametric
  oddness `hF1` (`Work.Drive.refTriple_mixedFactors`) and the two mixed pairs' goodness at `t`.

This module performs that assembly once, so that the producer can replace its `sorry` by a call.  The
hypotheses are grouped in the order in which the producer obtains them.
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false

/-- **Clause `6` of `RefTripleAt` at one parameter, from the data its components consume.**  The
conclusion is verbatim the six-conjunct bundle of `Work.Drive.refTripleAt_blockT6At`. -/
theorem refTripleAt_blockT6At_of_data {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (u v : UnitAddCircle) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k)
    (t : EuclideanSpace ℝ (Fin 12))
    (hM : Meet3Hyp CappingSpace
      (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) cblk t))
    (hgen0 : T6GenAtDBox (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1)
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)
      (cblk 1) (cblk 2))
    (hgen1 : T6GenAtDBox (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0)
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)
      (cblk 0) (cblk 2))
    (hdisj01 : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 0 t) (rotCapping u (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1 y)
    (hdisj02 : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 0 t) (rotCapping u (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y)
    (hdisj012 : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y')
    (hlev01 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 1 < levelOf (chartPert (blk 0 t) (rotCapping u (Q z))))
    (hlev02 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 2 < levelOf (chartPert (blk 0 t) (rotCapping u (Q z))))
    (hdisj10 : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 1 t) (rotCapping v (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y)
    (hdisj12 : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 1 t) (rotCapping v (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y)
    (hdisj102 : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y')
    (hlev10 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 0 < levelOf (chartPert (blk 1 t) (rotCapping v (Q z))))
    (hlev12 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 2 < levelOf (chartPert (blk 1 t) (rotCapping v (Q z))))
    {δF : ℝ} (hδF : 0 < δF)
    (hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δF → ‖τ₁‖ < δF → ‖τ₂‖ < δF →
        GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)) (cblk 2) →
        GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)) (cblk 2) →
        Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z))) (cblk 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z))) (cblk 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))))
    (hsmall0 : ‖blk 0 t‖ < δF) (hsmall1 : ‖blk 1 t‖ < δF) (hsmall2 : ‖blk 2 t‖ < δF)
    (hgp0 : GoodPair (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
        (fun z : ℂ => chartPert (blk 2 t) (linPlaneChart (φ 2) lam hlam z)) (cblk 2))
    (hgp1 : GoodPair (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
        (fun z : ℂ => chartPert (blk 2 t) (linPlaneChart (φ 2) lam hlam z)) (cblk 2)) :
    (Odd (topBdryMeet CappingSpace
        (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) cblk t) 0).ncard ↔
      Odd (coreSideCount (fun z => chartPert (blk 0 t) (rotCapping u (Q z)))
          (cblk 1)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1)) ∧
      Odd (coreSideCount (fun z => chartPert (blk 0 t) (rotCapping u (Q z)))
          (cblk 2)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2))) ∧
    (Odd (topBdryMeet CappingSpace
        (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) cblk t) 1).ncard ↔
      Odd (coreSideCount (fun z => chartPert (blk 1 t) (rotCapping v (Q z)))
          (cblk 0)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0)) ∧
      Odd (coreSideCount (fun z => chartPert (blk 1 t) (rotCapping v (Q z)))
          (cblk 2)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2))) ∧
    coreSideCount (fun z => chartPert (blk 0 t) (rotCapping u (Q z)))
        (cblk 1)
        (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1)
      = CntAt (fun s p => chartPert s p) Q
          (cblk 1) (v - u) (blk 0 t, blk 1 t) ∧
    coreSideCount (fun z => chartPert (blk 1 t) (rotCapping v (Q z)))
        (cblk 0)
        (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0)
      = CntAt (fun s p => chartPert s p) Q
          (cblk 0) (u - v) (blk 1 t, blk 0 t) ∧
    Odd (coreSideCount (fun z => chartPert (blk 0 t) (rotCapping u (Q z)))
        (cblk 2)
        (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)) ∧
    Odd (coreSideCount (fun z => chartPert (blk 1 t) (rotCapping v (Q z)))
        (cblk 2)
        (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)) := by
  have hT6₀ := refTriple_topBdryMeet_zero_iff hQ φ lam hlam u v cblk (hcpos 1) (hcpos 2) t
    hM hgen0 hdisj01 hdisj02 hdisj012 hlev01 hlev02
  have hT6₁ := refTriple_topBdryMeet_zero_iff_block1 hQ φ lam hlam u v cblk (hcpos 0) (hcpos 2) t
    hM hgen1 hdisj10 hdisj12 hdisj102 hlev10 hlev12
  have hid := refTriple_blockIdent Q (refPlanePres φ lam hlam) u v cblk t
  have hmix := refTriple_mixedFactors_at hγ hQ u v φ lam hlam (cblk 2) hδF hF1
    hsmall0 hsmall1 hsmall2 hgp0 hgp1
  exact ⟨hT6₀, hT6₁, hid.1, hid.2, hmix.1, hmix.2⟩

end

end Work.Drive
