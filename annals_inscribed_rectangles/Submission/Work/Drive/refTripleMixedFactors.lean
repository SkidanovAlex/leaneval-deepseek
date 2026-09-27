import Mathlib
import Submission.Work.Drive.refMixedBox
import Submission.Work.Drive.mixedSweep_injOn
import Submission.Work.Drive.refTripleProducerDefs

/-!
# The two mixed factors `(F1)` of the `hn2` reference triple, in the box form and with **no**
perturbation-independence hypothesis

`Work.Drive.exists_delta_odd_coreSideCount_mixed` (`Drive/refMixedBox.lean`) turns the geometric `(F1)`
of `Work.Drive.exists_delta_odd_coreSideCountPt_mixed` into the **box** form the transport `T6`
consumes, at the price of the sweep's injectivity on the box at the parameter.  That injectivity is
`Work.Drive.mixedSweep_injOn` (`Drive/mixedSweep_injOn.lean`) for the design's own data
(perturbed linear reference plane, level band `c₂ < lam / 2`, small perturbation), so this module
removes it and states the final interface:

* **`Work.Drive.refTriple_mixedFactors`** — from the configuration chart `Q` and its level band alone
  there are a *reference functional* `φ` and a radius `δ > 0` such that, for **every** perturbation
  `τ₀, τ₁, τ₂` of norm below `δ` (`‖τ₂‖ < log 2`), if the two *mixed pairs*
  `(chartPert τ₀ ∘ rotCapping u₀ ∘ Q, chartPert τ₂ ∘ linPlaneChart φ lam)`,
  `(chartPert τ₁ ∘ rotCapping u₁ ∘ Q, chartPert τ₂ ∘ linPlaneChart φ lam)`
  are `Work.Drive.GoodPair`s at the level `c₂`, then the two mixed **box** counts
  `Odd (coreSideCount …)` — the conjuncts `(F1)` of `Work.Drive.refTripleAt_blockT6At` — hold.

Every hypothesis of the conclusion is now one the reference-triple producer can produce *at the
parameter it chooses*: `φ` is the generic functional of the `(F1)` lane (`F1_GENERICITY_RESOLUTION.md`),
the smallness of `τ` is the Sard's, and the two `GoodPair`s are open-dense conditions on `t`
(`Work.Drive.mixedGoodPairs_openDense`), to be added to the open dense set of the producer's enhanced
Sard step `Work.Drive.exists_meet3Hyp_opens`.  The producer's remaining obligation for `(F1)` is
therefore *bookkeeping*: choose `φ` generic **first** (the common `φ` of the reference plane and of the
genericity), and add the two mixed-pair goodnesses to the Sard's `Pcond` list.
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false

/-- **The two mixed factors `(F1)` of the `hn2` reference triple, in the box form.**  Same `φ` and
radius as `Work.Drive.exists_delta_odd_coreSideCountPt_mixed`; the only remaining hypotheses at the
parameter are the two mixed pairs' `GoodPair`s. -/
theorem refTriple_mixedFactors {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (u₀ u₁ : UnitAddCircle)
    {c β lam c₂ : ℝ} (hc : 0 < c) (hβpos : 0 < β) (hlampos : 0 < lam) (hc₂ : 0 < c₂)
    (hc₂c : c₂ < c) (hβlam : β < lam) (hc₂lam : c₂ < lam / 2)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) :
    ∃ (φ : Eucl 3 ≃L[ℝ] Eucl 3) (δ : ℝ), 0 < δ ∧
      ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δ → ‖τ₁‖ < δ → ‖τ₂‖ < δ → ‖τ₂‖ < Real.log 2 →
        GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u₀ (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z)) c₂ →
        GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping u₁ (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z)) c₂ →
        Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u₀ (Q z))) c₂
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z)))) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping u₁ (Q z))) c₂
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z)))) := by
  obtain ⟨φ, δ, hδpos, hmain⟩ :=
    exists_delta_odd_coreSideCount_mixed hγ hQ u₀ u₁ hc hβpos hlampos hc₂ hc₂c hβlam hclow hβ
  refine ⟨φ, δ, hδpos, ?_⟩
  intro τ₀ τ₁ τ₂ h₀ h₁ h₂ hτ₂ hgp₀ hgp₁
  obtain ⟨hA, hB⟩ := hmain τ₀ τ₁ τ₂ h₀ h₁ h₂
  have hsweep := mixedSweep_injOn (φ := φ) (lam := lam) hlampos hc₂ hc₂lam hτ₂
  exact ⟨hA hgp₀ hsweep, hB hgp₁ hsweep⟩


/-- **The `(F1)` conjuncts of `Work.Drive.refTripleAt_blockT6At`, at one parameter.**  The two mixed
factors of the reference triple in the exact form of the last two conjuncts of
`Work.Drive.refTripleAt_blockT6At` (`Drive/hn2_refTripleAt_producer.lean`), from

* the parametric oddness `hF1` produced by `Work.Drive.refTriple_mixedFactors` at the *same* reference
  functional `φ₃` and radius `δF` (the producer chooses `φ₃` generic first), and
* the two mixed pairs' `GoodPair`s at `t` (`Work.Drive.mixedGoodPairs_openDense`).

The identification `refBlock (fun s p => chartPert s p) Q (refPlanePres φ₃ lam hlam) u v t 2
= fun y => chartPert (blk 2 t) (diskPlane (linPlaneChart (φ₃ 2) lam hlam) y)` is definitional. -/
theorem refTriple_mixedFactors_at {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (u v : UnitAddCircle) (φ₃ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (c₂ : ℝ) {δF : ℝ} (hδF : 0 < δF)
    (hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δF → ‖τ₁‖ < δF → ‖τ₂‖ < δF →
        GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ₃ 2) lam hlam z)) c₂ →
        GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ₃ 2) lam hlam z)) c₂ →
        Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z))) c₂
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ₃ 2) lam hlam z)))) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z))) c₂
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ₃ 2) lam hlam z)))))
    {t : EuclideanSpace ℝ (Fin 12)}
    (h₀ : ‖blk 0 t‖ < δF) (h₁ : ‖blk 1 t‖ < δF) (h₂ : ‖blk 2 t‖ < δF)
    (hgp₀ : GoodPair (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
        (fun z : ℂ => chartPert (blk 2 t) (linPlaneChart (φ₃ 2) lam hlam z)) c₂)
    (hgp₁ : GoodPair (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
        (fun z : ℂ => chartPert (blk 2 t) (linPlaneChart (φ₃ 2) lam hlam z)) c₂) :
    Odd (coreSideCount (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z))) c₂
        (refBlock (fun s p => chartPert s p) Q (refPlanePres φ₃ lam hlam) u v t 2)) ∧
    Odd (coreSideCount (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z))) c₂
        (refBlock (fun s p => chartPert s p) Q (refPlanePres φ₃ lam hlam) u v t 2)) := by
  obtain ⟨hA, hB⟩ := hF1 (blk 0 t) (blk 1 t) (blk 2 t) h₀ h₁ h₂ hgp₀ hgp₁
  exact ⟨hA, hB⟩

end

end Work.Drive
