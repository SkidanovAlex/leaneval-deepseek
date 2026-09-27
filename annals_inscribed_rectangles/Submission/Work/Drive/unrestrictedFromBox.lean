import Mathlib
import Submission.Work.Drive.endTripleRegUnrestricted
import Submission.Work.Drive.boxRegDefs
import Submission.Work.Drive.endTripleRegRefTriple

/-!
# Box-restricted end data is *unrestricted*, for affinely invariant presentations

`Work.Drive.BoxEndTripleReg`/`Work.Drive.BoxPairReg` (`Drive/boxRegDefs.lean`) are the box-restricted
class-level regularities of the ends clause, and they are what the sweeps' `Meet3Hyp` and the
loop-versus-chain producers supply.  Until now the passage to the *unrestricted*
`Work.Drive.EndTripleReg`/`Work.Drive.PairReg` of the consumers went through the extra hypothesis that
every common-value triple already lies in the box (`Work.Drive.endTripleReg_of_boxEndTripleReg`) — a
hypothesis that is *false* for the design's presentations, whose class maps are defined on all of
`ℝ²`.

This file removes it for every presentation that is invariant under the symmetries
`x ↦ (ε i * x i + 2 m i)` (`ε i = ±1`) of the parameter square — which is the case for *all* the
design's presentations, since they factor through `foldBox` (`Work.Drive.diskPlane_affRep`,
`Work.Drive.rotPresentation_affRep`, `Work.Drive.blockPlane_affRep`,
`Work.Drive.refBlock_affRep`).

The mechanism is `Work.Drive.transfer_mfderiv_class_of_affRep`: an affine symmetry with invertible
linear part along which the class map is invariant preserves the injectivity and the range of the
manifold derivative.  Hence moving a common-value triple into the box does not change the ranges, and
the box-restricted data transfer.

Deliverables:

* `Work.Drive.pairReg_of_boxPairReg_affRep` — `BoxPairReg → PairReg`;
* `Work.Drive.endTripleReg_of_boxEndTripleReg_affRep` — `BoxEndTripleReg → EndTripleReg`;
* `Work.Drive.pairReg_diskPlane_of_box`, `Work.Drive.endTripleReg_diskPlane_of_box` — the instances at
  `diskPlane` presentations (hence at `rotPresentation` and at the reference plane);
* `Work.Drive.endTripleReg_refBlock_of_box` — the instance at the `hn2` node's perturbed blocks.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartUB :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-! ## 1. The pair regularity -/

/-- **The box-restricted pair regularity is the unrestricted one, for affinely invariant
presentations.** -/
theorem pairReg_of_boxPairReg_affRep
    (P Q : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop Q)
    (hPinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P (affRep e mm y) = P y)
    (hQinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), Q (affRep e mm y) = Q y)
    (h : Work.Drive.BoxPairReg (Work.Drive.planeClassMap P) (Work.Drive.planeClassMap Q)) :
    Work.Drive.PairReg (Work.Drive.planeClassMap P) (Work.Drive.planeClassMap Q) := by
  intro y y' hyy
  obtain ⟨e, mm, hrep⟩ := exists_affRep_mem_unitBox y
  obtain ⟨e', mm', hrep'⟩ := exists_affRep_mem_unitBox y'
  have hy : Work.Drive.planeClassMap P (affRep e mm y) = Work.Drive.planeClassMap P y :=
    congrArg (fun p => (Work.Drive.cappingSpaceHomeoProj p).2) (hPinv e mm hrep.1 y)
  have hy' : Work.Drive.planeClassMap Q (affRep e' mm' y') = Work.Drive.planeClassMap Q y' :=
    congrArg (fun p => (Work.Drive.cappingSpaceHomeoProj p).2) (hQinv e' mm' hrep'.1 y')
  have hbox := h (affRep e mm y) (affRep e' mm' y')
    (affRep_mem_unitBox hrep.2) (affRep_mem_unitBox hrep'.2)
    (by rw [hy, hy']; exact hyy)
  have tP := transfer_mfderiv_class_of_affRep P hP e mm hrep.1 (hPinv e mm hrep.1) y
  have tQ := transfer_mfderiv_class_of_affRep Q hQ e' mm' hrep'.1 (hQinv e' mm' hrep'.1) y'
  rw [tP.2, tQ.2]
  exact hbox

/-! ## 2. The end-triple regularity -/

/-- **The box-restricted end-triple regularity is the unrestricted one, for affinely invariant
presentations.** -/
theorem endTripleReg_of_boxEndTripleReg_affRep
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), P k (affRep e mm y) = P k y)
    (h : Work.Drive.BoxEndTripleReg (Work.Drive.planeClassMap (P 0))
      (Work.Drive.planeClassMap (P 1)) (Work.Drive.planeClassMap (P 2))) :
    Work.Drive.EndTripleReg (Work.Drive.planeClassMap (P 0))
      (Work.Drive.planeClassMap (P 1)) (Work.Drive.planeClassMap (P 2)) := by
  intro y₀ y₁ y₂ h01 h02
  let Y : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![y₀, y₁, y₂]
  have hrep : ∀ k : Fin 3, ∃ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ),
      (∀ i, e i = 1 ∨ e i = -1) ∧
        ∀ i, e i * (Y k) i + 2 * (mm i : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun k => exists_affRep_mem_unitBox (Y k)
  choose e mm hrep' using hrep
  have hsymm : ∀ k : Fin 3, Work.Drive.planeClassMap (P k) (affRep (e k) (mm k) (Y k))
      = Work.Drive.planeClassMap (P k) (Y k) :=
    fun k => congrArg (fun p => (Work.Drive.cappingSpaceHomeoProj p).2)
      (hinv (e k) (mm k) (hrep' k).1 k (Y k))
  have hbox : Work.Drive.BoxPt (affRep (e 0) (mm 0) (Y 0)) (affRep (e 1) (mm 1) (Y 1))
      (affRep (e 2) (mm 2) (Y 2)) := by
    intro k
    fin_cases k <;> exact affRep_mem_unitBox (hrep' _).2
  have hmain := h (affRep (e 0) (mm 0) (Y 0)) (affRep (e 1) (mm 1) (Y 1))
    (affRep (e 2) (mm 2) (Y 2)) hbox
    (by rw [hsymm 0, hsymm 1]; exact h01)
    (by rw [hsymm 0, hsymm 2]; exact h02)
  have htr : ∀ k : Fin 3,
      (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k)) (Y k)).range
        = (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k))
            (affRep (e k) (mm k) (Y k))).range :=
    fun k => (transfer_mfderiv_class_of_affRep (P k) (hP k) (e k) (mm k) (hrep' k).1
      (hinv (e k) (mm k) (hrep' k).1 k) (Y k)).2
  have htr' : ∀ k : Fin 3,
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k))
          (affRep (e k) (mm k) (Y k)))
        ↔ Function.Injective
            (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P k)) (Y k)) :=
    fun k => (transfer_mfderiv_class_of_affRep (P k) (hP k) (e k) (mm k) (hrep' k).1
      (hinv (e k) (mm k) (hrep' k).1 k) (Y k)).1
  refine ⟨(htr' 0).mp hmain.1, (htr' 1).mp hmain.2.1, (htr' 2).mp hmain.2.2.1, ?_⟩
  show (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 0)) (Y 0)).range ⊓
      (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 1)) (Y 1)).range ⊓
      (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (P 2)) (Y 2)).range = ⊥
  rw [htr 0, htr 1, htr 2]
  exact hmain.2.2.2

/-! ## 3. The instances at the design's presentations -/

/-- **`PairReg` for two `diskPlane` presentations, from the box-restricted version** (hence for
`rotPresentation` and for the reference plane, which are `diskPlane` presentations). -/
theorem pairReg_diskPlane_of_box (Q R : ℂ → Work.Drive.CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (Work.Drive.diskPlane Q))
    (hR : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (Work.Drive.diskPlane R))
    (h : Work.Drive.BoxPairReg (Work.Drive.planeClassMap (Work.Drive.diskPlane Q))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane R))) :
    Work.Drive.PairReg (Work.Drive.planeClassMap (Work.Drive.diskPlane Q))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane R)) :=
  pairReg_of_boxPairReg_affRep (Work.Drive.diskPlane Q) (Work.Drive.diskPlane R) hQ hR
    (fun e mm he _ => diskPlane_affRep he mm Q _) (fun e mm he _ => diskPlane_affRep he mm R _) h

/-- **`EndTripleReg` for a triple of `diskPlane` presentations, from the box-restricted version.** -/
theorem endTripleReg_diskPlane_of_box (Q : Fin 3 → ℂ → Work.Drive.CappingSpace)
    (hQ : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (Work.Drive.diskPlane (Q k)))
    (h : Work.Drive.BoxEndTripleReg (Work.Drive.planeClassMap (Work.Drive.diskPlane (Q 0)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Q 1)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Q 2)))) :
    Work.Drive.EndTripleReg (Work.Drive.planeClassMap (Work.Drive.diskPlane (Q 0)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Q 1)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Q 2))) :=
  endTripleReg_of_boxEndTripleReg_affRep (fun k => Work.Drive.diskPlane (Q k)) hQ
    (fun e mm he k _ => diskPlane_affRep he mm (Q k) _) h

/-- **`EndTripleReg` for the `hn2` node's perturbed reference blocks, from the box-restricted
version.** -/
theorem endTripleReg_refBlock_of_box (Ξ : Eucl 3 → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (hQsm : Work.Drive.IsSmoothChart Q)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12))
    (h : Work.Drive.BoxEndTripleReg
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 0))
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 1))
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 2))) :
    Work.Drive.EndTripleReg
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 0))
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 1))
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 2)) :=
  endTripleReg_of_boxEndTripleReg_affRep
    (fun k => refBlock Ξ Q (refPlanePres φ lam hlam) u v t k)
    (refBlock_contMDiff Q hQsm Ξ hΞ φ lam hlam u v t)
    (fun e mm he k _ => refBlock_affRep Ξ Q φ lam hlam u v t he mm k _) h

end

end Work.Drive
