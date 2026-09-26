import Submission.Work.BoxShrink.crux
import Submission.Work.BoxShrink.Core.Bubble.Persistence
import Submission.Work.BoxShrink.Core.Counting.Sphere
import Submission.Work.BoxShrink.Core.Counting.Disc

/-!
# The crux of Pardon's shrinking step, from the bubble input

`Submission/Work/BoxShrink/crux.lean` splits the remaining content of Pardon's shrinking step into
three independent inputs (`Work.BoxShrink.CruxStatement = CleansDiscsAll ∧ CruxCore ∧
AeSlicedAll`).  The piece proved here is the **double-bubble core** `Work.BoxShrink.CruxCore`,
under the two hypotheses collected in `Work.BoxShrink.Core.BubbleInput`:

* the classical (planar) innermost-disc input at the flat disc cut out of the box by the plane;
* Pardon's double bubble in the local-model form `Work.BoxShrink.Core.BubbleSweep`.

Everything else is proved.  Two of Pardon's inputs are supplied *inside* `CruxCore` itself by its
own hypotheses: the general position of the swept sphere (`Work.BoxShrink.SlicedSphere`, i.e.
`Nonempty (Work.InnermostDisk.SphereSlicing P {y | boxNorm c σ y = s})`) and the cut-and-paste step
for the surface (`Work.InnermostDisk.CleansDiscs`); together they give the classical innermost-disc
input `CleansInSphere` at the boundary sphere (see
`Work.BoxShrink.Core.cleansInSphere_of_slicedSphere_and_cleansDiscs`).  The rest is the argument:

* the two intersection counts produced by the sweep (`Work.BoxSweep.sweep`) give, through the two
  innermost-disc inputs, that the boundary sphere `{boxNorm c σ · = s}` and the slicing disc
  `PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}` carry no essential loop
  (`Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing`,
  `Work.BoxShrink.Core.not_containsEssentialLoop_sliceRegion`);
* the essential loop of `F ∩ PBox r c σ` lies in the larger region `F ∩ PBox s c σ` (`r < s`), so
  that region contains an essential loop;
* Pardon's double bubble carries that loop to one of the two half-regions
  (`Work.BoxShrink.Core.containsEssentialLoop_half_of_bubbleSweep`), which is the conclusion of
  `Work.BoxShrink.CruxCore`, by `containsEssentialLoop_upperRegion_iff` /
  `containsEssentialLoop_lowerRegion_iff`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Core

noncomputable section

/-- **The double-bubble core from the bubble input.** -/
theorem cruxCore_of_bubbleInput (hin : BubbleInput) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q := by
  intro p q
  unfold Work.BoxShrink.CruxCore
  intro hp hq hc ψ K d hd _hbound himg hsmall hcl r hr c σ hbox s hrs _hs hslice u _hu hS hU
  set P := Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph with hP
  have hs0 : 0 < s := lt_trans hr hrs
  -- the sweep's two counts make the two cut sets inessential
  have hnoS : ¬ P.ContainsEssentialLoop (sphereSet c σ s) :=
    not_containsEssentialLoop_sphereSet_of_slicing p q hp hq hc ψ K hd himg hsmall hs0 c σ
      hslice hcl hS
  have hnoZ : ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) :=
    not_containsEssentialLoop_sliceRegion p q hp hq hc ψ K hd himg hsmall hs0 c σ u
      (hin.cleansInDisc ψ s c σ u) hU
  -- the double bubble, and the essential loop inside the box of size `s`
  have hB : BubbleSweep P s c σ u := hin.bubble P s c σ u hnoS hnoZ
  have hbox' : P.ContainsEssentialLoop (boxRegion P s c σ) :=
    containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  rcases containsEssentialLoop_half_of_bubbleSweep (P := P) hB hbox' with hup | hlo
  · exact Or.inr ((containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inl ((containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

/-- **The double-bubble core, with the hypotheses of the bubble input unpacked.** -/
theorem cruxCore_of_hypotheses
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (cutDisc s c σ u))
    (hbubble : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
      (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) → BubbleSweep P s c σ u) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_bubbleInput ⟨hcleanD, hbubble⟩

/-- **The requested form of the deliverable**: `Work.BoxShrink.CruxStatement` for all `p, q`, from
the bubble input together with the two classical inputs of the sibling module
(`Work.BoxShrink.CleansDiscsAll`, the cut-and-paste, and `Work.BoxShrink.AeSlicedAll`, the
almost-everywhere general position of the box-norm level sets).  The remaining hypotheses are
exactly the fields of `Work.BoxShrink.Core.BubbleInput`; see
`Submission/Work/BoxShrink/Core/README.md`. -/
theorem crux_of_bubbleInput (hin : BubbleInput) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q := by
  intro p q
  exact ⟨hclean, cruxCore_of_bubbleInput hin p q, hae⟩

/-- **The double-bubble core from the *classical* form of the disc input.**

Here the planar innermost input at the flat disc is not assumed in the `CleansInSphere` form but
derived, in general position, from `SliceData` and the single cut-and-paste `CleanOneCurve` (the
vocabulary of the sibling chapter `Work.Topology.SphereSlicing`). -/
theorem cruxCore_of_sliceData
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SlicedDisc (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (cutDisc s c σ u))
    (hcl : ∀ (ψ : Submission.Diffeo),
      Work.Topology.SphereSlicing.CleanOneCurve
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph))
    (hbubble : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
      (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) → BubbleSweep P s c σ u) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_hypotheses
    (fun ψ s c σ u => cleansInSphere_of_slicedDisc_and_cleanOneCurve (P :=
      Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (hdisc ψ s c σ u) (hcl ψ))
    hbubble

/-- **The double-bubble core from the *physical* form of the bubble input.**

Here the double bubble is supplied as a family of regions with the local models of the library's
`Work.SurgeryInvariance.Sweep` (between exceptional parameters the region is moved by an ambient
isotopy of `ℝ³` preserving `F`; at an exceptional parameter it gains or loses the interior of an
embedded disc of `F`).  That datum is stronger than `BubbleInput.bubble` — it is converted with
`Work.SurgeryInvariance.Sweep.toLoops` — so the reduction is insensitive to which of the two local
model formulations the geometry delivers. -/
theorem cruxCore_of_physicalInput (hin : PhysicalBubbleInput) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_hypotheses hin.cleansInDisc fun P s c σ u hS hZ =>
    ⟨(hin.bubbleSweep P s c σ u hS hZ).choose.toLoops,
      (hin.bubbleSweep P s c σ u hS hZ).choose_spec.1,
      (hin.bubbleSweep P s c σ u hS hZ).choose_spec.2⟩

/-- The same, under the name requested by the deliverable. -/
theorem crux (hin : BubbleInput) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  crux_of_bubbleInput hin hclean hae

end

end Work.BoxShrink.Core
