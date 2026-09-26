import Submission.Work.BoxShrink.Bubble.Corrected
import Submission.Work.BoxShrink.assemble
import Submission.Assemble
import Submission.Shrink

/-!
# The corrected residual input: the push-off at spheres in general position

The plane lemma of `PlaneLemma.lean` / `PathFree.lean` is **false**
(`Work.BoxShrink.Pinch.not_planePathLemma`, `PlaneLemmaFalse.lean`): the `hS ∧ hZ` hypotheses alone
do not suffice for a statement about an arbitrary open periodic set of the parameter plane, because
they do not forbid a *one-sided* "wall" with a **free endpoint on the slice**, which can block a
half-region while keeping it path-free.

What the box/plane setting has and the abstract plane setting does not is the **general position of
the box-sphere trace with the surface**: `Work.BoxShrink.SlicedSphere`, which is exactly the
hypothesis `hslice` that `Work.BoxShrink.CruxCore` carries (see `Submission/Work/BoxShrink/crux.lean`).
`SlicedSphere P S` is a `SphereSlicing`: finitely many pairwise disjoint **closed** curves covering
every loop of the surface in `S`, with embedded discs inside `S` and a nesting rank — in particular
the trace has no free endpoint, so the counterexample of the previous section cannot occur.

This module therefore isolates the residual in the honest form

```
Work.BoxShrink.Pinch.PushOffHalfSliced :
  ∀ P s c σ u, SlicedSphere P (sphereSet c σ s) →
    ¬ ContainsEssentialLoop (sphereSet c σ s) → ¬ ContainsEssentialLoop (sliceRegion P s c σ u) →
    BubbleHalf P s c σ u
```

* `pushOffHalf_of_slicedPushOff` : the old (stronger) interface implies this one, so this input is
  *strictly weaker* and is not refuted by the walls of `PlaneLemmaFalse.lean`;
* `cruxCore_of_pushOffHalfSliced`, `cruxStatement_of_pushOffHalfSliced`,
  `boxShrinkStatement_of_pushOffHalfSliced` and `pardon_torus_knot_distortion_of_pushOffHalfSliced`:
  the verbatim replay of the delivered chain with this input — the crux's own hypothesis `hslice`
  supplies the `SlicedSphere` argument, so nothing is lost on the way to the challenge.

Everything here is unconditional: this is the interface a future proof (or a colleague attacking the
pinch) should supply, in place of the refuted abstract plane lemma.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **The push-off at box spheres in general position.**  Pardon's Lemma 3, restricted to
configurations whose sphere trace with the surface is a `SlicedSphere` — a finite union of *closed*
curves, as in `Work.InnermostDisk.SphereSlicing`.  This is the honest form of the residual:
`hS ∧ hZ` alone is refuted as an abstract plane statement (`not_planePathLemma`), while the crux
supplies `SlicedSphere` for free. -/
def PushOffHalfSliced : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.SlicedSphere P (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u

/-- The old, stronger interface implies the sliced one (which is therefore not refuted by the walls
of `PlaneLemmaFalse.lean`). -/
theorem pushOffHalf_of_slicedPushOff (h : Work.BoxShrink.Bubble.PushOffHalf) :
    PushOffHalfSliced :=
  fun P s c σ u _ hS hZ => h P s c σ u hS hZ

/-- **The crux from the sliced push-off**: a verbatim replay of
`Work.BoxShrink.Bubble.cruxCore_of_pushOffHalf` in which the crux's own general-position hypothesis
`hslice : SlicedSphere …` is handed to the input. -/
theorem cruxCore_of_pushOffHalfSliced
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfSliced) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q := by
  intro p q
  unfold Work.BoxShrink.CruxCore
  intro hp hq hc ψ K d hd _hbound himg hsmall hcl r hr c σ hbox s hrs _hs hslice u _hu hS hU
  set P := Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph with hP
  have hs0 : 0 < s := lt_trans hr hrs
  have hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.BoxShrink.Core.not_containsEssentialLoop_sphereSet_of_slicing p q hp hq hc ψ K hd himg
      hsmall hs0 c σ hslice hcl hS
  have hnoZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) :=
    Work.BoxShrink.Core.not_containsEssentialLoop_sliceRegion p q hp hq hc ψ K hd himg hsmall hs0
      c σ u (hcleanD ψ s c σ u) hU
  have hbox' : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) :=
    Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ)
      (le_of_lt hrs) hbox
  rcases h P s c σ u hslice hnoS hnoZ hbox' with hup | hlo
  · exact Or.inr ((Work.BoxShrink.Core.containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inl ((Work.BoxShrink.Core.containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

/-- **The crux statement from the sliced push-off.** -/
theorem cruxStatement_of_pushOffHalfSliced
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfSliced) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) : ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  fun p q => ⟨hclean, cruxCore_of_pushOffHalfSliced hcleanD h p q, hae⟩

/-- **Pardon's shrinking statement from the sliced push-off.** -/
theorem boxShrinkStatement_of_pushOffHalfSliced
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfSliced) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll) : ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux (cruxStatement_of_pushOffHalfSliced hcleanD h hclean hae)

/-- **Pardon's theorem from the sliced push-off.** -/
theorem pardon_torus_knot_distortion_of_pushOffHalfSliced
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : PushOffHalfSliced) (hclean : Work.BoxShrink.CleansDiscsAll)
    (hae : Work.BoxShrink.AeSlicedAll)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Submission.theorem_of_core
    (Submission.CoreStatement_of_boxShrink (boxShrinkStatement_of_pushOffHalfSliced hcleanD h hclean hae))
    p q hp hq hc K hclass

end

end Work.BoxShrink.Pinch
