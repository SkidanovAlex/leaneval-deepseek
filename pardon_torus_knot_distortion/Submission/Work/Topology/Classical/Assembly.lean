import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.SliceInput
import Submission.Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost
import Submission.Work.Topology.Classical.PushThrough
import Submission.Work.Topology.SphereSlicing.Assembly

/-!
# Assembly: Pardon's Lemma 4.2 at the box boundary, from the classical topological input

This is the entry point of the chapter `Work.Topology.Classical`.  From the single packaged
hypothesis

```
Work.Topology.Classical.ClassicalTopology
```

— the Jordan–Schoenflies theorem on the round sphere together with the standard position of
finitely many pairwise disjoint Jordan curves on it (`JordanSchoenfliesSphere`), and the
cut-and-paste of Pardon's second innermost argument for the standard torus of revolution
(`PushThroughInnermost standard`, i.e. Alexander's theorem plus isotopy extension) — everything is
proved:

* `classicalInput_standard_of_classicalTopology` — **`ClassicalInput standard`**, the classical
  input of `Work.Topology.SphereSlicing` at the standard torus of revolution;
* `classicalInput_mapHomeomorph_of_classicalTopology` — `ClassicalInput (mapHomeomorph ψ)` for
  every homeomorphism `ψ` of `ℝ³` (the classical input is an invariant of the ambient
  homeomorphism class, `classicalInput_map_homeomorph_iff`);
* `pardonPLInputOnGeneralPosition_of_classicalTopology` — the general-position PL input;
* `mustbeinessentialBox_of_classicalTopology` — **Pardon's Lemma 4.2 at the box boundary** for the
  tori `F = ψ(F_standard)` of the challenge, with the intersection count in the parameter form in
  which Pardon's sweep produces it and `I(F,β) = min p q`: this is exactly
  `Work.Topology.SphereSlicing.mustbeinessentialBox_of_classicalInput_standard` with its
  hypothesis `ClassicalInput standard` discharged.

This is the statement that `Work.BoxBubble.mustbeinessentialBox` needs, so with this chapter
Pardon's Lemma 4.2 — and hence, through `Work.BoxShrink.boxShrink` and
`Submission.CoreStatement_of_boxShrink`, Pardon's Theorem 1.1 — is unconditional in the two
classical facts isolated in `Work.Topology.Classical.Defs`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-- **The classical input of `Work.Topology.SphereSlicing` at the standard torus of revolution**,
from the packaged classical input of this chapter. -/
theorem classicalInput_standard_of_classicalTopology (h : ClassicalTopology) :
    Work.Topology.SphereSlicing.ClassicalInput standard :=
  ⟨sliceInput_standard_of_jordanSchoenflies h.1,
    cleanOneCurve_of_pushThroughInnermost h.2⟩

/-- **The classical input of `Work.Topology.SphereSlicing` at the standard torus, from the
primitive classical facts**: Jordan–Schoenflies on the round sphere, the existence of an innermost
intersection curve (Jordan separation in the disc) and the surgery along the sub-disc it bounds
(Alexander's theorem plus isotopy extension). -/
theorem classicalInput_standard_of_decomposed (h₁ : JordanSchoenfliesSphere)
    (h₂ : InnermostCurveExists standard) (h₃ : CutsAlongSubdisc standard) :
    Work.Topology.SphereSlicing.ClassicalInput standard :=
  classicalInput_standard_of_classicalTopology (classicalTopology_of_decomposed h₁ h₂ h₃)

/-- **The classical input at the tori of the challenge**, `P = mapHomeomorph ψ` for a
homeomorphism `ψ` of `ℝ³`. -/
theorem classicalInput_mapHomeomorph_of_classicalTopology (ψ : R3 ≃ₜ R3)
    (h : ClassicalTopology) :
    Work.Topology.SphereSlicing.ClassicalInput (ParamTorus.mapHomeomorph ψ) :=
  (Work.Topology.SphereSlicing.classicalInput_map_homeomorph_iff ψ).mpr
    (classicalInput_standard_of_classicalTopology h)

/-- **The cut-and-paste at the tori of the challenge**: the classical input is an invariant of the
ambient homeomorphism class, so the single cut-and-paste for the standard torus
(`PushThroughInnermost standard`) gives `CleanOneCurve (mapHomeomorph ψ)` for every homeomorphism
`ψ` of `ℝ³`. -/
theorem cleanOneCurve_mapHomeomorph_of_classicalTopology (ψ : R3 ≃ₜ R3)
    (h : ClassicalTopology) :
    Work.Topology.SphereSlicing.CleanOneCurve (ParamTorus.mapHomeomorph ψ) :=
  (Work.Topology.SphereSlicing.cleanOneCurve_map_homeomorph_iff ψ).mpr
    (cleanOneCurve_of_pushThroughInnermost h.2)

/-- The repaired PL input of Pardon's first innermost argument, from the classical input of this
chapter (the version with the transversality hypothesis built in). -/
theorem pardonPLInputOnGeneralPosition_of_classicalTopology (h : ClassicalTopology) :
    Work.Topology.SphereSlicing.PardonPLInputOnGeneralPosition standard :=
  Work.Topology.SphereSlicing.pardonPLInputOnGeneralPosition_of_classicalInput
    (classicalInput_standard_of_classicalTopology h)

/-- **The `hclean` hypothesis of `Work.BoxBubble.mustbeinessentialBox`, discharged from the
classical input of this chapter.**

`Work.BoxBubble.mustbeinessentialBox` is stated with

```
hclean : CleansInSphere (ParamTorus.mapHomeomorph ψ) {y | boxNorm c σ y = s}
```

i.e. Pardon's geometric hypothesis at the box boundary: every essential loop of `ψ(F_standard)`
lying in the box boundary can be replaced by a simple essential loop in it bounding a disc whose
interior misses the torus.  That hypothesis is *derived* here from the classical input
`ClassicalTopology` and the general position of the box boundary with the torus: Pardon's first
innermost input at the box boundary comes from `SliceInput` (Jordan–Schoenflies, via
`sliceInput_mapHomeomorph_of_jordanSchoenflies`), and Pardon's second step is Pardon's cut-and-paste
iterated (`cleansDiscs_of_cleanOneCurve` composed with
`cleanOneCurve_mapHomeomorph_of_classicalTopology`).

So, together with `Work.BoxBubble.encard_range_inter_le_param`, the sibling's
`Work.BoxBubble.mustbeinessentialBox` is discharged: its `hclean` is supplied by this theorem and
its conclusion is `mustbeinessentialBox_of_classicalTopology` below (the box boundary is
definitionally `{y | boxNorm c σ y = s}`). -/
theorem cleansInSphere_mapHomeomorph_BoxSphere_of_classicalTopology (h : ClassicalTopology)
    (ψ : R3 ≃ₜ R3) {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hT : Work.Topology.SphereSlicing.TransverseSphere (ParamTorus.mapHomeomorph ψ)
      (Work.Topology.SphereSlicing.BoxSphere s c σ)) :
    CleansInSphere (ParamTorus.mapHomeomorph ψ)
      (Work.Topology.SphereSlicing.BoxSphere s c σ) :=
  Work.InnermostDisk.cleansInSphere_of_inputs
    (Work.Topology.SphereSlicing.innermostDiscInput_of_sliceInput
      (sliceInput_mapHomeomorph_of_jordanSchoenflies ψ h.1)
      (Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere hs c σ) hT)
    (Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
      (cleanOneCurve_mapHomeomorph_of_classicalTopology ψ h))

/-- **Pardon's Lemma 4.2 at the box boundary, from the classical topological input.**

`ψ` is a homeomorphism of `ℝ³`, `F = ψ(F_standard)` the image of the standard torus, `β` the image
of the standard `(p,q)`-curve (`I(F,β) = min p q`), `K` a knot with the same image as `β`, and
`S = ∂PBox s c σ = {y | boxNorm c σ y = s}` the boundary sphere of Pardon's box, in general
position with respect to `F` (`hT`).  If `S` meets `K` in fewer than `min p q` points, counted in
the fundamental period of the parameter (`hcount`, the form produced by Pardon's sweep), then `S`
contains no essential loop of `F`.

This is `Work.Topology.SphereSlicing.mustbeinessentialBox_of_classicalInput_standard` with its
hypothesis `ClassicalInput standard` supplied by this chapter, and it is exactly the statement that
`Work.BoxBubble.mustbeinessentialBox` consumes. -/
theorem mustbeinessentialBox_of_classicalTopology (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : R3 ≃ₜ R3) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hT : Work.Topology.SphereSlicing.TransverseSphere (ParamTorus.mapHomeomorph ψ)
      (Work.Topology.SphereSlicing.BoxSphere s c σ))
    (h : ClassicalTopology)
    (hcount : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞)) :
    ¬ (ParamTorus.mapHomeomorph ψ).ContainsEssentialLoop
      (Work.Topology.SphereSlicing.BoxSphere s c σ) :=
  Work.Topology.SphereSlicing.mustbeinessentialBox_of_classicalInput_standard
    p q hp hq hc ψ K himg hs c σ hT (classicalInput_standard_of_classicalTopology h) hcount

/-- The same conclusion in the form of Pardon's reduction of the whole chapter: no essential loop
of the torus `ψ(F_standard)` lies in the box boundary. -/
theorem not_containsEssentialLoop_BoxSphere_of_classicalTopology (p q : ℕ) (hp : 0 < p)
    (hq : 0 < q) (hc : Nat.Coprime p q) (ψ : R3 ≃ₜ R3) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hT : Work.Topology.SphereSlicing.TransverseSphere (ParamTorus.mapHomeomorph ψ)
      (Work.Topology.SphereSlicing.BoxSphere s c σ))
    (h : ClassicalTopology)
    (hcount : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞)) :
    ¬ (ParamTorus.mapHomeomorph ψ).ContainsEssentialLoop
      (Work.Topology.SphereSlicing.BoxSphere s c σ) :=
  mustbeinessentialBox_of_classicalTopology p q hp hq hc ψ K himg hs c σ hT h hcount

/-! ## The interface in the vocabulary of `Work.InnermostDisk`

For callers working at the level of Pardon's own inputs rather than that of the box, the same
classical input also supplies the geometric hypothesis of Pardon's Lemma 4.2
(`Work.InnermostDisk.CleansInSphere`) at *every* embedded sphere in general position. -/

/-- **Pardon's geometric input at an embedded sphere in general position**, from the classical
input of this chapter: every essential loop of the standard torus lying in `S` can be replaced by a
simple essential loop in `S` bounding a disc whose interior is disjoint from `F`. -/
theorem cleansInSphere_standard_of_classicalTopology (h : ClassicalTopology) {S : Set R3}
    (hS : IsEmbeddedSphere S) (hT : Work.Topology.SphereSlicing.TransverseSphere standard S) :
    CleansInSphere standard S :=
  Work.InnermostDisk.cleansInSphere_of_inputs
    (Work.Topology.SphereSlicing.innermostDiscInput_of_sliceInput
      (sliceInput_standard_of_jordanSchoenflies h.1) hS hT)
    (Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
      (cleanOneCurve_of_pushThroughInnermost h.2))

/-- **Pardon's Lemma 4.2 for the standard torus of revolution**, in the vocabulary of
`Work.InnermostDisk`: an embedded sphere `S` in general position with `F` meeting `β` in fewer
than `I(F,β)` points contains no essential loop of `F`. -/
theorem mustbeinessential_standard_of_classicalTopology (h : ClassicalTopology)
    (β : ClosedCurve standard) {S : Set R3} (hS : IsEmbeddedSphere S)
    (hT : Work.Topology.SphereSlicing.TransverseSphere standard S)
    (hβS : Set.encard (Set.range β.γ ∩ S) < pardonsI standard β) :
    ∀ α : ClosedCurve standard, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential standard α :=
  Work.InnermostDisk.mustbeinessential_of_cleansInSphere standard β S
    (cleansInSphere_standard_of_classicalTopology h hS hT) hβS

end

end Work.Topology.Classical
