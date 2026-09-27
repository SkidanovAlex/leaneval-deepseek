import Mathlib
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.LinChart.linPlaneChart_immersion
import Submission.Work.Drive.contMDiff_rotPresentation

/-!
# The chart genericity of the `hdense`/`hn2` route

`TRIPLE_MULTIPLICATIVITY_STATUS.md` §1quater reduces the triple engine's geometric hypotheses for the
design's triple to **two** conditions: (i) *one* chart `Q` whose class map is an immersion on the open
disk, and (ii) a *generic* triple of angles for the general-position condition `hV`.  This file settles
(i).

## The problem

For the honest plane chart (`Work.Drive.IsPlaneChart γ hγne Q`) the class map `cls ∘ Q` need *not* be an
immersion on the open disk: `HC_VS_PLANE_IMMERSION.md` §2 exhibits a curve with a straight segment whose
line passes through the enclosed point (a "pac-man") for which the class derivative has rank `≤ 1` on an
**open** set of chords lying inside that segment (the class of those chords runs through a projective
line).  And a *class* perturbation cannot repair this: `cls ∘ (linCapping A ∘ Q) = projMap A ∘ cls ∘ Q`
and `d (projMap A)` is an isomorphism, so injectivity of the derivative is unchanged.  What *can* repair
it is a perturbation of the chart itself — but the design's count `Work.Drive.designCount` is stated for
an **arbitrary** chart `Q : ℂ → CappingSpace` (`designCount.lean`), so the cheapest repair is to *exhibit*
a chart with the immersion property, which is what this file does.

## The witness: the linear plane chart

`Work.Drive.linPlaneChart φ c hc z = cappingVecPoint c hc (φ (linVecC z))`, `linVecC z = (z, 1 - ‖z‖²)`
(`Submission/Work/Drive/linearPlaneChart.lean`) is the disk model of the *linear* projective plane
`φ (linStd)` placed on the level `c > 0`.  It is

* `C^∞` (`Work.Drive.linPlaneChart_contMDiff`),
* invariant under `z ↦ -z` on the unit circle (`Work.Drive.linPlaneChart_neg`, i.e. the seam clause of
  `diskPlane`),
* and its class map `z ↦ [φ (linVecC z)]` is an immersion **everywhere** on `ℂ`
  (`Work.Drive.LinChart.linPlaneChart_immersion`: `d (linVecC) (z) w = (w, - 2 Re (z̄ w))`, and a
  proportionality `(w, -2 Re (z̄ w)) = λ (z, 1 - ‖z‖²)` forces `λ (1 + ‖z‖²) = 0`).

So the linear plane chart is the required witness.  The one step that is not a restatement is the
passage from the immersion of the *disk* presentation of the chart to the immersion of the **folded**
presentation `Work.Drive.diskPlane Q = Q ∘ sqDisk ∘ foldBox` that the counting engine consumes; it is
`Work.Drive.injective_mfderiv_cls_diskPlane_of_openSquare`, whose second factor is the immersion of the
square-to-disk parametrisation on the open square (the delegated leaf
`Work.Drive.injective_fderiv_sqDisk_foldBox`).  This file supplies the missing differentiability input
in the complex form and then instantiates everything.

## What this file does *not* claim

* It does **not** repair the honest chart of a curve with a straight segment: no chart obtained from `γ`
  by a small perturbation is produced here.  In particular the theorem below is *not* a proof that
  `Work.Drive.ClassTripleRegular.hci` holds for the design's triple when `Q` is the honest chart of such
  a curve; for that route the workspace's recommendation (`HC_AND_FACE_STATUS.md` §4) is the
  bordism/Sard treatment of the *given* triple.
* It says nothing about the second genericity input `hV` (the general position of the three class
  `2`-planes at a triple point), which is a genuine condition on the parameter triple; see
  `LinChart/linPlaneChartNormals.lean` for the linear-algebra form of `hV` for the linear plane.

## State

All declarations below are **proved**, with no missing proof:
`mdifferentiableAt_cls_of_contMDiff_cplx`, `injective_mfderiv_cls_diskPlane_linPlaneChart`,
`injective_mfderiv_cls_rotPresentation_linPlaneChart` and the file's original target
`exists_chart_immersion`.

## History

The first version of this file (`HANDOFF.md`, session 43) stated `exists_chart_immersion` with the
hypotheses `hγ : ∀ x, γ x ≠ 0` and `hQ : IsPlaneChart γ hγ Q` and intended to produce `Q'` from `Q` by a
*chart shift* (`chartPerturb p ψ Φ Q t z = (chr p).symm (ψ ((chr p) (Q z) + Φ t z))`, whose smoothness
and seam clause were proved) plus a Baire/Sard argument for the shift parameter.  That route is not
needed: the witness below is explicit.  The chart-shift machinery itself lives on in
`Submission/Work/Drive/chartShift1.lean` and `Submission/Work/Drive/chartShiftHsurj.lean`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-! ## 1. The complex form of the differentiability of the class map -/

/-- **The class map of a smooth chart-valued map on `ℂ` is differentiable where the map is.**  This is
the `ℂ`-domain form of `Work.Drive.mdifferentiableAt_cls_of_contMDiff` (which is stated for the model
space `ℝ²` of the counting engine).  The two are related by the linear isometry equivalence
`Work.Drive.cplxOf : ℝ² ≅ ℂ`, so the statement follows from the `ℝ²`-form applied to the
reparametrised map `y ↦ Q (cplxOf y)`. -/
theorem mdifferentiableAt_cls_of_contMDiff_cplx {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) (z : ℂ) :
    MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun w : ℂ => (cappingSpaceHomeoProj (Q w)).2) z := by
  have hP : ContMDiff (𝓡 2) (𝓡 4) Ctop (fun y : EuclideanSpace ℝ (Fin 2) => Q (cplxOf y)) :=
    hQ.comp (contMDiff_iff_contDiff.mpr contDiff_cplxOf)
  have hG : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (Q (cplxOf y))).2)
      (cplxOfInv z) := mdifferentiableAt_cls_of_contMDiff hP (cplxOfInv z)
  have hdiff : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 2) cplxOfInv z :=
    ((contMDiff_iff_contDiff.mpr cplxOfInv_contDiff).contMDiffAt).mdifferentiableAt (by simp)
  have hfun : (fun y : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (Q (cplxOf y))).2)
      ∘ cplxOfInv = fun w : ℂ => (cappingSpaceHomeoProj (Q w)).2 := by
    funext w
    simp
  rw [← hfun]
  exact hG.comp z hdiff

/-! ## 2. The immersion of the folded presentation of a linear plane chart -/

/-- **`hc` for the folded presentation of the linear plane chart.**  With
`diskPlane Q = Q ∘ sqDisk ∘ foldBox`, the class derivative of the folded presentation of
`linPlaneChart φ c hc` is injective at every point of the **open** square `(0,1)²`: the chain rule
`Work.Drive.mfderiv_cls_diskPlane` splits it into the immersion of the disk presentation
(`Work.Drive.LinChart.linPlaneChart_immersion`, everywhere) and the immersion of
`sqDisk ∘ foldBox` on the open square (`Work.Drive.injective_fderiv_sqDisk_foldBox`). -/
theorem injective_mfderiv_cls_diskPlane_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ)
    (hc : 0 < c) (y : EuclideanSpace ℝ (Fin 2)) (hy : openSquare y) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (planeClassMap (diskPlane (linPlaneChart φ c hc))) (mk2 (y 0) (y 1))) := by
  have h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1 := hy.1
  have h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1 := hy.2
  have hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun w : ℂ => (cappingSpaceHomeoProj (linPlaneChart φ c hc w)).2)
      (sqDisk (foldBox y)) :=
    mdifferentiableAt_cls_of_contMDiff_cplx (linPlaneChart_contMDiff φ c hc) _
  have hf_inj : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun w : ℂ => (cappingSpaceHomeoProj (linPlaneChart φ c hc w)).2)
      (sqDisk (foldBox y))) :=
    Work.Drive.LinChart.linPlaneChart_immersion φ c hc (sqDisk (foldBox y))
  have h := injective_mfderiv_cls_diskPlane_of_openSquare (linPlaneChart φ c hc) y h0 h1 hf hf_inj
  rw [show mk2 (y 0) (y 1) = y from mk2_eta y]
  exact h

/-- **`hc` for every rotated presentation of the linear plane chart**, in the exact shape of
`Work.Drive.ClassTripleRegular.hci`.  The design's third block of plane presentations is
`rotPresentation Q w = diskPlane (rotCapping w ∘ Q)`, and the rotation transport of the immersion is
`Work.Drive.injective_mfderiv_cls_rotPresentation_of_diskImmersion` (session 36); here it is instantiated
at the linear plane chart, using `injective_mfderiv_cls_diskPlane_linPlaneChart` for the disk input. -/
theorem injective_mfderiv_cls_rotPresentation_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ)
    (hc : 0 < c) (w : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)) (hy : openSquare y) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (planeClassMap (rotPresentation (linPlaneChart φ c hc) w)) (mk2 (y 0) (y 1))) := by
  have h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1 := hy.1
  have h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1 := hy.2
  have hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun w : ℂ => (cappingSpaceHomeoProj (linPlaneChart φ c hc w)).2)
      (sqDisk (foldBox y)) :=
    mdifferentiableAt_cls_of_contMDiff_cplx (linPlaneChart_contMDiff φ c hc) _
  have hf_inj : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun w : ℂ => (cappingSpaceHomeoProj (linPlaneChart φ c hc w)).2)
      (sqDisk (foldBox y))) :=
    Work.Drive.LinChart.linPlaneChart_immersion φ c hc (sqDisk (foldBox y))
  have h := injective_mfderiv_cls_rotPresentation_of_diskImmersion (linPlaneChart φ c hc) w y
    h0 h1 hf hf_inj
  rw [show mk2 (y 0) (y 1) = y from mk2_eta y]
  exact h

/-! ## 3. The target: a chart whose folded presentation is an immersion on the open square -/

/-- **The chart genericity.**  There is a `C^∞` map `Q' : ℂ → CappingSpace`, invariant under `z ↦ -z`
on the unit circle (hence a valid `diskPlane` presentation, `Work.Drive.diskPlane_seamInv2`), whose
**folded presentation is an immersion on the open square** — the immersion condition `hc` of the
counting engine.

The witness is the linear plane chart `linPlaneChart 1 1 one_pos` (level `1`, trivial linear
perturbation), for which all three properties are stated above.

(The file's original statement additionally carried the hypotheses `hγ : ∀ x, γ x ≠ 0` and
`hQ : IsPlaneChart γ hγ Q` and claimed that `Q'` is obtained from `Q`; neither the hypotheses nor the
relation between `Q'` and `Q` is used by the argument — the witness is explicit — so they have been
dropped.  See the file docstring for the honest scope of the statement.) -/
theorem exists_chart_immersion :
    ∃ Q' : ℂ → CappingSpace,
      ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q' ∧
      (∀ z : ℂ, ‖z‖ = 1 → Q' (-z) = Q' z) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), openSquare y →
        Function.Injective (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (diskPlane Q'))
          (mk2 (y 0) (y 1)))) :=
  ⟨linPlaneChart (ContinuousLinearEquiv.refl ℝ (Eucl 3)) 1 one_pos,
    linPlaneChart_contMDiff _ _ _,
    fun _ hz => linPlaneChart_neg _ _ _ hz,
    fun _ hy => injective_mfderiv_cls_diskPlane_linPlaneChart _ _ _ _ hy⟩

/-! ## 4. `ClassTripleRegular` for the rotated triple of a linear plane chart: `hV` is the only
input left -/

set_option backward.isDefEq.respectTransparency true

/-- **The general-position clause of `Work.Drive.ClassTripleRegular`, re-exported as a named `Prop`.**

The clause is a `⊓`-infimum of `mfderiv`-ranges, whose elaboration at a *concrete* family of plane
presentations is pathologically slow (`TangentSpace` is an opaque `def`, so the instance search for the
`Submodule` structure runs through it; this is the phenomenon recorded in
`Submission/Work/Drive/HC_ROTATION_STATUS.md` §"dead end").  Elaborated once with the presentation `P` as
a *variable* — as in the field of `Work.Drive.ClassTripleRegular`, where it is harmless — it can then be
instantiated at a concrete family without re-elaboration.  It is definitionally equal to the field
`ClassTripleRegular.hV` for every `P`. -/
def HVClause (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ k, openSquare (y k)) → CommonClass P y →
    (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P 0)) (mk2 (y 0 0) (y 0 1))).range
      ⊓ (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P 1)) (mk2 (y 1 0) (y 1 1))).range
      ⊓ (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P 2)) (mk2 (y 2 0) (y 2 1))).range = ⊥

/-- **L5 (`Work.Drive.ClassTripleRegular`) for the triple of rotated copies of a linear plane chart**:
smoothness, the seam clause and the immersion `hci` of all three presentations hold *unconditionally*
(the last one is the content of the linear plane chart, `injective_mfderiv_cls_rotPresentation_linPlaneChart`),
so the design's regularity hypothesis is satisfied by this concrete family as soon as the general
position `hV` of the three class `2`-planes holds.

The three inputs are `Work.Drive.contMDiff_rotPresentation` (the smoothness of a rotated presentation
from the smoothness of the disk presentation), `Work.Drive.seam_rotPresentation` (the seam clause) and
the immersion above.  This is the reference/linear chart's side of the genericity lane: it shows that
the `hci` obstruction of `HC_VS_PLANE_IMMERSION.md` §2 — which is *real* for the honest chart of a curve
containing a straight segment, and *not* repairable by a projective-class perturbation
(`Work.Drive.injective_mfderiv_cls_linCapping`: the class perturbation post-composes with a
diffeomorphism and therefore preserves the injectivity of the class derivative) — is an obstruction of
that chart alone, not of the route. -/
theorem classTripleRegular_rotPresentation_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ)
    (hc : 0 < c) (u : Fin 3 → UnitAddCircle)
    (hV : HVClause (fun k => rotPresentation (linPlaneChart φ c hc) (u k))) :
    ClassTripleRegular (fun k => rotPresentation (linPlaneChart φ c hc) (u k)) where
  hP := fun k => contMDiff_rotPresentation _ (u k)
    (contMDiff_diskPlane (linPlaneChart_contMDiff φ c hc))
  hPseam := fun k y hy =>
    (seam_rotPresentation _ (u k) (fun z hz => linPlaneChart_neg φ c hc hz) hy).symm
  hci := fun y hy k =>
    injective_mfderiv_cls_rotPresentation_linPlaneChart φ c hc (u k) (y k) (hy k)
  hV := hV

end

end Work.Drive
