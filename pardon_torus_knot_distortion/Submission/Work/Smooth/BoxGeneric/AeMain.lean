import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.AeBox
import Submission.Work.Smooth.BoxGeneric.Bridge
import Submission.Work.Smooth.BoxGeneric.Case.exists_active_signed_of_not_vertex
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_corner
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_tangentialCorner
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord
import Submission.Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector
import Submission.Work.Smooth.BoxGeneric.Sard.SardCoord
import Submission.Work.Topology.Classical.SliceInput
import Submission.Work.Smooth.SphereJordan.RoundSphere
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# Almost every box-norm level set is in general position

This is the main theorem of the chapter, in its sharp form: the corner input `AeTransverseCorner`
of `Submission/Work/Smooth/BoxGeneric/AeBox.lean` is replaced by the *consequences* of
two-dimensional Sard on the smooth pieces of the box norm.

At an almost every level `s`:

* every one of the six signed faces `faceLin c σ i ε` (`ε = ±1`) is *regular* at the value `± s`,
  i.e. no point of the level set is a critical point of the active face
  (`FaceRegular.ae_face_regular_of_sardCoord`, from `Sard.sardCoord` and the two-dimensional Sard
  theorem of `Submission/Work/Smooth/BoxGeneric/Sard/`);
* at every corner of the level set (`IsCornerTransverseAt`; two tight faces `(i, ε)`, `(j, ε')`)
  the case analysis of `Work.Smooth.BoxGeneric.Case.exists_active_signed_of_not_vertex` splits into
  * the *tangential* case, in which the derivative of the bisector `faceLin i ε - faceLin j ε'`
    vanishes: the local model `LocalSurface.isLocalArcAt_of_tangentialCorner`;
  * the *transverse* case, in which that derivative is non-zero: then
    `AeCorner.ae_transverseCorner_of_regularBisector` (itself proved from the restricted Sard
    theorem, `Sard.exists_isOpen_volume_image_restrictedCritical_null`) gives the invertibility of
    the pair of face derivatives, i.e. `CornerTransverseAt`, and the local model
    `LocalSurface.isLocalArcAt_of_corner` applies.

The only genericity inputs left are therefore

* `AeNoVertex ψ c σ` — the surface misses the vertices of the box for almost every level (this is
  *not* a consequence of smoothness; see the README),
* `Work.Smooth.Morse.CompactOneManifoldInput ψ` — the classification of compact `1`-manifolds,

and the classical Jordan–Schoenflies input of the slicing of a sphere by the surface.

## Main results

* `Work.Smooth.BoxGeneric.exists_fderiv_pullback_faceLin_ne_zero` — the regularity of a face at the
  level gives a parameter at which the derivative of the pulled-back face does not vanish;
* `Work.Smooth.BoxGeneric.isLocalArc_levelSet_of_regular` — **a good level is locally an arc**;
* `Work.Smooth.BoxGeneric.aeTransverseBox_of_regularBisector` — **`AeTransverseBox ψ c σ`** from
  `AeNoVertex` and the compact `1`-manifold classification;
* `Work.Smooth.BoxGeneric.aeSlicedAll_of_vertex_classify` — **the target
  `Work.BoxShrink.AeSlicedAll`** from those two inputs and the classical slicing input;
* `Work.Smooth.BoxGeneric.sliceInput_of_jordanSchoenflies` — the classical slicing input of the
  tori of the challenge, from the sphere-side Jordan–Schoenflies theorem;
* `Work.Smooth.BoxGeneric.aeSlicedAll_of_vertex_classify_of_planeHypothesis` — the target with the
  *planar* Jordan–Schoenflies theorem as the only classical input.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.BoxGeneric

noncomputable section

variable {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}

/-! ## A regular face level has a non-critical parameter -/

/-- **The regularity of a signed face at the level gives a parameter with non-vanishing
derivative.**  If `signedFace c σ i` is a regular value `ε * s` (`ε = ±1`) of the surface and the
signed face `faceLin c σ i ε` is tight at `y` with level `s`, then at (any) parameter `p` over `y`
the derivative of the pulled-back signed face does not vanish. -/
theorem exists_fderiv_pullback_faceLin_ne_zero {s : ℝ} {i : Fin 3} {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {y : R3} (hy : y ∈ (Work.Smooth.Morse.torus ψ).carrier)
    (hact : IsActiveSignedFace c σ s i ε y)
    (hreg : Work.Smooth.Morse.IsRegularValue ψ (signedFace c σ i) (ε * s)) :
    ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
      fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p ≠ 0 := by
  rw [Work.Smooth.Morse.torus_carrier] at hy
  obtain ⟨p, hp⟩ := hy
  refine ⟨p, hp, ?_⟩
  intro hzero
  have hval : Work.Smooth.Morse.pullback ψ (signedFace c σ i) p = ε * s := by
    have h2 : signedFace c σ i y = ε * s := signedFace_eq_of_faceLin_eq hε hact.1
    have h3 : Work.Smooth.Morse.pullback ψ (signedFace c σ i) p = signedFace c σ i y := by
      show signedFace c σ i (Work.Smooth.Morse.param ψ p) = signedFace c σ i y
      rw [hp]
    rw [h3, h2]
  have hzero' : fderiv ℝ (Work.Smooth.Morse.pullback ψ (signedFace c σ i)) p = 0 := by
    rw [fderiv_pullback_faceLin] at hzero
    rcases hε with h1 | h1
    · rw [h1, one_smul] at hzero; exact hzero
    · rw [h1] at hzero
      simpa using hzero
  exact ((Work.Smooth.Morse.isRegularValue_iff ψ _ _).mp hreg) p hval hzero'

/-! ## A good level is locally an arc -/

/-- **The local model of a good level, sharp form.**  If `s > 0` is a level at which

* every signed face function is regular at the value `± s`,
* every corner of the level set at which the bisector is regular is transverse
  (`CornerTransverseAt`, supplied almost everywhere by
  `Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector`), and
* no point of the level set is a vertex of the box,

then the level set of the box norm at `s` is locally an arc.

At a corner of the level set with a *critical* bisector the tangential local model is used instead,
so no transversality hypothesis is needed in that case; this is why the hypothesis `hcorn` below is
stated only for the pair `(i, ε)`, `(j, ε')` together with the *non-vanishing* of the bisector
derivative. -/
theorem isLocalArc_levelSet_of_regular {s : ℝ} (hs : 0 < s)
    (hreg : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) →
      Work.Smooth.Morse.IsRegularValue ψ (signedFace c σ i) (ε * s))
    (hcorn : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, Submission.boxNorm c σ y = s →
      ∀ (i j : Fin 3) (ε ε' : ℝ), i ≠ j → (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) →
        IsActiveSignedFace c σ s i ε y → IsActiveSignedFace c σ s j ε' y →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p ≠ 0) →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) p ≠ 0) →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ
            (fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z)) p ≠ 0) →
        CornerTransverseAt ψ c σ i j ε ε' y)
    (hvert : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, ¬ IsBoxVertexPoint c σ s y) :
    Work.Smooth.Morse.IsLocalArc ψ
      (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  intro x hx
  rw [Work.Smooth.Morse.mem_levelSet] at hx
  obtain ⟨hxcar, hxbox⟩ := hx
  have hnv := hvert x hxcar
  rcases Case.exists_active_signed_of_not_vertex hs hxbox hnv with
    ⟨i, ε, hε, hact, huniq⟩ | ⟨i, j, ε, ε', hij, hε, hε', hacti, hactj, huniq⟩
  · exact LocalSurface.isLocalArcAt_of_uniqueActiveFace hs hε hxcar hact huniq
      (exists_fderiv_pullback_faceLin_ne_zero hε hxcar hact (hreg i ε hε))
  · have hregi := exists_fderiv_pullback_faceLin_ne_zero hε hxcar hacti (hreg i ε hε)
    have hregj := exists_fderiv_pullback_faceLin_ne_zero hε' hxcar hactj (hreg j ε' hε')
    by_cases hcrit : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = x ∧
        fderiv ℝ (Work.Smooth.Morse.pullback ψ
          (fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z)) p = 0
    · exact LocalSurface.isLocalArcAt_of_tangentialCorner hs hij hε hε' hxcar hacti hactj
        huniq hcrit hregi
    · have hregbis : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = x ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ
            (fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z)) p ≠ 0 := by
        obtain ⟨p, hp, -⟩ := hregi
        exact ⟨p, hp, fun h0 => hcrit ⟨p, hp, h0⟩⟩
      exact LocalSurface.isLocalArcAt_of_corner hs hij hε hε' hxcar hacti hactj huniq
        (hcorn x hxcar hxbox i j ε ε' hij hε hε' hacti hactj hregi hregj hregbis)

/-- **For almost every level, the box-norm level set on the surface is a compact locally-arc set**
— i.e. a compact `1`-manifold — the essential content of the chapter, isolated from the
classification of compact `1`-manifolds and from the Jordan–Schoenflies input.

The two ingredients are the three local models of the level set (a unique active face, a transverse
corner, a tangential corner) and two-dimensional Sard (through the a.e. regularity of the six signed
faces and the a.e. transversality of the bisector). -/
theorem ae_isCompact_isLocalArc_levelSet (hvert : AeNoVertex ψ c σ) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsCompact (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) ∧
      Work.Smooth.Morse.IsLocalArc ψ
        (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have hreg := FaceRegular.ae_face_regular_of_sardCoord (Sard.sardCoord ψ) c σ
  have hcorn := AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  have hcont : Continuous (Submission.boxNorm c σ) :=
    Work.Topology.SphereSlicing.boxNorm_continuous c σ
  filter_upwards [hreg, hcorn, hvert, hne] with s hs_reg hs_corn hs_vert hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact BoxSphere_eq_empty_of_neg hslt c σ
    have hempty : Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s = ∅ := by
      rw [Work.Smooth.Morse.levelSet, hbox, Set.inter_empty]
    rw [hempty]
    exact ⟨isCompact_empty, fun x hx => absurd hx (Set.notMem_empty x)⟩
  · exact ⟨Work.Smooth.Morse.Surface.isCompact_levelSet ψ hcont s,
      isLocalArc_levelSet_of_regular hsgt (fun i ε hε => hs_reg i ε hε) hs_corn hs_vert⟩

/-- **For almost every level, the box-norm level set is a finite disjoint union of simple closed
curves of the surface** (granted the classification of compact `1`-manifolds): the conclusion of the
chapter's smooth analysis, in the form of `Work.Smooth.Morse.IsCircleUnion`. -/
theorem ae_isCircleUnion_levelSet (hvert : AeNoVertex ψ c σ)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsCircleUnion ψ
        (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have hreg := FaceRegular.ae_face_regular_of_sardCoord (Sard.sardCoord ψ) c σ
  have hcorn := AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  have hcont : Continuous (Submission.boxNorm c σ) :=
    Work.Topology.SphereSlicing.boxNorm_continuous c σ
  filter_upwards [hreg, hcorn, hvert, hne] with s hs_reg hs_corn hs_vert hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact BoxSphere_eq_empty_of_neg hslt c σ
    have hempty : Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s = ∅ := by
      rw [Work.Smooth.Morse.levelSet, hbox, Set.inter_empty]
    rw [hempty]
    exact ⟨0, Fin.elim0, (fun i => i.elim0), (fun i => i.elim0), by ext x; simp⟩
  · exact hclass _ (Work.Smooth.Morse.Surface.isCompact_levelSet ψ hcont s)
      (isLocalArc_levelSet_of_regular hsgt (fun i ε hε => hs_reg i ε hε) hs_corn hs_vert)

/-! ## Almost every box sphere is transverse to the surface -/

/-- **Almost every box sphere meets the surface in general position**, from the genericity of the
vertex stratum and the classification of compact `1`-manifolds.  All the other inputs —
two-dimensional Sard, the regularity of the face levels, the corner transversality (both the
tangential and the transverse case) — are theorems of the chapter. -/
theorem aeTransverseBox_of_regularBisector (hvert : AeNoVertex ψ c σ)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) : AeTransverseBox ψ c σ := by
  have hreg := FaceRegular.ae_face_regular_of_sardCoord (Sard.sardCoord ψ) c σ
  have hcorn := AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hreg, hcorn, hvert, hne] with s hs_reg hs_corn hs_vert hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact BoxSphere_eq_empty_of_neg hslt c σ
    rw [hbox]
    exact transverseSphere_empty _
  · have hcont : Continuous (Submission.boxNorm c σ) :=
      Work.Topology.SphereSlicing.boxNorm_continuous c σ
    refine transverseSphere_of_compact_isLocalArc hclass ?_ ?_
    · rw [Set.inter_comm, ← Work.Smooth.Morse.levelSet]
      exact Work.Smooth.Morse.Surface.isCompact_levelSet ψ hcont s
    · rw [Set.inter_comm, ← Work.Smooth.Morse.levelSet]
      exact isLocalArc_levelSet_of_regular hsgt (fun i ε hε => hs_reg i ε hε) hs_corn hs_vert

/-- **Almost every box sphere meets the surface in general position**, with `ψ`, `c`, `σ`
explicit. -/
theorem aeTransverseBox (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hvert : AeNoVertex ψ c σ) (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    AeTransverseBox ψ c σ :=
  aeTransverseBox_of_regularBisector hvert hclass

/-! ## The target -/

/-- **The target `Work.BoxShrink.AeSliced` for a single diffeomorphism**, from the genericity of
the vertex stratum, the classification of compact `1`-manifolds and the classical slicing input. -/
theorem aeSliced_of_vertex_classify (hvert : AeNoVertex ψ c σ)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hslice : Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    Work.BoxShrink.AeSliced ψ c σ :=
  aeSliced_of_aeTransverseBox ψ c σ (aeTransverseBox_of_regularBisector hvert hclass) hslice

/-- **The target `Work.BoxShrink.AeSlicedAll`** from the two genericity inputs and the classical
slicing input. -/
theorem aeSlicedAll_of_vertex_classify
    (hvert : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)), AeNoVertex ψ c σ)
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hslice : ∀ ψ : Submission.Diffeo,
      Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    Work.BoxShrink.AeSlicedAll :=
  fun ψ c σ => aeSliced_of_vertex_classify (hvert ψ c σ) (hclass ψ) (hslice ψ)

/-! ## The classical slicing input, from Jordan–Schoenflies

The classical input `Work.Topology.SphereSlicing.SliceInput` of the tori of the challenge is *not*
taken as a hypothesis in the final form of the chapter: it follows from the sphere-side
Jordan–Schoenflies theorem, which the sibling chapter `Submission/Work/Smooth/SphereJordan` derives
from the planar Jordan–Schoenflies theorem. -/

/-- **The classical slicing input of the tori of the challenge, from Jordan–Schoenflies on the
round sphere.** -/
theorem sliceInput_of_jordanSchoenflies
    (h : Work.Topology.Classical.JordanSchoenfliesSphere) (ψ : Submission.Diffeo) :
    Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ) :=
  Work.Topology.Classical.sliceInput_mapHomeomorph_of_jordanSchoenflies ψ.toHomeomorph h

/-- **The target `Work.BoxShrink.AeSlicedAll` from the two genericity inputs and the sphere-side
Jordan–Schoenflies theorem.**  The classical slicing input is discharged by
`sliceInput_of_jordanSchoenflies`. -/
theorem aeSlicedAll_of_vertex_classify_of_jordanSchoenflies
    (hvert : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)), AeNoVertex ψ c σ)
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_vertex_classify hvert hclass (fun ψ => sliceInput_of_jordanSchoenflies hjordan ψ)

/-- **The target `Work.BoxShrink.AeSlicedAll` from the two genericity inputs and the planar
Jordan–Schoenflies theorem** (`Work.Smooth.SphereJordan.PlaneHypothesis`, the classical input of the
sibling chapters `Submission/Work/Smooth/Jordan` and `Submission/Work/Smooth/SphereJordan`). -/
theorem aeSlicedAll_of_vertex_classify_of_planeHypothesis
    (hvert : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)), AeNoVertex ψ c σ)
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hplane : Work.Smooth.SphereJordan.PlaneHypothesis) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_vertex_classify_of_jordanSchoenflies hvert hclass
    (Work.Smooth.SphereJordan.jordanSchoenfliesSphere hplane)

/-- **The pointwise target** `Work.BoxShrink.AeSliced ψ c σ` from the two genericity inputs (the
classical slicing input is applied through its homeomorphism-invariance). -/
theorem aeSliced_of_vertex_classify_of_jordanSchoenflies (hvert : AeNoVertex ψ c σ)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Work.BoxShrink.AeSliced ψ c σ :=
  aeSliced_of_vertex_classify hvert hclass (sliceInput_of_jordanSchoenflies hjordan ψ)

end

end Work.Smooth.BoxGeneric
