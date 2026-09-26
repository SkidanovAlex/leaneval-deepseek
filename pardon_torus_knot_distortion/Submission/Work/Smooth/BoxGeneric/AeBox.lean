import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Bridge
import Submission.Work.Smooth.BoxGeneric.Case.exists_active_signed_of_not_vertex
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_corner
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_coord
import Submission.Work.Smooth.BoxGeneric.Sard.SardCoord

/-!
# Almost every box-norm level set is in general position: the local model

This file contains the *local* theory of the box-norm level sets: the basic API of the faces of
Pardon's box and the model of a "good" level at which the level set is locally an arc.

* `Work.Smooth.BoxGeneric.pullback_faceLin_eq`, `Work.Smooth.BoxGeneric.fderiv_pullback_faceLin` —
  the pulled-back signed faces and their derivatives;
* `Work.Smooth.BoxGeneric.signedFace_eq_of_faceLin_eq`, `Work.Smooth.BoxGeneric.boxNorm_eq_of_active_signed`
  — the sign bookkeeping of a tight signed face;
* `Work.Smooth.BoxGeneric.isLocalArc_levelSet` — **the local model**: if `s > 0` is a level at which
  * every signed face function is regular at the value `± s` (`SardCoord`, or two-dimensional Sard
    through `Work.Smooth.BoxGeneric.Sard.sardCoord`),
  * every corner of the level set is transverse (`AeTransverseCorner`),
  * no point of the level set is a vertex of the box (`AeNoVertex`),

  then the level set of the box norm at `s` is locally an arc;
* `Work.Smooth.BoxGeneric.aeTransverseBox_of_inputs` — the corresponding almost-everywhere
  statement `AeTransverseBox ψ c σ`, from the same inputs and the classification of compact
  `1`-manifolds.

The *sharp* form of the same theorem, in which the corner input `AeTransverseCorner` is replaced by
its almost-everywhere consequences (two-dimensional Sard on the smooth pieces and on the bisector),
is in `Submission/Work/Smooth/BoxGeneric/AeMain.lean`.  This file keeps the older, weaker interface
as a documented reduction step.

## Main results

* `Work.Smooth.BoxGeneric.isLocalArc_levelSet` — **a good level is locally an arc**;
* `Work.Smooth.BoxGeneric.aeTransverseBox_of_inputs` — **`AeTransverseBox` from the inputs**
  `SardCoord`, `AeTransverseCorner`, `AeNoVertex` and `CompactOneManifoldInput`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.BoxGeneric

noncomputable section

variable {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}

/-! ## The signed faces and their pull-backs -/

theorem pullback_faceLin_eq (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) :
    Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) =
      fun p => ε * Work.Smooth.Morse.pullback ψ (signedFace c σ i) p := rfl

theorem fderiv_pullback_faceLin (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p =
      ε • fderiv ℝ (Work.Smooth.Morse.pullback ψ (signedFace c σ i)) p := by
  have h : Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) =
      ε • Work.Smooth.Morse.pullback ψ (signedFace c σ i) := rfl
  rw [h]
  exact fderiv_const_smul
    ((pullback_signedFace_contDiff ψ c σ i).differentiable (by simp)).differentiableAt ε

/-- The sign of an active signed face: if `faceLin c σ i ε y = s` with `ε = ±1` then the signed
face coordinate of `y` is `ε * s`. -/
theorem signedFace_eq_of_faceLin_eq {s : ℝ} {i : Fin 3} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {y : R3}
    (h : faceLin c σ i ε y = s) : signedFace c σ i y = ε * s := by
  rcases hε with rfl | rfl
  · simpa using h
  · simp only [faceLin_apply] at h
    linarith

/-- A tight signed face gives the level: `boxNorm c σ y = s` when `faceLin c σ i ε y = s` with
`ε = ± 1`. -/
theorem boxNorm_eq_of_active_signed {s : ℝ} {i : Fin 3} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {y : R3}
    (h : IsActiveSignedFace c σ s i ε y) : Submission.boxNorm c σ y = s := by
  have hsnn : 0 ≤ s := le_trans (faceNorm_nonneg c σ i y) (h.2 i)
  refine le_antisymm ((boxNorm_le_iff c σ s y).mpr h.2) ?_
  have h1 : faceNorm c σ i y = s := by
    have hsf : signedFace c σ i y = ε * s := signedFace_eq_of_faceLin_eq hε h.1
    rw [faceNorm_eq_abs_signedFace, hsf]
    rcases hε with rfl | rfl
    · rw [one_mul, abs_of_nonneg hsnn]
    · rw [abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg hsnn]
  exact h1 ▸ faceNorm_le_boxNorm c σ i y

/-! ## A point of the level set is locally an arc -/

/-- **The local model of a good level.**  If `s > 0` is a level at which

* every signed face function is regular at the value `± s`,
* every corner of the level set is transverse (`CornerTransverseAt`), and
* no point of the level set is a vertex of the box,

then the level set of the box norm at `s` is locally an arc. -/
theorem isLocalArc_levelSet {s : ℝ} (hs : 0 < s)
    (hreg : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) →
      Work.Smooth.Morse.IsRegularValue ψ (signedFace c σ i) (ε * s))
    (hcorn : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, Submission.boxNorm c σ y = s →
      ∀ (i j : Fin 3) (ε ε' : ℝ), i ≠ j → IsActiveSignedFace c σ s i ε y →
        IsActiveSignedFace c σ s j ε' y → CornerTransverseAt ψ c σ i j ε ε' y)
    (hvert : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, ¬ IsBoxVertexPoint c σ s y) :
    Work.Smooth.Morse.IsLocalArc ψ
      (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  intro x hx
  rw [Work.Smooth.Morse.mem_levelSet] at hx
  obtain ⟨hxcar, hxbox⟩ := hx
  have hnv := hvert x hxcar
  rcases Case.exists_active_signed_of_not_vertex hs hxbox hnv with
    ⟨i, ε, hε, hact, huniq⟩ | ⟨i, j, ε, ε', hij, hε, hε', hacti, hactj, huniq⟩
  · -- unique active face: the level set is locally the level set of a smooth face
    have hregp : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = x ∧
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p ≠ 0 := by
      have hxcar' : x ∈ Set.range (Work.Smooth.Morse.param ψ) := by
        rwa [← Work.Smooth.Morse.torus_carrier]
      obtain ⟨p, hp⟩ := hxcar'
      refine ⟨p, hp, ?_⟩
      intro hzero
      have hval : Work.Smooth.Morse.pullback ψ (signedFace c σ i) p = ε * s := by
        have h2 : signedFace c σ i x = ε * s := signedFace_eq_of_faceLin_eq hε hact.1
        have h3 : Work.Smooth.Morse.pullback ψ (signedFace c σ i) p = signedFace c σ i x := by
          show signedFace c σ i (Work.Smooth.Morse.param ψ p) = signedFace c σ i x
          rw [hp]
        rw [h3, h2]
      have hzero' : fderiv ℝ (Work.Smooth.Morse.pullback ψ (signedFace c σ i)) p = 0 := by
        rw [fderiv_pullback_faceLin] at hzero
        rcases hε with h1 | h1
        · rw [h1, one_smul] at hzero; exact hzero
        · rw [h1] at hzero
          simpa using hzero
      exact ((Work.Smooth.Morse.isRegularValue_iff ψ _ _).mp (hreg i ε hε)) p hval hzero'
    exact LocalSurface.isLocalArcAt_of_uniqueActiveFace hs hε hxcar hact huniq hregp
  · exact LocalSurface.isLocalArcAt_of_corner hs hij hε hε' hxcar hacti hactj huniq
      (hcorn x hxcar hxbox i j ε ε' hij hacti hactj)

/-! ## The main theorem -/

/-- **Almost every box sphere meets the surface in general position.** -/
theorem aeTransverseBox_of_inputs (hS : SardCoord ψ) (hcorn : AeTransverseCorner ψ c σ)
    (hvert : AeNoVertex ψ c σ) (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    AeTransverseBox ψ c σ := by
  have hreg := FaceRegular.ae_face_regular_of_sardCoord hS c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hreg, hcorn, hvert, hne] with s hs_reg hs_corn hs_vert hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = ∅ := by
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
      exact isLocalArc_levelSet hsgt (fun i ε hε => hs_reg i ε hε) hs_corn hs_vert

end

end Work.Smooth.BoxGeneric
