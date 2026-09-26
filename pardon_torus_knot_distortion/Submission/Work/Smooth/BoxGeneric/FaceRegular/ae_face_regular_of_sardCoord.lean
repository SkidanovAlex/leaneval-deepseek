import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs

/-!
# Almost every signed face level is a regular value of the box coordinate function

The box norm is the maximum of the six signed faces `faceLin c σ i ε = ε * signedFace c σ i`
(`ε = ± 1`).  For the general position theory of the box level sets one needs that for almost every
level `s` *all six* of the smooth pieces through the level `s` are cut transversally: that is,
`ε * s` is a regular value of `signedFace c σ i` for every `i` and every sign `ε`.

The only smoothness input is `SardCoord ψ`: almost every level of every coordinate function
`y ↦ y j` is a regular value.  Since `signedFace c σ i = ((·) (σ i) - c (σ i)) / boxSide i` is an
affine reparametrisation of the coordinate function `(·) (σ i)` (a nonzero scaling followed by a
translation, both of which preserve critical points and regular values), the set of non-regular
levels of `signedFace c σ i` is the image of the null set of non-regular levels of `(·) (σ i)`
under a nonzero affine map, hence null.  Intersecting the finitely many null exceptional sets
(`i : Fin 3` and the two signs) gives the result.
-/

namespace Work.Smooth.BoxGeneric.FaceRegular

open MeasureTheory Filter
open LeanEval.KnotTheory.PardonDistortion

/-- **The ae (Lebesgue) filter is invariant under a nonzero affine reparametrisation.**  If `P`
holds almost everywhere then so does `s ↦ P (b * s + a)` for `b ≠ 0`.

This is the elementary fact that the map `s ↦ b * s + a` (a nonzero scaling followed by a
translation) is quasi-measure-preserving for Lebesgue measure: `(· + a)` is measure preserving on
`(ℝ, +)` (`measure_preimage_add`) and `(b * ·)` scales the measure by `|b|⁻¹`
(`Real.volume_preimage_mul_left`), in particular taking null sets to null sets. -/
private lemma ae_comp_affine_aux {P : ℝ → Prop} {a b : ℝ} (hb : b ≠ 0)
    (h : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), P t) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), P (b * s + a) := by
  rw [MeasureTheory.ae_iff] at h ⊢
  have hset : {s : ℝ | ¬ P (b * s + a)}
      = (fun x : ℝ => b * x) ⁻¹' ((fun u : ℝ => a + u) ⁻¹' {t : ℝ | ¬ P t}) := by
    ext s; simp [add_comm]
  rw [hset, Real.volume_preimage_mul_left hb]
  rw [MeasureTheory.measure_preimage_add]
  rw [h, mul_zero]

/-- **The chain rule for a signed face.**  The pulled-back signed face is `b⁻¹` times the shifted
pulled-back coordinate function (`b = boxSide i`), so its derivative is `b⁻¹` times the derivative
of the pulled-back coordinate function. -/
private theorem pullback_signedFace_fderiv (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)) p =
      (Submission.boxSide i)⁻¹ •
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i))) p := by
  have hfun : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)
      = fun q : ℝ × ℝ =>
          (Submission.boxSide i)⁻¹ *
            (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) := by
    funext q
    rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have hdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) p :=
    (((Work.Smooth.Morse.pullback_contDiff ψ (g := fun y : R3 => y (σ i))
        (by fun_prop)).differentiable (by simp)).sub_const (c (σ i))).differentiableAt
  rw [fderiv_const_mul hdiff, fderiv_sub_const]

/-- **The regular values of a signed face are the regular values of the coordinate function.**
`t` is a regular value of the signed face `signedFace c σ i` exactly when
`t * boxSide i + c (σ i)` is a regular value of the coordinate function `y ↦ y (σ i)`.

Both the level value and the derivative transform affinely: `signedFace c σ i y = t` iff
`y (σ i) = t * boxSide i + c (σ i)`, and the derivative of the pulled-back signed face is the
nonzero multiple `boxSide i⁻¹` of the derivative of the pulled-back coordinate function. -/
private theorem isRegularValue_signedFace_iff (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (t : ℝ) :
    Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) t ↔
      Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => y (σ i))
        (t * Submission.boxSide i + c (σ i)) := by
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  rw [Work.Smooth.Morse.isRegularValue_iff, Work.Smooth.Morse.isRegularValue_iff]
  constructor
  · intro h p hp
    have hp' : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i) p = t := by
      rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, div_eq_iff hb, hp]
      ring
    have hne : (Submission.boxSide i)⁻¹ •
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i))) p ≠ 0 := by
      have := h p hp'
      rwa [pullback_signedFace_fderiv] at this
    exact (smul_ne_zero_iff.mp hne).2
  · intro h p hp
    have hp' : Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) p
        = t * Submission.boxSide i + c (σ i) := by
      have h' := hp
      rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, div_eq_iff hb] at h'
      exact sub_eq_iff_eq_add.mp h'
    have hne := h p hp'
    rw [pullback_signedFace_fderiv]
    exact smul_ne_zero_iff.mpr ⟨inv_ne_zero hb, hne⟩

theorem ae_face_regular_of_sardCoord {ψ : Submission.Diffeo} (hS : Work.Smooth.BoxGeneric.SardCoord ψ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s) := by
  have key : ∀ i : Fin 3, ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (1 * s) ∧
      Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) ((-1) * s) := by
    intro i
    have hcoord := hS (σ i)
    have h1 : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (1 * s) := by
      have hcomp := ae_comp_affine_aux (a := c (σ i)) (b := 1 * Submission.boxSide i)
        (by rw [one_mul]; exact ne_of_gt (Submission.boxSide_pos i))
        (P := fun u => Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => y (σ i)) u) hcoord
      filter_upwards [hcomp] with s hs
      rw [isRegularValue_signedFace_iff,
        ← show (1 * Submission.boxSide i) * s + c (σ i)
            = (1 * s) * Submission.boxSide i + c (σ i) from by ring]
      exact hs
    have h2 : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) ((-1) * s) := by
      have hb : ((-1) * Submission.boxSide i) ≠ 0 := by
        have := Submission.boxSide_pos i; nlinarith
      have hcomp := ae_comp_affine_aux (a := c (σ i)) (b := (-1) * Submission.boxSide i) hb
        (P := fun u => Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => y (σ i)) u) hcoord
      filter_upwards [hcomp] with s hs
      rw [isRegularValue_signedFace_iff,
        ← show ((-1) * Submission.boxSide i) * s + c (σ i)
            = ((-1) * s) * Submission.boxSide i + c (σ i) from by ring]
      exact hs
    exact h1.and h2
  refine MeasureTheory.ae_all_iff.mpr (fun i => ?_)
  filter_upwards [key i] with s hs ε hε
  rcases hε with hε | hε
  · rw [hε]; exact hs.1
  · rw [hε]; exact hs.2

end Work.Smooth.BoxGeneric.FaceRegular
