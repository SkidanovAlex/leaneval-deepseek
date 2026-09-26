import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dent_annulus_defs
import Submission.Work.Drive.Final.fderiv_boxNorm_par_active

/-!
# The determinant of the differential of the box norm along an active face

Pardon's box norm `boxNorm c σ y = max_i |y (σ i) - c (σ i)| / boxSide i` is the maximum of the
three face norms; on the open set where the `σ i`-th face attains the maximum it is smooth, and on
the tie locus it is a (non-smooth) maximum of smooth functions.

This file records the elementary consequence used by the margin analysis of the L4b route: if at a
point `q` of the parameter plane the `σ i`-th face is *attained* — the level `s` of the box norm is
`boxNorm c σ (par ψ q)` and the `σ i`-th coordinate sits exactly on the face,
`|(par ψ q) (σ i) - c (σ i)| = boxSide i * s` — and the box norm is differentiable there with
non-zero differential, then its differential is the differential of the `σ i`-th face alone:
`fderiv (boxNorm ∘ par ψ) q = fderiv (faceNorm c σ i ∘ par ψ) q`.  Consequently the determinant
`det2 L` of the two differentials is related by the single factor `1 / boxSide i`.

The differentiability hypothesis is what rules out the degenerate case `s = 0` (where `q` would be a
global minimum of the box norm and hence a critical point), which is the only way the active face
norm could fail to be differentiable at `q`.

## Main result

* `abs_det2_fderiv_boxNorm_comp_param` — the statement requested by the margin analysis.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.Final

noncomputable section

/-! ## Elementary consequences of the definition of `det2` -/

/-- `det2` is linear in its second argument. -/
lemma det2_smul (L D : (ℝ × ℝ) →L[ℝ] ℝ) (a : ℝ) :
    det2 L (a • D) = a * det2 L D := by
  have h1 : (a • D) ((1 : ℝ), (0 : ℝ)) = a * D ((1 : ℝ), (0 : ℝ)) := by simp
  have h2 : (a • D) ((0 : ℝ), (1 : ℝ)) = a * D ((0 : ℝ), (1 : ℝ)) := by simp
  rw [det2, h1, h2, det2]
  ring

/-- The absolute value of `det2` scales by the absolute value of the scaling factor. -/
lemma abs_det2_smul (L D : (ℝ × ℝ) →L[ℝ] ℝ) (a : ℝ) :
    |det2 L (a • D)| = |a| * |det2 L D| := by
  rw [det2_smul, abs_mul]

/-! ## Two differentiable functions, equal at a point, one dominated by the other -/

/-- **A squeeze for differentials.**  If `F ≤ B` everywhere, `B q = F q` and both are
differentiable at `q`, then their differentials at `q` agree:  `B - F` has a (global) minimum at
`q`, hence vanishing differential there. -/
lemma fderiv_eq_of_le_of_eq {B F : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hBF : ∀ x, F x ≤ B x) (hq : B q = F q)
    (hB : DifferentiableAt ℝ B q) (hF : DifferentiableAt ℝ F q) :
    fderiv ℝ B q = fderiv ℝ F q := by
  have hmin : IsLocalMin (B - F) q := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [Pi.sub_apply]
    rw [hq]
    linarith [hBF x]
  have h0 : fderiv ℝ (B - F) q = 0 := hmin.fderiv_eq_zero
  rw [fderiv_sub hB hF] at h0
  exact sub_eq_zero.mp h0

/-! ## The differential of the pulled-back face norm -/

/-- The pulled-back face norm as an absolute value times a constant. -/
lemma faceNorm_par_eq (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (fun q' : ℝ × ℝ => Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q'))
      = (fun q' : ℝ × ℝ =>
          |Work.BoxShrink.Pinch.par ψ q' (σ i) - c (σ i)| * (Submission.boxSide i)⁻¹) := by
  funext q'
  rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_eq_mul_inv]

/-- The pulled-back `i`-th face norm is differentiable at a point at which the `σ i`-th coordinate
of the parametrisation does not sit at the centre: there `|·|` is differentiable. -/
lemma differentiableAt_faceNorm_par (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) {q : ℝ × ℝ}
    (hne : Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i) ≠ 0) :
    DifferentiableAt ℝ (fun q' : ℝ × ℝ =>
      Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q')) q := by
  have hG : DifferentiableAt ℝ
      (fun q' : ℝ × ℝ => Work.BoxShrink.Pinch.par ψ q' (σ i) - c (σ i)) q :=
    (Work.Drive.Final.par_coord_differentiableAt ψ (σ i) q).sub_const (c (σ i))
  rw [faceNorm_par_eq ψ c σ i]
  exact (hG.abs hne).mul_const _

/-- **The differential of the pulled-back face norm** at a point off the centre is
`(1 / boxSide i)` times the signed differential of the `σ i`-th coordinate. -/
lemma fderiv_faceNorm_par (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) {q : ℝ × ℝ}
    (hne : Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i) ≠ 0) :
    fderiv ℝ (fun q' : ℝ × ℝ =>
        Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q')) q
      = (Submission.boxSide i)⁻¹ •
        (((SignType.sign (Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i))) : ℝ) •
          fderiv ℝ (fun q' : ℝ × ℝ => Work.BoxShrink.Pinch.par ψ q' (σ i)) q) := by
  have hG : HasFDerivAt (fun q' : ℝ × ℝ =>
        Work.BoxShrink.Pinch.par ψ q' (σ i) - c (σ i))
      (fderiv ℝ (fun q' : ℝ × ℝ => Work.BoxShrink.Pinch.par ψ q' (σ i)) q) q :=
    (Work.Drive.Final.par_coord_differentiableAt ψ (σ i) q).hasFDerivAt.sub_const (c (σ i))
  have hF := (hG.abs hne).mul_const ((Submission.boxSide i)⁻¹)
  rw [faceNorm_par_eq ψ c σ i]
  exact hF.fderiv

/-! ## The main lemma -/

theorem abs_det2_fderiv_boxNorm_comp_param {ψ : Submission.Diffeo}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {q : ℝ × ℝ}
    {i : Fin 3} {L : (ℝ × ℝ) →L[ℝ] ℝ}
    (hbox : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) = s)
    (hi : |Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i)| = Submission.boxSide i * s)
    (hdiff : fderiv ℝ (fun q' : ℝ × ℝ =>
      Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q ≠ 0) :
    |det2 L (fderiv ℝ (fun q' : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q)| =
      (1 / Submission.boxSide i) * |det2 L (fderiv ℝ (fun q' : ℝ × ℝ =>
        Work.BoxShrink.Pinch.par ψ q' (σ i)) q)| := by
  have hbpos : 0 < Submission.boxSide i := Submission.boxSide_pos i
  -- the level `s` is positive, otherwise `q` would be a critical point of the box norm
  have hs : 0 < s := by
    by_contra h
    have hle0 : s ≤ 0 := le_of_not_gt h
    have hle : Submission.boxSide i * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbpos.le hle0
    have hge : 0 ≤ Submission.boxSide i * s := by rw [← hi]; exact abs_nonneg _
    have hs0 : s = 0 := by
      have hz : Submission.boxSide i * s = 0 := le_antisymm hle hge
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hbpos)
    have hmin : IsLocalMin
        (fun q' : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q := by
      apply Filter.Eventually.of_forall
      intro x
      show Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)
        ≤ Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ x)
      rw [hbox, hs0]
      exact Submission.boxNorm_nonneg c σ (Work.BoxShrink.Pinch.par ψ x)
    exact hdiff hmin.fderiv_eq_zero
  -- hence the active coordinate sits off the centre
  have hne : Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i) ≠ 0 := by
    intro h0
    have hz : Submission.boxSide i * s = 0 := by rw [← hi, h0]; simp
    exact (ne_of_gt hs) ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hbpos))
  -- differentiability of the box norm and of the active face norm
  have hBdiff : DifferentiableAt ℝ
      (fun q' : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q := by
    by_contra h
    exact hdiff (fderiv_zero_of_not_differentiableAt h)
  have hFdiff := differentiableAt_faceNorm_par ψ c σ i hne
  -- the two agree at `q`
  have hq_eq : (fun q' : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q
      = (fun q' : ℝ × ℝ =>
          Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q')) q := by
    show Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)
      = Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q)
    rw [hbox, Work.Smooth.BoxGeneric.faceNorm_apply, hi]
    exact (mul_div_cancel_left₀ s (ne_of_gt hbpos)).symm
  -- the squeeze: the differential of the box norm is that of the active face
  have hderiv : fderiv ℝ (fun q' : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q
      = fderiv ℝ (fun q' : ℝ × ℝ =>
        Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q')) q :=
    fderiv_eq_of_le_of_eq
      (fun x => Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i (Work.BoxShrink.Pinch.par ψ x))
      hq_eq hBdiff hFdiff
  -- the differential of the active face norm, and the sign
  have hsgn : |((SignType.sign (Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i))) : ℝ)| = 1 := by
    have hne' : SignType.sign (Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i)) ≠ 0 :=
      sign_ne_zero.mpr hne
    rcases SignType.trichotomy (SignType.sign (Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i)))
      with h | h | h
    · rw [h, SignType.coe_neg_one]; norm_num
    · exact absurd h hne'
    · rw [h, SignType.coe_one]; norm_num
  have hscal : |(Submission.boxSide i)⁻¹ *
        ((SignType.sign (Work.BoxShrink.Pinch.par ψ q (σ i) - c (σ i))) : ℝ)|
      = 1 / Submission.boxSide i := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hbpos), hsgn, mul_one, inv_eq_one_div]
  rw [hderiv, fderiv_faceNorm_par ψ c σ i hne, smul_smul, abs_det2_smul, hscal]

end

end Work.Drive.Final
