/-
# The tangency-arc region of the cusp-`0` half tile

Fix the set of `w ∈ 𝒟` lying within `1/10` of one of the two arcs
`{|w ∓ 1/2| = 1/2}` of `∂𝒟` (the tangency loci of the grazing pole `z = (w-1)/w`)
and satisfying `1/2 ≤ Im (S • w) ≤ 2`.  This module records the elementary geometry of
that region: it is bounded and bounded away from the real axis, so all the kernel
bounds on it are uniform.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.All

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Topology

namespace Work.Asymptotics

/-- **The tangency-arc region**: `w ∈ 𝒟` with `1/2 ≤ Im (S • w) ≤ 2` and `w` within `1/10`
of one of the two arcs. -/
def arcT : Set ℍ :=
  {w | w ∈ DomainD ∧ (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im ∧
    (ModularGroup.S • w).im ≤ 2 ∧
    (‖(w : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10 ∨
      ‖(w : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10)}

lemma mem_arcT {w : ℍ} :
    w ∈ arcT ↔ w ∈ DomainD ∧ (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im ∧
      (ModularGroup.S • w).im ≤ 2 ∧
      (‖(w : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10 ∨
        ‖(w : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10) := Iff.rfl

lemma arcT_subset_DomainD : arcT ⊆ DomainD := fun _ h => h.1

/-- `Im (S • w) = Im w / ‖w‖²`. -/
private lemma arcT_im_S (w : ℍ) :
    (ModularGroup.S • w).im = w.im / Complex.normSq (w : ℂ) := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
    Complex.inv_im, Complex.neg_im, Complex.normSq_neg, UpperHalfPlane.coe_im]
  ring

/-- **The away-from-the-axis estimate.**  For `w ∈ arcT` one has `Im w > 1/10`. -/
lemma arcT_im_gt {w : ℍ} (hw : w ∈ arcT) : (1 : ℝ) / 10 < w.im := by
  obtain ⟨hD, hI, hII, -⟩ := mem_arcT.mp hw
  obtain ⟨hx1, hx2, harc1, harc2⟩ := mem_DomainD.mp hD
  have hY : 0 < w.im := w.im_pos
  have hA : w.re ^ 2 - w.re + w.im ^ 2 > 0 := by
    have h : (1 / 4 : ℝ) < Complex.normSq ((w : ℂ) - (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ((w : ℂ) - (1 / 2 : ℂ))]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at h
    norm_num at h
    nlinarith [h]
  have hB : w.re ^ 2 + w.re + w.im ^ 2 > 0 := by
    have h : (1 / 4 : ℝ) < Complex.normSq ((w : ℂ) + (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ((w : ℂ) + (1 / 2 : ℂ))]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at h
    norm_num at h
    nlinarith [h]
  have hXlt : w.re < w.re ^ 2 + w.im ^ 2 := by linarith
  have hXgt : -(w.re ^ 2 + w.im ^ 2) < w.re := by linarith
  have hX2 : w.re ^ 2 < (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have habs : |w.re| < w.re ^ 2 + w.im ^ 2 := abs_lt.mpr ⟨hXgt, hXlt⟩
    nlinarith [sq_abs w.re, sq_abs (w.re ^ 2 + w.im ^ 2), abs_nonneg w.re,
      abs_nonneg (w.re ^ 2 + w.im ^ 2)]
  have hNsq : Complex.normSq (w : ℂ) = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  have hApos : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  have hAle : w.re ^ 2 + w.im ^ 2 ≤ 2 * w.im := by
    rw [arcT_im_S, hNsq, le_div_iff₀ hApos] at hI
    linarith
  have hAge : w.im ≤ 2 * (w.re ^ 2 + w.im ^ 2) := by
    rw [arcT_im_S, hNsq, div_le_iff₀ hApos] at hII
    linarith
  have h1 : w.re ^ 2 + w.im ^ 2 - (w.re ^ 2 + w.im ^ 2) ^ 2 < w.im ^ 2 := by nlinarith [hX2]
  have h2 : (w.re ^ 2 + w.im ^ 2) ^ 2 ≤ 4 * w.im ^ 2 := by nlinarith [hAle, hApos]
  have hAlt : w.re ^ 2 + w.im ^ 2 < 5 * w.im ^ 2 := by nlinarith [h1, h2]
  have h3 : w.im / 2 < 5 * w.im ^ 2 := by linarith
  nlinarith [h3, hY]

/-- `‖w‖ ≤ 3` on `arcT`. -/
lemma arcT_norm_le {w : ℍ} (hw : w ∈ arcT) : ‖(w : ℂ)‖ ≤ 3 := by
  obtain ⟨hD, hI, -, -⟩ := mem_arcT.mp hw
  obtain ⟨hx1, hx2, -, -⟩ := mem_DomainD.mp hD
  have hY : 0 < w.im := w.im_pos
  have hNsq : Complex.normSq (w : ℂ) = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  have hApos : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  have hAle : w.re ^ 2 + w.im ^ 2 ≤ 2 * w.im := by
    rw [arcT_im_S, hNsq, le_div_iff₀ hApos] at hI
    linarith
  have hsq : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hNsq]
  have hX : w.re ^ 2 ≤ 1 := by nlinarith [hAle, hY, sq_nonneg w.im]
  have hY2 : w.im ≤ 2 := by nlinarith [hAle, sq_nonneg w.re, hY]
  nlinarith [hsq, hX, hY2, norm_nonneg (w : ℂ), sq_nonneg w.im]

/-- The `scale` of a point of `arcT` is at most `14`. -/
lemma arcT_scale_le {w : ℍ} (hw : w ∈ arcT) : Work.Kernels.scale w ≤ 14 := by
  have him := arcT_im_gt hw
  have hnorm := arcT_norm_le hw
  have hinv : (w.im)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ w.im_pos]
    linarith
  simp only [Work.Kernels.scale]
  linarith

end Work.Asymptotics
