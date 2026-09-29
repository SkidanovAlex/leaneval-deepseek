import Mathlib
import Submission.Work.CPull.phiC_ext_defs
import Submission.Work.CPsi.psiC_base

/-!
# CPull — `psiF` is the two-sided analytic inverse of the contour map `psiC`

The contour map is `psiC z = -(3/4) * lune (23/10) z`, the inverse of `psiF` is the explicit
rational map `psiF w = luneF (-(4/3) w)`, where

`luneF w = w (B + C w) / (C + B w)`,  `B = 1 + (23/10)² = 629/100`,  `C = (23/10)² - 1 = 429/100`.

This module proves that `psiF ∘ psiC = id` (`psiC_psiF`) and that `psiF` is holomorphic at every
point of the image `psiC(ℂ)` of the contour map.

The algebraic heart is already in `Submission.Work.CPsi.psiC_base`: with `gobL = lune (23/10)`
and `gobF w = w (gB + gC w)/(gC + gB w)`, `psiC_base` proves `gobF (gobL z) = z` for every `z`
and `gC + gB * gobL z ≠ 0`.  We only translate `psiF`, `psiC` into `gobF`, `gobL`.
-/

namespace Work.CPull

open Submission.CDTPlan

noncomputable section

/-- `luneF` is the explicit rational map `gobF w = w (gB + gC w)/(gC + gB w)` of `CPsi.psiC_base`:
the numerical constants `1 + gammaC`, `gammaC - 1` are `gB = 629/100`, `gC = 429/100`. -/
theorem luneF_eq_gobF (w : ℂ) : luneF w = Work.CPsi.gobF w := by
  have h1 : (1 : ℂ) + gammaC = Work.CPsi.gB := by
    simp only [gammaC, Work.CPsi.gB, Work.CPsi.gBr]
    push_cast
    norm_num
  have h2 : gammaC - 1 = Work.CPsi.gC := by
    simp only [gammaC, Work.CPsi.gC, Work.CPsi.gCr]
    push_cast
    norm_num
  simp only [luneF, Work.CPsi.gobF, h1, h2]

/-- `psiC z = -(3/4) * gobL z`, with `gobL = lune (23/10)`. -/
theorem psiC_eq_neg_gobL (z : ℂ) :
    Submission.CDTPlan.psiC z = -(3 / 4) * Work.CPsi.gobL z := by
  simp only [Submission.CDTPlan.psiC, Work.CPsi.lune_eq]

/-- `psiF` is the map `w ↦ gobF (-(4/3) w)`. -/
theorem psiF_eq (w : ℂ) : psiF w = Work.CPsi.gobF (-(4 / 3) * w) := by
  simp only [psiF, luneF_eq_gobF]

/-- `-(4/3) * psiC z = gobL z`. -/
theorem neg_four_thirds_psiC (z : ℂ) :
    -(4 / 3) * Submission.CDTPlan.psiC z = Work.CPsi.gobL z := by
  rw [psiC_eq_neg_gobL]; ring

/-- `psiF` is a left inverse of `psiC`. -/
theorem psiF_psiC (z : ℂ) : psiF (Submission.CDTPlan.psiC z) = z := by
  rw [psiF_eq, neg_four_thirds_psiC, Work.CPsi.gobF_gobL]

/-- `gobF` is holomorphic wherever its denominator `gC + gB w` does not vanish. -/
theorem differentiableAt_gobF {w : ℂ} (h : Work.CPsi.gC + Work.CPsi.gB * w ≠ 0) :
    DifferentiableAt ℂ Work.CPsi.gobF w := by
  have hnum : DifferentiableAt ℂ (fun v : ℂ => v * (Work.CPsi.gB + Work.CPsi.gC * v)) w :=
    differentiableAt_id.mul
      ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id))
  have hden : DifferentiableAt ℂ (fun v : ℂ => Work.CPsi.gC + Work.CPsi.gB * v) w :=
    (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)
  unfold Work.CPsi.gobF
  exact hnum.div hden h

/-- `psiF` is holomorphic at every point of `psiC(ℂ)`. -/
theorem differentiableAt_psiF (z : ℂ) :
    DifferentiableAt ℂ psiF (Submission.CDTPlan.psiC z) := by
  have hfun : psiF = fun w : ℂ => Work.CPsi.gobF (-(4 / 3) * w) := funext psiF_eq
  rw [hfun]
  refine (differentiableAt_gobF ?_).comp (Submission.CDTPlan.psiC z)
    ((differentiableAt_const _).mul differentiableAt_id)
  rw [neg_four_thirds_psiC]
  exact Work.CPsi.gobL_pole_ne z

end

theorem psiC_psiF :
    (∀ z : ℂ, Work.CPull.psiF (Submission.CDTPlan.psiC z) = z) ∧
    (∀ z : ℂ, DifferentiableAt ℂ Work.CPull.psiF (Submission.CDTPlan.psiC z)) :=
  ⟨psiF_psiC, differentiableAt_psiF⟩

end Work.CPull
