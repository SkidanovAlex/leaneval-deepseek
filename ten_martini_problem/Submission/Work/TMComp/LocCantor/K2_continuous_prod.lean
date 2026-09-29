import Mathlib
import Submission.Work.TMComp.LocCantor.C8_jump
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.EllDerivDefs
import Submission.Work.TMComp.Kotani.Psi_bounds
import Submission.Work.TMComp.Kotani.ell_defect_le

/-!
# Joint continuity of the (K2)-integrand along the upper side

The (K2)-integrand `K2 α lam (E₀ + iε) y` is, for fixed `ε > 0`, jointly continuous in
`(E₀, y)`.  Indeed every ingredient (`mfun`, `sSec`, `sigSec`, `defect`, `N₁`, `N₂`) is
continuous in the pair `(E, y)` on the upper half plane (`mfun_props`), the substitution
`E = E₀ + iε` is continuous in `E₀`, and the denominator
`N₁ · N₂ · ‖defect‖²` is strictly positive there (`N1_pos`, `N2_pos`, `defect_ne_zero`), so
the quotient is continuous too.
-/

open MeasureTheory Filter Topology Set
open Work.TMComp.Kotani

namespace Work.TMComp.LocCantor

theorem K2_continuous_prod (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℝ => Work.TMComp.LocCantor.K2 α lam ((p.1 : ℂ) + (ε : ℂ) * Complex.I) p.2) := by
  set E : ℝ → ℂ := fun t => (t : ℂ) + (ε : ℂ) * Complex.I with hEdef
  have hEim : ∀ t : ℝ, (E t).im = ε := by
    intro t
    simp only [E, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one]
    ring
  have hEpos : ∀ t : ℝ, 0 < (E t).im := fun t => by rw [hEim t]; exact hε
  have hEcont : Continuous fun p : ℝ × ℝ => E p.1 := by
    simp only [E]
    exact (Complex.continuous_ofReal.comp continuous_fst).add continuous_const
  have himcont : Continuous fun p : ℝ × ℝ => (E p.1).im := Complex.continuous_im.comp hEcont
  have hmcont : Continuous fun p : ℝ × ℝ => mfun α lam (E p.1) p.2 := by
    have hg : Continuous fun p : ℝ × ℝ => (E p.1, p.2) := hEcont.prodMk continuous_snd
    exact ((mfun_props α lam).2.2.2.2.1).comp_continuous hg (fun p => hEpos p.1)
  have hmcont' : Continuous fun p : ℝ × ℝ => mfun α lam (E p.1) (α - p.2) := by
    have hg : Continuous fun p : ℝ × ℝ => (E p.1, α - p.2) :=
      hEcont.prodMk (continuous_const.sub continuous_snd)
    exact ((mfun_props α lam).2.2.2.2.1).comp_continuous hg (fun p => hEpos p.1)
  have hmne : ∀ p : ℝ × ℝ, mfun α lam (E p.1) p.2 ≠ 0 := by
    intro p h
    have h1 := (mfun_props α lam).2.1 (E p.1) (hEpos p.1) p.2
    rw [h] at h1
    simp at h1
  have hmne' : ∀ p : ℝ × ℝ, mfun α lam (E p.1) (α - p.2) ≠ 0 := by
    intro p h
    have h1 := (mfun_props α lam).2.1 (E p.1) (hEpos p.1) (α - p.2)
    rw [h] at h1
    simp at h1
  have hscont : Continuous fun p : ℝ × ℝ => sSec α lam (E p.1) p.2 :=
    (hmcont'.inv₀ hmne').congr (fun p => by simp [sSec, one_div])
  have hσcont : Continuous fun p : ℝ × ℝ => sigSec α lam (E p.1) p.2 :=
    ((hmcont'.star).inv₀ (fun p => star_ne_zero.mpr (hmne' p))).congr
      (fun p => by simp [sigSec, one_div])
  have hσim : Continuous fun p : ℝ × ℝ => (sigSec α lam (E p.1) p.2).im :=
    Complex.continuous_im.comp hσcont
  have hdcont : Continuous fun p : ℝ × ℝ => defect α lam (E p.1) p.2 :=
    (hmcont.sub hscont).congr (fun p => by simp [defect])
  have hdim : Continuous fun p : ℝ × ℝ => (defect α lam (E p.1) p.2).im :=
    Complex.continuous_im.comp hdcont
  have hN1cont : Continuous fun p : ℝ × ℝ => N1 α lam (E p.1) p.2 :=
    ((Complex.continuous_im.comp hmcont).sub (himcont.div_const 2)).congr
      (fun p => by simp [N1])
  have hN2cont : Continuous fun p : ℝ × ℝ => N2 α lam (E p.1) p.2 :=
    (hσim.add (himcont.div_const 2)).congr (fun p => by simp [N2])
  have hnum : Continuous fun p : ℝ × ℝ =>
      (defect α lam (E p.1) p.2).im *
        ‖(mfun α lam (E p.1) p.2 - E p.1 / 2) - (sigSec α lam (E p.1) p.2 - star (E p.1) / 2)‖ ^ 2 :=
    hdim.mul ((((hmcont.sub (hEcont.div_const 2)).sub
      (hσcont.sub (hEcont.star.div_const 2))).norm).pow 2)
  have hden : Continuous fun p : ℝ × ℝ =>
      N1 α lam (E p.1) p.2 * N2 α lam (E p.1) p.2 * ‖defect α lam (E p.1) p.2‖ ^ 2 :=
    (hN1cont.mul hN2cont).mul (hdcont.norm.pow 2)
  have hdenne : ∀ p : ℝ × ℝ,
      N1 α lam (E p.1) p.2 * N2 α lam (E p.1) p.2 * ‖defect α lam (E p.1) p.2‖ ^ 2 ≠ 0 := by
    intro p
    have h1 := N1_pos α lam (E p.1) (hEpos p.1) p.2
    have h2 := N2_pos α lam (E p.1) (hEpos p.1) p.2
    have h3 : 0 < ‖defect α lam (E p.1) p.2‖ ^ 2 := by
      have h4 := norm_pos_iff.mpr (defect_ne_zero α lam (hEpos p.1) p.2)
      positivity
    positivity
  have hfin := hnum.div hden hdenne
  refine hfin.congr (fun p => ?_)
  simp only [Pi.div_apply, Work.TMComp.LocCantor.K2, hEdef]

end Work.TMComp.LocCantor
