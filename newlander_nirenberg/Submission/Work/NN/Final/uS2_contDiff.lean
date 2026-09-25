import Mathlib
import Submission.Work.NN.Final.twoRec
import Submission.Work.NN.Final.uS2_smooth
import Submission.Work.CR.Flat.Cauchy.contDiff_dbarTransform

noncomputable section
open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Final

open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## Finite-order regularity of the Cauchy transform and the linear extension `dTLM` -/

/-- The one-variable Cauchy transform of a `C^m` datum supported in a disc of radius `b < ρ` is
`C^m`; this is `Work.CR.Flat.Cauchy.contDiff_dbarTransform` restated at the order `(m : ℕ∞)`. -/
lemma contDiff_dbarTransform_fin {n : ℕ} {ρ b : ℝ} (hρ : b < ρ) (j : Fin n) (m : ℕ)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ (m : ℕ∞) g)
    (hsupp : ∀ y, b ≤ ‖y j‖ → g y = 0) :
    ContDiff ℝ (m : ℕ∞) (dbarTransform ρ j g) :=
  contDiff_dbarTransform hρ j m (by simpa using hg) hsupp

/-- The linear extension `dTLM j` of the Cauchy transform maps `C^m` functions which vanish for
`cutOut ≤ ‖y j‖` to `C^m` functions. -/
lemma contDiff_dTLM_fin {n : ℕ} {j : Fin n} (m : ℕ) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ (m : ℕ∞) g) (hsupp : ∀ y, cutOut ≤ ‖y j‖ → g y = 0) :
    ContDiff ℝ (m : ℕ∞) (dTLM j g) := by
  rw [dTLM_eq hg.continuous]
  exact contDiff_dbarTransform_fin (b := cutOut) (by norm_num [cutOut, trRho]) j m hg hsupp

/-! ## The recursion preserves `C^m` -/

lemma uStep_contDiff_fin {n : ℕ} (m : ℕ) {s : Fin n} {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l, ContDiff ℝ (m : ℕ∞) (D i l)) (i l : Fin n) :
    ContDiff ℝ (m : ℕ∞) (uStep s D i l) := by
  by_cases hc : i = s ∨ l = s
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z := by
      funext z; rw [uStep_apply, if_pos hc]; ring
    rw [hfun]
    exact ((contDiff_const.sub (contDiff_cutF s)).of_le (le_infty_omega m)).mul (hD i l)
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z
        + dTLM s (fun y => cutFbar s y * D i l y) z := by
      funext z; rw [uStep_apply, if_neg hc]
    rw [hfun]
    refine ContDiff.add
      (((contDiff_const.sub (contDiff_cutF s)).of_le (le_infty_omega m)).mul (hD i l)) ?_
    exact contDiff_dTLM_fin m
      (((contDiff_cutFbar s).of_le (le_infty_omega m)).mul (hD i l))
      (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])

lemma uD_contDiff_fin {n : ℕ} (m : ℕ) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ (m : ℕ∞) (η i l)) :
    ∀ k ≤ n, ∀ i l, ContDiff ℝ (m : ℕ∞) (uD η k i l) := by
  intro k
  induction k with
  | zero => intro _; simpa using hη
  | succ k ih =>
      intro hk i l
      have hk' : k < n := by omega
      rw [uD_succ_of_lt η hk']
      exact uStep_contDiff_fin m (fun i l => ih (by omega) i l) i l

/-! ## The solution operator -/

/-- **Regularity of the `(0,2)`-solver `uS2` at finite order.**  `Work.NN.Final.uS2` is a finite
sum `∑ s, dTLM s (cutF s · uD η s s ·)` where `uD` is built by the derivative-free recursion
`uStep s D = (1 - cutF s) · D + dTLM s (cutFbar s · D)`; every operation is a multiplication by a
fixed smooth cutoff or the one-variable Cauchy transform `dTLM`, which preserves finite
regularity (`Work.CR.Flat.Cauchy.contDiff_dbarTransform` is stated for every `m : ℕ`, and
`contDiff_dTLM`, `uStep_contDiff`, `uD_contDiff` in `Submission/Work/NN/Final/twoRec.lean` already
give the order-`1` case used by the proved `uS2_solves`).

This is the finite-order version of the proved `Work.NN.Final.uS2_smooth`
(`Submission/Work/NN/Final/uS2_smooth.lean`), whose proof should be copied verbatim with
`ContDiff ℝ (⊤ : ℕ∞)` replaced by `ContDiff ℝ (m : ℕ∞)`; it is needed to apply the
composition bound `holderNorm_comp_linear` to `uS2 η`. -/
theorem uS2_contDiff {n : ℕ} (m : ℕ) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ (m : ℕ∞) (η i l)) :
    ∀ j : Fin n, ContDiff ℝ (m : ℕ∞) (Work.NN.Final.uS2 η j) := by
  intro j
  have hD := uD_contDiff_fin m hη
  have hterm : ∀ s : Fin n, ContDiff ℝ (m : ℕ∞) (uPsi η s j) := by
    intro s
    have hs : (s : ℕ) ≤ n := le_of_lt s.isLt
    show ContDiff ℝ (m : ℕ∞) (dTLM s (fun y => cutF s y * uD η (s : ℕ) s j y))
    exact contDiff_dTLM_fin m
      (((contDiff_cutF s).of_le (le_infty_omega m)).mul (hD (s : ℕ) hs s j))
      (fun y hy => by rw [cutF_eq_zero hy, zero_mul])
  have hsum : ContDiff ℝ (m : ℕ∞) (fun z => ∑ s : Fin n, uPsi η s j z) :=
    ContDiff.sum (fun s _ => hterm s)
  have hgoal : uS2 η j = fun z => ∑ s : Fin n, uPsi η s j z := by
    funext z
    simp [uS2, Finset.sum_apply]
  rw [hgoal]
  exact hsum

end Work.NN.Final
