import Mathlib
import Submission.Work.NN.Final.twoRec

noncomputable section
open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Final

open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## The `C^∞` level of the Cauchy transform and of the linear extension `dTLM` -/

/-- The one-variable Cauchy transform of a globally `C^∞` datum supported in a disc of radius
`b < ρ` is `C^∞`.  This is `Work.CR.Flat.Cauchy.contDiff_dbarTransform` at every finite level,
collected with `contDiff_iff_forall_nat_le`. -/
lemma contDiff_dbarTransform_top {n : ℕ} {ρ b : ℝ} (hρ : b < ρ) (j : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : ∀ y, b ≤ ‖y j‖ → g y = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (dbarTransform ρ j g) := by
  refine (contDiff_iff_forall_nat_le (n := (⊤ : ℕ∞))).mpr ?_
  intro m hm
  exact contDiff_dbarTransform hρ j m
    ((contDiff_iff_forall_nat_le (n := (⊤ : ℕ∞))).mp hg m hm) hsupp

/-- The linear extension `dTLM j` of the Cauchy transform maps globally `C^∞` functions which
vanish for `cutOut ≤ ‖y j‖` to `C^∞` functions. -/
lemma contDiff_dTLM_top {n : ℕ} {j : Fin n} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : ∀ y, cutOut ≤ ‖y j‖ → g y = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (dTLM j g) := by
  rw [dTLM_eq hg.continuous]
  exact contDiff_dbarTransform_top (by norm_num [cutOut, trRho]) j hg hsupp

/-! ## The recursion preserves `C^∞` -/

lemma uStep_contDiff_top {n : ℕ} {s : Fin n} {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (D i l)) (i l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (uStep s D i l) := by
  by_cases hc : i = s ∨ l = s
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z := by
      funext z; rw [uStep_apply, if_pos hc]; ring
    rw [hfun]
    exact (contDiff_const.sub (contDiff_cutF s)).mul (hD i l)
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z
        + dTLM s (fun y => cutFbar s y * D i l y) z := by
      funext z; rw [uStep_apply, if_neg hc]
    rw [hfun]
    refine ContDiff.add ((contDiff_const.sub (contDiff_cutF s)).mul (hD i l)) ?_
    exact contDiff_dTLM_top ((contDiff_cutFbar s).mul (hD i l))
      (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])

lemma uD_contDiff_top {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (η i l)) :
    ∀ m ≤ n, ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (uD η m i l) := by
  intro m
  induction m with
  | zero => intro _; simpa using hη
  | succ m ih =>
      intro hm i l
      have hm' : m < n := by omega
      rw [uD_succ_of_lt η hm']
      exact uStep_contDiff_top (fun i l => ih (by omega) i l) i l

/-! ## The solution operator -/

theorem uS2_smooth {n : ℕ} (η : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (hη : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (η i l)) : ∀ j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.uS2 η j) := by
  intro j
  have hD := uD_contDiff_top hη
  have hterm : ∀ s : Fin n, ContDiff ℝ (⊤ : ℕ∞) (uPsi η s j) := by
    intro s
    have hs : (s : ℕ) ≤ n := le_of_lt s.isLt
    exact contDiff_dTLM_top ((contDiff_cutF s).mul (hD (s : ℕ) hs s j))
      (fun y hy => by rw [cutF_eq_zero hy, zero_mul])
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ s : Fin n, uPsi η s j z) :=
    ContDiff.sum (fun s _ => hterm s)
  have hgoal : uS2 η j = fun z => ∑ s : Fin n, uPsi η s j z := by
    funext z
    simp [uS2, Finset.sum_apply]
  rw [hgoal]
  exact hsum

end Work.NN.Final
