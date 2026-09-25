/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The parameterised `(0,2)`-telescoping preserves `C^k` for every `k`

The one-step operator `uStep G s D = (1 - kappa G s) · D + TL G s (kappabar G s · D)` is *derivative
free*: a product with a smooth cutoff plus a one-variable Cauchy transform of fibre-supported data.
Hence it preserves `C^k` for every `k`, including `k = ⊤`.

The corresponding statements for the fixed cutoff `openCut` are
`Work.NN.Final.uStep_contDiff_k`, `uD_contDiff_k` and `uS2_smooth` in
`Submission/Work/NN/Final/`.
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-! ## Regularity of the recursion at every finite order and at infinite order

The one-step operator `uStep G s D = (1 - kappa G s) · D + TL G s (kappabar G s · D)` is *derivative
free*: a product with a smooth cutoff plus a one-variable Cauchy transform of fibre-supported data.
Hence it preserves `C^k` for every `k`, including `k = ⊤`. -/

lemma uStep_contDiff_k (G : Geom n) {k : ℕ} {s : Fin n}
    {D : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hD : ∀ i l, ContDiff ℝ k (D i l)) (i l : Fin n) :
    ContDiff ℝ k (uStep G s D i l) := by
  by_cases hc : i = s ∨ l = s
  · have hfun : uStep G s D i l = fun z => (1 - kappa G s z) * D i l z := by
      funext z; rw [uStep_apply, if_pos hc]; ring
    rw [hfun]
    exact ((contDiff_const.sub (contDiff_kappa G s)).of_le (by exact_mod_cast le_top)).mul (hD i l)
  · have hfun : uStep G s D i l = fun z => (1 - kappa G s z) * D i l z
        + TL G s (fun y => kappabar G s y * D i l y) z := by
      funext z; rw [uStep_apply, if_neg hc]
    rw [hfun]
    refine ContDiff.add
      (((contDiff_const.sub (contDiff_kappa G s)).of_le (by exact_mod_cast le_top)).mul (hD i l)) ?_
    have hg : ContDiff ℝ k (fun y : Fin n → ℂ => kappabar G s y * D i l y) :=
      ((contDiff_kappabar G s).of_le (by exact_mod_cast le_top)).mul (hD i l)
    rw [TL_eq G s hg.continuous]
    exact contDiff_dbarTransform_univ (G.b_pos s).le s k hg
      (fun y hy => by rw [kappabar_eq_zero_of_ge G s hy, zero_mul])

lemma uD_contDiff_k (G : Geom n) {k : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ k (η i l)) :
    ∀ m ≤ n, ∀ i l, ContDiff ℝ k (uD G η m i l) := by
  intro m
  induction m with
  | zero => intro _; simpa using hη
  | succ m ih =>
      intro hm i l
      have hm' : m < n := by omega
      rw [uD_succ_of_lt G η hm']
      exact uStep_contDiff_k G (fun i l => ih (by omega) i l) i l

lemma uPsi_contDiff_k (G : Geom n) {k : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ k (η i l)) (s : Fin n) :
    ∀ l, ContDiff ℝ k (uPsi G η s l) := by
  intro l
  have hD : ContDiff ℝ k (uD G η (s : ℕ) s l) :=
    uD_contDiff_k G hη (s : ℕ) (le_of_lt s.isLt) s l
  have hg : ContDiff ℝ k (fun y : Fin n → ℂ => kappa G s y * uD G η (s : ℕ) s l y) :=
    ((contDiff_kappa G s).of_le (by exact_mod_cast le_top)).mul hD
  change ContDiff ℝ k (fun z => TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y) z)
  rw [TL_eq G s hg.continuous]
  exact contDiff_dbarTransform_univ (G.b_pos s).le s k hg
    (fun y hy => by rw [kappa_eq_zero G s hy, zero_mul])

lemma S2_contDiff_k (G : Geom n) {k : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ k (η i l)) (j : Fin n) :
    ContDiff ℝ k (S2 G η j) := by
  have hgoal : S2 G η j = fun z => ∑ s : Fin n, uPsi G η s j z := by
    funext z
    rw [S2_apply]
  rw [hgoal]
  exact ContDiff.sum (fun s _ => uPsi_contDiff_k G hη s j)

lemma S2_contDiff_top (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (η i l)) (j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (S2 G η j) := by
  refine (contDiff_iff_forall_nat_le (n := (⊤ : ℕ∞))).mpr fun m hm => ?_
  exact S2_contDiff_k G
    (fun i l => (contDiff_iff_forall_nat_le (n := (⊤ : ℕ∞))).mp (hη i l) m hm) j


end Work.NN.Core.TelTwoDF
