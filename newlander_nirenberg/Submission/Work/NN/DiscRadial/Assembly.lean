/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The identification `discExt = discUnfoldExt ∘ discSigma`
-/
import Mathlib
import Submission.Work.NN.DiscRadial.Setup
import Submission.Work.NN.DiscRadial.Unfold
import Submission.Work.NN.DiscRadial.Comp

noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter

namespace Work.NN.DiscRadial

open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The unfolding map `discSigma` is smooth away from `p.2 = 0`. -/
lemma contDiffOn_discSigma : ContDiffOn ℝ ⊤ (discSigma (X := X)) {p : X × ℂ | p.2 ≠ 0} := by
  intro p hp
  have h1 : ContDiffWithinAt ℝ ⊤ (fun q : X × ℂ => q.1) {p : X × ℂ | p.2 ≠ 0} p :=
    contDiffWithinAt_id.fst
  have h2 : ContDiffWithinAt ℝ ⊤ (fun q : X × ℂ => q.2 / (‖q.2‖ : ℂ)) {p : X × ℂ | p.2 ≠ 0} p :=
    (contDiffOn_div_norm.contDiffWithinAt hp).comp p contDiffWithinAt_id.snd (fun q hq => hq)
  have h3 : ContDiffWithinAt ℝ ⊤ (fun q : X × ℂ => 1 - ‖q.2‖) {p : X × ℂ | p.2 ≠ 0} p :=
    contDiffWithinAt_const.sub (ContDiffWithinAt.norm ℝ contDiffWithinAt_id.snd hp)
  exact (h1.prodMk h2).prodMk h3

/-- `discRefl b z` is the point of the ray through `z` with radius `1 - b (‖z‖ - 1)`, written as a
real scalar times the unit vector `z/‖z‖`. -/
lemma discRefl_eq_smul (b : ℝ) (z : ℂ) :
    discRefl b z = (1 - b * (‖z‖ - 1)) • (z / (‖z‖ : ℂ)) := by
  rw [discRefl, Complex.real_smul, Complex.real_smul, Complex.ofReal_div]
  ring

/-- The identification `discExt = discUnfoldExt ∘ discSigma` away from `p.2 = 0`. -/
lemma discExt_eq_discUnfoldExt {k : ℕ} {g : X × ℂ → ℂ} {p : X × ℂ} (hp : p.2 ≠ 0) :
    discExt k (discWt k) (discScale) g p = discUnfoldExt k g (discSigma p) := by
  rcases lt_trichotomy ‖p.2‖ 1 with h | h | h
  · rw [discExt_of_norm_lt_one h, discUnfoldExt_of_pos (by show (0:ℝ) < 1 - ‖p.2‖; linarith)]
    show g p = discUnfold g (discSigma p)
    rw [discUnfold_apply']
    simp only [discSigma, Prod.fst, Prod.snd]
    have ha : ((‖p.2‖ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr hp
    have harg : ‖p.2‖ • ((p.2 / (‖p.2‖ : ℂ)) / (‖p.2 / (‖p.2‖ : ℂ)‖ : ℂ)) = p.2 := by
      rw [norm_div_norm_eq_one hp, Complex.ofReal_one, div_one, Complex.real_smul]
      field_simp
    rw [show (1 : ℝ) - (1 - ‖p.2‖) = ‖p.2‖ from by ring, harg]
  · have hlt : ¬ (‖p.2‖ < 1) := by rw [h]; norm_num
    unfold discExt
    rw [if_neg hlt, if_pos h]
    rw [discUnfoldExt_of_eq_zero (by show (1:ℝ) - ‖p.2‖ = 0; linarith), discBdry]
    have hfun : (fun σ : ℝ => discUnfold g ((discSigma p).1, σ))
        = (fun σ : ℝ => g (p.1, (1 - σ) • p.2)) := by
      funext σ
      rw [show (discSigma (X := X) p).1 = (p.1, p.2 / (‖p.2‖ : ℂ)) from rfl, discUnfold_apply']
      simp only [Prod.fst, Prod.snd]
      congr 1
      simp only [h, Complex.ofReal_one, div_one]
    rw [hfun]
    exact (limUnder_comp_one_sub (fun s => g (p.1, s • p.2))).symm
  · have hlt : ¬ (‖p.2‖ < 1) := by intro hc; linarith
    have hne : ¬ (‖p.2‖ = 1) := by intro hc; linarith
    unfold discExt
    rw [if_neg hlt, if_neg hne]
    rw [discUnfoldExt_of_neg (by show (1:ℝ) - ‖p.2‖ < 0; linarith)]
    simp only [discSigma, discSum, discTerm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [discUnfold_apply']
    simp only [Prod.fst, Prod.snd]
    rw [norm_div_norm_eq_one hp, Complex.ofReal_one, div_one]
    congr 2
    · rw [show discScale i * (‖p.2‖ - 1) = -(discScale i) * (1 - ‖p.2‖) from by ring]
    · rw [discRefl_eq_smul]
      rw [show 1 - (-(discScale i) * (1 - ‖p.2‖)) = 1 - discScale i * (‖p.2‖ - 1) from by ring]

end Work.NN.DiscRadial
