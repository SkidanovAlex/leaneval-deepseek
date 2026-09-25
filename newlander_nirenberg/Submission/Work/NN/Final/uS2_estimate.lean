/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `C^{0,α}` estimate for the `(0,2)`-solver `uS2`

`Work.NN.Final.uS2` is the explicit solution operator of the `(0,2)`-`∂̄`-recursion on the unit
polydisc (`Work.NN.Final.twoRec`).  This file proves the uniform `C^{0,α}` estimate

  `‖uS2 η‖_{C^{0,α}(solveSet)} ≤ C · ∑_{i,l} ‖η_{il}‖_{C^{0,α}(P(0,1))}`,

with a constant `C` depending only on `n`, `α` and the fixed absolute constants of the cutoff
`openCut` — in particular independent of the datum `η`.

The proof is a stage-by-stage induction on the recursion, exactly as in
`Work.CR.Flat.Cauchy.recF_stage_bound` for the `(0,1)`-recursion:

* `uK` is the uniform constant of one step of the recursion;
* `one_sub_cutF_bound` bounds the `(1 - cutF)`-factor of one step;
* `dbarTransform_track_bound` bounds the Cauchy-transform factor, using the fibre estimates of
  `exists_uniform_dbarC_bound` and `dbarTransform_basic`;
* `uD_stage_bound` assembles the two into the induction;
* `uPsi_bound` bounds the summands `uPsi η σ l = T_σ(cutF σ · uD η σ σ l)` on `solveSet`;
* `uS2_estimate` sums over `σ` and converts the pointwise and Hölder bounds into the
  `holderNorm` bound.
-/
import Mathlib
import Submission.Work.NN.Final.twoRec
import Submission.Work.CR.Flat.Cauchy.cutFbar_mul_bound_uniform
import Submission.Work.CR.Flat.Cauchy.cutF_mul_fiber_holder_two_add
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic
import Submission.Work.CR.Flat.Cauchy.recU_estimate_uniform

noncomputable section
open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Final
open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## The uniform constant of the recursion -/

/-- The constant `K` of the stage estimate for the `(0,2)`-recursion.  It dominates every
coefficient produced by a single step of the recursion: the cutoff factor `2` of `1 - cutF`,
the Lipschitz constants of the cutoffs, and the Cauchy-transform constant `2 * trRho * C₀`. -/
def uK (L C₀ : ℝ) : ℝ := L + 4 * trRho * C₀ + 131

lemma uK_pos {L C₀ : ℝ} (hL0 : 0 ≤ L) (hC₀ : 0 ≤ C₀) : 0 < uK L C₀ := by
  have htr : (0 : ℝ) ≤ 4 * trRho := by have := trRho_pos; linarith
  have h : 0 ≤ 4 * trRho * C₀ := mul_nonneg htr hC₀
  unfold uK; linarith

lemma uK_one_le {L C₀ : ℝ} (hL0 : 0 ≤ L) (hC₀ : 0 ≤ C₀) : 1 ≤ uK L C₀ := by
  have htr : (0 : ℝ) ≤ 4 * trRho := by have := trRho_pos; linarith
  have h : 0 ≤ 4 * trRho * C₀ := mul_nonneg htr hC₀
  unfold uK; linarith

lemma uK_sup_le {L C₀ : ℝ} (hL0 : 0 ≤ L) (hC₀ : 0 ≤ C₀) :
    2 + 2 * trRho * C₀ ≤ uK L C₀ := by
  have h : 0 ≤ trRho * C₀ := mul_nonneg (le_of_lt trRho_pos) hC₀
  unfold uK; linarith

lemma uK_hol_le {L C₀ : ℝ} : 2 + L + 128 + 4 * trRho * C₀ ≤ uK L C₀ := by
  unfold uK; linarith

lemma uK_two_le {L C₀ : ℝ} (hL0 : 0 ≤ L) (hC₀ : 0 ≤ C₀) : 2 ≤ uK L C₀ := by
  have htr : (0 : ℝ) ≤ 4 * trRho := by have := trRho_pos; linarith
  have h : 0 ≤ 4 * trRho * C₀ := mul_nonneg htr hC₀
  unfold uK; linarith

lemma uK_nt_le {L C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 2 + L + 128 ≤ uK L C₀ := by
  have htr : (0 : ℝ) ≤ 4 * trRho := by have := trRho_pos; linarith
  have h : 0 ≤ 4 * trRho * C₀ := mul_nonneg htr hC₀
  unfold uK; linarith

/-! ## The datum bounds -/

/-- A single term of a double sum of nonnegative terms is bounded by the double sum. -/
lemma double_sum_le_sum {α : ℝ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} (i l : Fin n) :
    holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) ≤
      ∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) := by
  have h1 : holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))
      ≤ ∑ l', holderNorm 0 α (η i l') (polydisc 0 (fun _ => 1)) :=
    Finset.single_le_sum (f := fun l' => holderNorm 0 α (η i l') (polydisc 0 (fun _ => 1)))
      (fun _ _ => zero_le) (Finset.mem_univ l)
  have h2 : (∑ l', holderNorm 0 α (η i l') (polydisc 0 (fun _ => 1)))
      ≤ ∑ i', ∑ l', holderNorm 0 α (η i' l') (polydisc 0 (fun _ => 1)) :=
    Finset.single_le_sum
      (f := fun i' => ∑ l', holderNorm 0 α (η i' l') (polydisc 0 (fun _ => 1)))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => zero_le)) (Finset.mem_univ i)
  exact le_trans h1 h2

/-- If the double sum of the `C^{0,α}`-norms of the coefficients of `η` on the unit polydisc is
finite, then so is each individual norm. -/
lemma holderNorm_ne_top_of_dsum_ne_top {α : ℝ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hS : (∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))) ≠ ⊤) :
    ∀ i l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) ≠ ⊤ := by
  intro i l hil
  refine hS ?_
  have hle : holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) ≤
      ∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) :=
    double_sum_le_sum i l
  rw [hil] at hle
  exact top_le_iff.mp hle

/-- Pointwise bound on the tracked polydisc by the sum of the `C^{0,α}`-norms of the datum. -/
lemma eta_sup_track {α : ℝ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hS : (∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))) ≠ ⊤)
    (i l : Fin n) {z : Fin n → ℂ} (hz : z ∈ trackSet) :
    ‖η i l z‖ ≤ (∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))).toReal := by
  have hfin := holderNorm_ne_top_of_dsum_ne_top hS
  have hle : holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) ≤
      ∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) :=
    double_sum_le_sum i l
  have h1 : ENNReal.ofReal ‖η i l z‖ ≤ holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) :=
    norm_apply_le_holderNorm 0 α (η i l) _ (trackSet_subset_unit hz)
  have h2 : ‖η i l z‖ ≤ (holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (hfin i l)).mp h1
  exact le_trans h2 (ENNReal.toReal_mono hS hle)

/-- Hölder bound on the tracked polydisc by the sum of the `C^{0,α}`-norms of the datum. -/
lemma eta_holder_track {α : ℝ} (hα : 0 < α) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hS : (∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))) ≠ ⊤)
    (i l : Fin n) {x y : Fin n → ℂ} (hx : x ∈ trackSet) (hy : y ∈ trackSet) :
    ‖η i l x - η i l y‖
      ≤ (∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))).toReal * ‖x - y‖ ^ α := by
  have hfin := holderNorm_ne_top_of_dsum_ne_top hS
  have hle : holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) ≤
      ∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) :=
    double_sum_le_sum i l
  have hS0 : (0 : ℝ) ≤ (∑ i, ∑ l, holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))).toReal :=
    ENNReal.toReal_nonneg
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, norm_zero]
    exact mul_nonneg hS0 (Real.rpow_nonneg (norm_nonneg _) α)
  · have hx' := trackSet_subset_unit hx
    have hy' := trackSet_subset_unit hy
    have hD : ‖iteratedFDerivWithin ℝ 0 (η i l) (polydisc 0 (fun _ => 1)) x
        - iteratedFDerivWithin ℝ 0 (η i l) (polydisc 0 (fun _ => 1)) y‖
        = ‖η i l x - η i l y‖ := by
      rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
    have h1 : ENNReal.ofReal (‖η i l x - η i l y‖ / ‖x - y‖ ^ α)
        ≤ holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1)) := by
      rw [← hD]
      exact le_trans (le_holderSeminorm 0 α (η i l) _ hx' hy' hxy)
        (holderSeminorm_le_holderNorm 0 α (η i l) _ (le_refl 0))
    have h2 : ‖η i l x - η i l y‖ / ‖x - y‖ ^ α
        ≤ (holderNorm 0 α (η i l) (polydisc 0 (fun _ => 1))).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin i l)).mp h1
    have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (by rwa [norm_pos_iff, sub_ne_zero]) α
    have hmul : (‖η i l x - η i l y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α = ‖η i l x - η i l y‖ :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (le_trans h2 (ENNReal.toReal_mono hS hle)) (le_of_lt hpos)

/-! ## The two elementary estimates for one step -/

/-- For `0 ≤ d ≤ 1` and `0 < α ≤ 1` one has `d ≤ d ^ α`. -/
lemma self_le_rpow {d α : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    d ≤ d ^ α := by
  rcases eq_or_lt_of_le hd0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt hα0)]
  · have hle : d ^ (1 : ℝ) ≤ d ^ α := Real.rpow_le_rpow_of_exponent_ge h hd1 hα1
    rwa [Real.rpow_one] at hle

/-- **The `(1 - cutF)`-factor of one step.**  If `F` is bounded by `A` and Hölder with constant
`A` on the tracked polydisc, then so is `(1 - cutF j) F`, with constants `2` and `2 + L + 128`. -/
private lemma one_sub_cutF_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {j : Fin n} {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖)
    {F : (Fin n → ℂ) → ℂ} {A : ℝ} (hA0 : 0 ≤ A)
    (hF : ∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A)
    (hFh : ∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
      ‖F x - F y‖ ≤ A * ‖x - y‖ ^ α) :
    (∀ z, z ∈ trackSet → ‖(1 - cutF j z) * F z‖ ≤ 2 * A) ∧
    (∀ x y, x ∈ trackSet → y ∈ trackSet →
      ‖(1 - cutF j x) * F x - (1 - cutF j y) * F y‖
        ≤ (2 + L + 128) * A * ‖x - y‖ ^ α) := by
  have hone : ∀ z : Fin n → ℂ, ‖(1 : ℂ) - cutF j z‖ ≤ 2 := by
    intro z
    calc ‖(1 : ℂ) - cutF j z‖ ≤ ‖(1 : ℂ)‖ + ‖cutF j z‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          rw [norm_one]
          exact add_le_add le_rfl (norm_cutF_le_one j z)
      _ = 2 := by norm_num
  constructor
  · intro z hz
    rw [norm_mul]
    exact mul_le_mul (hone z) (hF z hz) (norm_nonneg _) (by norm_num)
  · intro x y hx hy
    have h1 : ‖(1 - cutF j x) * (F x - F y)‖ ≤ 2 * (A * ‖x - y‖ ^ α) := by
      rw [norm_mul]
      exact mul_le_mul (hone x) (hFh x y hx hy) (norm_nonneg _) (by norm_num)
    have h2 : ‖(cutF j y - cutF j x) * F y‖ ≤ (L * ‖x - y‖) * A := by
      rw [norm_mul]
      have hle : ‖cutF j y - cutF j x‖ ≤ L * ‖x - y‖ := by
        rw [norm_sub_rev]
        exact norm_cutF_sub_le j hL0 hLip x y
      exact mul_le_mul hle (hF y hy) (norm_nonneg _) (mul_nonneg hL0 (norm_nonneg _))
    have hsplit : (1 - cutF j x) * F x - (1 - cutF j y) * F y
        = (1 - cutF j x) * (F x - F y) + (cutF j y - cutF j x) * F y := by ring
    have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hD0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg hd0 α
    by_cases hbig : (1 / 32 : ℝ) ≤ ‖x - y‖
    · have h1' : ‖(1 - cutF j x) * F x‖ ≤ 2 * A := by
        rw [norm_mul]
        exact mul_le_mul (hone x) (hF x hx) (norm_nonneg _) (by norm_num)
      have h2' : ‖(1 - cutF j y) * F y‖ ≤ 2 * A := by
        rw [norm_mul]
        exact mul_le_mul (hone y) (hF y hy) (norm_nonneg _) (by norm_num)
      have hD32 : (1 / 32 : ℝ) ≤ ‖x - y‖ ^ α := by
        have hb : (1 / 32 : ℝ) ≤ (1 / 32 : ℝ) ^ α :=
          self_le_rpow (by norm_num) (by norm_num) hα0 (le_of_lt hα1)
        exact le_trans hb (Real.rpow_le_rpow (by norm_num) hbig (le_of_lt hα0))
      calc ‖(1 - cutF j x) * F x - (1 - cutF j y) * F y‖
          ≤ ‖(1 - cutF j x) * F x‖ + ‖(1 - cutF j y) * F y‖ := norm_sub_le _ _
        _ ≤ 2 * A + 2 * A := add_le_add h1' h2'
        _ = 4 * A := by ring
        _ ≤ (2 + L + 128) * A * ‖x - y‖ ^ α := by
            have h4 : 4 * A ≤ (2 + L + 128) * A * (1 / 32) := by nlinarith [hA0, hL0]
            have hc : 0 ≤ (2 + L + 128) * A := mul_nonneg (by linarith) hA0
            exact le_trans h4 (mul_le_mul_of_nonneg_left hD32 hc)
    · have hsmall : ‖x - y‖ < 1 / 32 := not_le.mp hbig
      have hd1 : ‖x - y‖ ≤ 1 := by linarith
      have hdα : ‖x - y‖ ≤ ‖x - y‖ ^ α :=
        self_le_rpow hd0 hd1 hα0 (le_of_lt hα1)
      calc ‖(1 - cutF j x) * F x - (1 - cutF j y) * F y‖
          = ‖(1 - cutF j x) * (F x - F y) + (cutF j y - cutF j x) * F y‖ := by rw [hsplit]
        _ ≤ ‖(1 - cutF j x) * (F x - F y)‖ + ‖(cutF j y - cutF j x) * F y‖ := norm_add_le _ _
        _ ≤ 2 * (A * ‖x - y‖ ^ α) + (L * ‖x - y‖) * A := add_le_add h1 h2
        _ ≤ 2 * (A * ‖x - y‖ ^ α) + (L * ‖x - y‖ ^ α) * A := by
            have hle : (L * ‖x - y‖) * A ≤ (L * ‖x - y‖ ^ α) * A :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdα hL0) hA0
            exact add_le_add le_rfl hle
        _ ≤ (2 + L + 128) * A * ‖x - y‖ ^ α := by
            nlinarith [hA0, hL0, hD0, mul_nonneg hA0 hD0]

/-- **The Cauchy-transform step.**  Given the fibre bounds of `cutFbar j · F` (as produced by
`exists_uniform_dbarC_bound`), the Cauchy transform of that function is bounded and Hölder on
the tracked polydisc. -/
private lemma dbarTransform_track_bound {α : ℝ} {j : Fin n} {C₀ : ℝ}
    (hC₀prop : ∀ {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
      (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
      (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
        ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
      (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
        ‖dbarC openCut (z j) * F z‖ ≤ C₀ * A) ∧
      (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
        (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
        ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
          ≤ C₀ * (A + H) * ‖a - a'‖ ^ α))
    {F : (Fin n → ℂ) → ℂ} (hFcont : Continuous F)
    {A H : ℝ} (hA0 : 0 ≤ A) (hH0 : 0 ≤ H)
    (hA : ∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A)
    (hH : ∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
      ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) :
    (∀ z, z ∈ trackSet → ‖dbarTransform trRho j (fun y => cutFbar j y * F y) z‖
        ≤ 2 * trRho * C₀ * A) ∧
    (∀ x y, x ∈ trackSet → y ∈ trackSet →
      ‖dbarTransform trRho j (fun y => cutFbar j y * F y) x
        - dbarTransform trRho j (fun y => cutFbar j y * F y) y‖
        ≤ 2 * trRho * C₀ * (A + H) * ‖x - y‖ ^ α) := by
  set g : (Fin n → ℂ) → ℂ := fun y => cutFbar j y * F y with hg
  have hgcont : Continuous g := (contDiff_cutFbar j).continuous.mul hFcont
  have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y j‖ → g y = 0 := by
    intro y hy
    rw [hg]
    simp only
    rw [cutFbar_eq_zero_of_ge hy, zero_mul]
  obtain ⟨hf1, hf2⟩ := hC₀prop hA0 hH0 hA hH
  constructor
  · intro z hz
    have hbd : ∀ y : Fin n → ℂ, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ cutOut →
        ‖g y‖ ≤ C₀ * A := by
      intro y hy hyj
      have hyt : ∀ l, l ≠ j → ‖y l‖ < trTrack := fun l hl => by rw [hy l hl]; exact hz l
      exact hf1 y hyt hyj
    have h := (dbarTransform_basic (n := n) (ρ := trRho) (b := cutOut) trRho_pos
      (le_of_lt cutOut_pos) (j := j)).1 hgcont hsupp (C₀ * A) z hbd
    calc ‖dbarTransform trRho j g z‖ ≤ 2 * trRho * (C₀ * A) := h
      _ = 2 * trRho * C₀ * A := by ring
  · intro x y hx hy
    have hhold : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → a l = x l) →
        (∀ l, l ≠ j → a' l = y l) →
        ‖g a - g a'‖ ≤ (C₀ * (A + H)) * ‖a - a'‖ ^ α := by
      intro a a' ha ha'
      have hat : ∀ l, l ≠ j → ‖a l‖ < trTrack := fun l hl => by rw [ha l hl]; exact hx l
      have ha't : ∀ l, l ≠ j → ‖a' l‖ < trTrack := fun l hl => by rw [ha' l hl]; exact hy l
      exact hf2 a a' hat ha't
    have h := (dbarTransform_basic (n := n) (ρ := trRho) (b := cutOut) trRho_pos
      (le_of_lt cutOut_pos) (j := j)).2.1 hgcont hsupp α (C₀ * (A + H)) x y hhold
    calc ‖dbarTransform trRho j g x - dbarTransform trRho j g y‖
        ≤ 2 * trRho * (C₀ * (A + H)) * ‖x - y‖ ^ α := h
      _ = 2 * trRho * C₀ * (A + H) * ‖x - y‖ ^ α := by ring

/-! ## The stage estimate for the recursion -/

/-- **The `C^{0,α}`-stage estimate for the `(0,2)`-recursion.**  If the datum `η` is bounded by
`S` and Hölder with constant `S` on `trackSet`, then so is every stage `uD η m` (with constants
`K ^ m * S`, `K = uK L C₀`), for all `m ≤ n`. -/
private theorem uD_stage_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {L C₀ : ℝ} (hL0 : 0 ≤ L) (hC₀pos : 0 < C₀)
    (hLip : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖)
    (hC₀prop : ∀ (j : Fin n) {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
      (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
      (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
        ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
      (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
        ‖dbarC openCut (z j) * F z‖ ≤ C₀ * A) ∧
      (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
        (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
        ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
          ≤ C₀ * (A + H) * ‖a - a'‖ ^ α))
    {S : ℝ} (hS0 : 0 ≤ S) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hA : ∀ i l z, z ∈ trackSet → ‖η i l z‖ ≤ S)
    (hH : ∀ i l x y, x ∈ trackSet → y ∈ trackSet →
      ‖η i l x - η i l y‖ ≤ S * ‖x - y‖ ^ α) :
    ∀ m ≤ n, ∀ i l,
      (∀ z, z ∈ trackSet → ‖uD η m i l z‖ ≤ uK L C₀ ^ m * S) ∧
      (∀ x y, x ∈ trackSet → y ∈ trackSet →
        ‖uD η m i l x - uD η m i l y‖ ≤ uK L C₀ ^ m * S * ‖x - y‖ ^ α) := by
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  have hKpos : 0 < uK L C₀ := uK_pos hL0 hC₀nn
  have hK2 : 2 ≤ uK L C₀ := uK_two_le hL0 hC₀nn
  have hKsup : 2 + 2 * trRho * C₀ ≤ uK L C₀ := uK_sup_le hL0 hC₀nn
  have hKhol : 2 + L + 128 + 4 * trRho * C₀ ≤ uK L C₀ := uK_hol_le
  have hKnt : 2 + L + 128 ≤ uK L C₀ := uK_nt_le hC₀nn
  intro m
  induction m with
  | zero =>
      intro _ i l
      exact ⟨fun z hz => by simpa using hA i l z hz,
             fun x y hx hy => by simpa using hH i l x y hx hy⟩
  | succ m ih =>
      intro hm1 i l
      have hm : m ≤ n := Nat.le_of_succ_le hm1
      have hmlt : m < n := Nat.lt_of_succ_le hm1
      obtain ⟨hAm, hHm⟩ := ih hm i l
      have hDcont : Continuous (uD η m i l) := (uD_contDiff hη m hm i l).continuous
      have hA0 : 0 ≤ uK L C₀ ^ m * S := mul_nonneg (pow_nonneg hKpos.le m) hS0
      have hstep : uD η (m + 1) i l = uStep ⟨m, hmlt⟩ (uD η m) i l := by
        rw [uD_succ_of_lt η hmlt]
      rw [hstep]
      set j : Fin n := ⟨m, hmlt⟩ with hj
      have hnt := one_sub_cutF_bound (n := n) hα0 hα1 (j := j) hL0 hLip hA0 hAm hHm
      have hT := dbarTransform_track_bound (n := n) (α := α) (j := j) (C₀ := C₀)
        (hC₀prop j) hDcont hA0 hA0 hAm hHm
      by_cases hic : i = j ∨ l = j
      · have hfun : uStep j (uD η m) i l = fun z => (1 - cutF j z) * uD η m i l z := by
          funext z; rw [uStep_apply, if_pos hic]; ring
        rw [hfun]
        refine ⟨?_, ?_⟩
        · intro z hz
          calc ‖(1 - cutF j z) * uD η m i l z‖ ≤ 2 * (uK L C₀ ^ m * S) := hnt.1 z hz
            _ ≤ uK L C₀ * (uK L C₀ ^ m * S) := mul_le_mul_of_nonneg_right (by linarith) hA0
            _ = uK L C₀ ^ (m + 1) * S := by rw [pow_succ]; ring
        · intro x y hx hy
          calc ‖(1 - cutF j x) * uD η m i l x - (1 - cutF j y) * uD η m i l y‖
              ≤ (2 + L + 128) * (uK L C₀ ^ m * S) * ‖x - y‖ ^ α := hnt.2 x y hx hy
            _ ≤ uK L C₀ * (uK L C₀ ^ m * S) * ‖x - y‖ ^ α := by
                have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (by linarith) hA0) hd
            _ = uK L C₀ ^ (m + 1) * S * ‖x - y‖ ^ α := by rw [pow_succ]; ring
      · have hfun : uStep j (uD η m) i l
            = fun z => (1 - cutF j z) * uD η m i l z
              + dTLM j (fun y => cutFbar j y * uD η m i l y) z := by
          funext z; rw [uStep_apply, if_neg hic]
        have hgcont : Continuous (fun y => cutFbar j y * uD η m i l y) :=
          (contDiff_cutFbar j).continuous.mul hDcont
        rw [hfun, dTLM_eq hgcont]
        refine ⟨?_, ?_⟩
        · intro z hz
          calc ‖(1 - cutF j z) * uD η m i l z
                + dbarTransform trRho j (fun y => cutFbar j y * uD η m i l y) z‖
              ≤ ‖(1 - cutF j z) * uD η m i l z‖
                + ‖dbarTransform trRho j (fun y => cutFbar j y * uD η m i l y) z‖ :=
                  norm_add_le _ _
            _ ≤ 2 * (uK L C₀ ^ m * S) + 2 * trRho * C₀ * (uK L C₀ ^ m * S) :=
                  add_le_add (hnt.1 z hz) (hT.1 z hz)
            _ = (2 + 2 * trRho * C₀) * (uK L C₀ ^ m * S) := by ring
            _ ≤ uK L C₀ * (uK L C₀ ^ m * S) := mul_le_mul_of_nonneg_right hKsup hA0
            _ = uK L C₀ ^ (m + 1) * S := by rw [pow_succ]; ring
        · intro x y hx hy
          have hsplit : ((1 - cutF j x) * uD η m i l x
                + dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') x)
              - ((1 - cutF j y) * uD η m i l y
                + dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') y)
              = ((1 - cutF j x) * uD η m i l x - (1 - cutF j y) * uD η m i l y)
                + (dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') x
                  - dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') y) := by
              ring
          rw [hsplit]
          calc ‖((1 - cutF j x) * uD η m i l x - (1 - cutF j y) * uD η m i l y)
                + (dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') x
                  - dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') y)‖
              ≤ ‖(1 - cutF j x) * uD η m i l x - (1 - cutF j y) * uD η m i l y‖
                + ‖dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') x
                  - dbarTransform trRho j (fun y' => cutFbar j y' * uD η m i l y') y‖ :=
                  norm_add_le _ _
            _ ≤ (2 + L + 128) * (uK L C₀ ^ m * S) * ‖x - y‖ ^ α
                + 2 * trRho * C₀ * (uK L C₀ ^ m * S + uK L C₀ ^ m * S) * ‖x - y‖ ^ α :=
                  add_le_add (hnt.2 x y hx hy) (hT.2 x y hx hy)
            _ = ((2 + L + 128) + 4 * trRho * C₀) * (uK L C₀ ^ m * S) * ‖x - y‖ ^ α := by ring
            _ ≤ uK L C₀ * (uK L C₀ ^ m * S) * ‖x - y‖ ^ α := by
                have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hKhol hA0) hd
            _ = uK L C₀ ^ (m + 1) * S * ‖x - y‖ ^ α := by rw [pow_succ]; ring

/-! ## The bound for one summand of the solution operator -/

/-- **The `C^{0,α}` bound for a single summand `uPsi η σ l` of `uS2`**, on the solution polydisc
`solveSet ⊆ trackSet`. -/
private lemma uPsi_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {L C₀ : ℝ} (hL0 : 0 ≤ L) (hC₀pos : 0 < C₀)
    (hLip : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖)
    {S : ℝ} (hS0 : 0 ≤ S) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hstage : ∀ m ≤ n, ∀ i l,
      (∀ z, z ∈ trackSet → ‖uD η m i l z‖ ≤ uK L C₀ ^ m * S) ∧
      (∀ x y, x ∈ trackSet → y ∈ trackSet →
        ‖uD η m i l x - uD η m i l y‖ ≤ uK L C₀ ^ m * S * ‖x - y‖ ^ α)) :
    ∀ σ : Fin n, ∀ l : Fin n,
      (∀ z, z ∈ solveSet → ‖uPsi η σ l z‖ ≤ 2 * trRho * (uK L C₀ ^ n * S)) ∧
      (∀ x y, x ∈ solveSet → y ∈ solveSet →
        ‖uPsi η σ l x - uPsi η σ l y‖
          ≤ 2 * trRho * (2 + L) * (uK L C₀ ^ n * S) * ‖x - y‖ ^ α) := by
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  have hK1 : 1 ≤ uK L C₀ := uK_one_le hL0 hC₀nn
  have hKpos : 0 < uK L C₀ := uK_pos hL0 hC₀nn
  intro σ l
  have hσle : (σ : ℕ) ≤ n := le_of_lt σ.isLt
  obtain ⟨hAσ, hHσ⟩ := hstage (σ : ℕ) hσle σ l
  set A : ℝ := uK L C₀ ^ (σ : ℕ) * S with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (pow_nonneg hKpos.le _) hS0
  have hApow : A ≤ uK L C₀ ^ n * S := by
    rw [hAdef]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hσle) hS0
  have hFcont : Continuous (uD η (σ : ℕ) σ l) := (uD_contDiff hη (σ : ℕ) hσle σ l).continuous
  have hgc : Continuous (fun y => cutF σ y * uD η (σ : ℕ) σ l y) :=
    (contDiff_cutF σ).continuous.mul hFcont
  have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y σ‖ →
      cutF σ y * uD η (σ : ℕ) σ l y = 0 :=
    fun y hy => by rw [cutF_eq_zero hy, zero_mul]
  have hfibsup : ∀ z : Fin n → ℂ, (∀ l', l' ≠ σ → ‖z l'‖ < trTrack) →
      ‖z σ‖ ≤ cutOut → ‖cutF σ z * uD η (σ : ℕ) σ l z‖ ≤ A := by
    intro z hz hzσ
    have hzt : z ∈ trackSet := by
      intro l'
      by_cases hl' : l' = σ
      · subst hl'; exact lt_of_le_of_lt hzσ cutOut_lt_trTrack
      · exact hz l' hl'
    calc ‖cutF σ z * uD η (σ : ℕ) σ l z‖
        = ‖cutF σ z‖ * ‖uD η (σ : ℕ) σ l z‖ := norm_mul _ _
      _ ≤ 1 * A := mul_le_mul (norm_cutF_le_one σ z) (hAσ z hzt) (norm_nonneg _) zero_le_one
      _ = A := one_mul A
  have hfibh : ∀ a a' : Fin n → ℂ, (∀ l', l' ≠ σ → ‖a l'‖ < trTrack) →
      (∀ l', l' ≠ σ → ‖a' l'‖ < trTrack) →
      ‖cutF σ a * uD η (σ : ℕ) σ l a - cutF σ a' * uD η (σ : ℕ) σ l a'‖
        ≤ (2 + L) * A * ‖a - a'‖ ^ α :=
    cutF_mul_fiber_holder_two_add (n := n) hα0 hα1 (j := σ) hL0 hLip hA0 hAσ hHσ
  have hdT : uPsi η σ l = dbarTransform trRho σ (fun y => cutF σ y * uD η (σ : ℕ) σ l y) :=
    dTLM_eq hgc
  constructor
  · intro z hz
    have hbd : ∀ y : Fin n → ℂ, (∀ l', l' ≠ σ → y l' = z l') → ‖y σ‖ ≤ cutOut →
        ‖cutF σ y * uD η (σ : ℕ) σ l y‖ ≤ A := by
      intro y hy hyσ
      exact hfibsup y (fun l' hl' => by rw [hy l' hl']; exact trackSet_of_solveSet hz l') hyσ
    have hb := (dbarTransform_basic (n := n) (ρ := trRho) (b := cutOut) trRho_pos
        (le_of_lt cutOut_pos) (j := σ)).1 hgc hsupp A z hbd
    rw [hdT]
    calc ‖dbarTransform trRho σ (fun y => cutF σ y * uD η (σ : ℕ) σ l y) z‖
        ≤ 2 * trRho * A := hb
      _ ≤ 2 * trRho * (uK L C₀ ^ n * S) :=
          mul_le_mul_of_nonneg_left hApow (by linarith [trRho_pos])
  · intro x y hx hy
    have hhold : ∀ a a' : Fin n → ℂ, (∀ l', l' ≠ σ → a l' = x l') →
        (∀ l', l' ≠ σ → a' l' = y l') →
        ‖cutF σ a * uD η (σ : ℕ) σ l a - cutF σ a' * uD η (σ : ℕ) σ l a'‖
          ≤ (2 + L) * A * ‖a - a'‖ ^ α := by
      intro a a' ha ha'
      exact hfibh a a'
        (fun l' hl' => by rw [ha l' hl']; exact trackSet_of_solveSet hx l')
        (fun l' hl' => by rw [ha' l' hl']; exact trackSet_of_solveSet hy l')
    have hb := (dbarTransform_basic (n := n) (ρ := trRho) (b := cutOut) trRho_pos
        (le_of_lt cutOut_pos) (j := σ)).2.1 hgc hsupp α ((2 + L) * A) x y hhold
    rw [hdT]
    calc ‖dbarTransform trRho σ (fun y => cutF σ y * uD η (σ : ℕ) σ l y) x
          - dbarTransform trRho σ (fun y => cutF σ y * uD η (σ : ℕ) σ l y) y‖
        ≤ 2 * trRho * ((2 + L) * A) * ‖x - y‖ ^ α := hb
      _ = 2 * trRho * (2 + L) * A * ‖x - y‖ ^ α := by ring
      _ ≤ 2 * trRho * (2 + L) * (uK L C₀ ^ n * S) * ‖x - y‖ ^ α := by
          have h2L : 0 ≤ 2 * trRho * (2 + L) :=
            mul_nonneg (by linarith [trRho_pos]) (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hApow h2L)
            (Real.rpow_nonneg (norm_nonneg _) α)

/-! ## The main estimate -/

theorem uS2_estimate {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiff ℝ 1 (η i l)) → ∀ j : Fin n,
        Work.CR.Flat.holderNorm 0 α (Work.NN.Final.uS2 η j) Work.CR.Flat.Cauchy.solveSet
          ≤ ENNReal.ofReal C *
              ∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l) (Work.CR.Flat.polydisc 0 (fun _ => 1)) := by
  obtain ⟨L, hL0, hLip⟩ := Work.CR.Flat.Cauchy.openCut_lipschitz
  obtain ⟨C₀, hC₀pos, hC₀prop⟩ := Work.CR.Flat.Cauchy.exists_uniform_dbarC_bound n α hα0 hα1
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  have hKpos : 0 < uK L C₀ := uK_pos hL0 hC₀nn
  refine ⟨2 * max ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
      ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ (n : ℝ) * (2 * trRho * uK L C₀ ^ n) :=
      mul_nonneg (Nat.cast_nonneg n)
        (le_of_lt (mul_pos (mul_pos (by norm_num) trRho_pos) (pow_pos hKpos n)))
    have h2 : (0 : ℝ) ≤ (n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n) :=
      mul_nonneg (Nat.cast_nonneg n)
        (le_of_lt (mul_pos (mul_pos (mul_pos (by norm_num) trRho_pos) (by linarith))
          (pow_pos hKpos n)))
    have h3 : (0 : ℝ) ≤ max ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
        ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) :=
      le_trans h1 (le_max_left _ _)
    linarith
  · intro η hη j
    by_cases htop : (∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l)
        (Work.CR.Flat.polydisc 0 (fun _ => 1))) = ⊤
    · rw [htop]
      have hCpos : 0 < 2 * max ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
          ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) + 1 := by
        have h1 : (0 : ℝ) ≤ (n : ℝ) * (2 * trRho * uK L C₀ ^ n) :=
          mul_nonneg (Nat.cast_nonneg n)
            (le_of_lt (mul_pos (mul_pos (by norm_num) trRho_pos) (pow_pos hKpos n)))
        have h3 : (0 : ℝ) ≤ max ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
            ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) :=
          le_trans h1 (le_max_left _ _)
        linarith
      have hne0 : ENNReal.ofReal (2 * max ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
          ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) + 1) ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact hCpos
      rw [ENNReal.mul_top hne0]
      exact le_top
    · have hne : (∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l)
          (Work.CR.Flat.polydisc 0 (fun _ => 1))) ≠ ⊤ := htop
      have hbaseA : ∀ i l z, z ∈ trackSet → ‖η i l z‖
          ≤ (∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l)
              (Work.CR.Flat.polydisc 0 (fun _ => 1))).toReal :=
        fun i l z hz => eta_sup_track hne i l hz
      have hbaseH : ∀ i l x y, x ∈ trackSet → y ∈ trackSet →
          ‖η i l x - η i l y‖
            ≤ (∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l)
                (Work.CR.Flat.polydisc 0 (fun _ => 1))).toReal * ‖x - y‖ ^ α :=
        fun i l x y hx hy => eta_holder_track hα0 hne i l hx hy
      have hstage := uD_stage_bound (n := n) hα0 hα1 hL0 hC₀pos hLip hC₀prop
        (S := (∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l)
            (Work.CR.Flat.polydisc 0 (fun _ => 1))).toReal)
        ENNReal.toReal_nonneg hη hbaseA hbaseH
      have hup := uPsi_bound (n := n) hα0 hα1 hL0 hC₀pos hLip
        (S := (∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l)
            (Work.CR.Flat.polydisc 0 (fun _ => 1))).toReal)
        ENNReal.toReal_nonneg hη hstage
      set Tm : ℝ≥0∞ := ∑ i, ∑ l, Work.CR.Flat.holderNorm 0 α (η i l)
          (Work.CR.Flat.polydisc 0 (fun _ => 1)) with hTmdef
      have hTm_ne : Tm ≠ ⊤ := hne
      have heq' : ENNReal.ofReal Tm.toReal = Tm := ENNReal.ofReal_toReal hTm_ne
      have hTm0 : 0 ≤ Tm.toReal := ENNReal.toReal_nonneg
      have hC10 : 0 ≤ (n : ℝ) * (2 * trRho * uK L C₀ ^ n) :=
        mul_nonneg (Nat.cast_nonneg n)
          (le_of_lt (mul_pos (mul_pos (by norm_num) trRho_pos) (pow_pos hKpos n)))
      have hC20 : 0 ≤ (n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n) :=
        mul_nonneg (Nat.cast_nonneg n)
          (le_of_lt (mul_pos (mul_pos (mul_pos (by norm_num) trRho_pos) (by linarith))
            (pow_pos hKpos n)))
      have hsup : ∀ z, z ∈ solveSet →
          ‖uS2 η j z‖ ≤ ((n : ℝ) * (2 * trRho * uK L C₀ ^ n)) * Tm.toReal := by
        intro z hz
        have hsum : uS2 η j z = ∑ σ : Fin n, uPsi η σ j z := by
          simp only [uS2, Finset.sum_apply]
        rw [hsum]
        calc ‖∑ σ : Fin n, uPsi η σ j z‖ ≤ ∑ σ : Fin n, ‖uPsi η σ j z‖ := norm_sum_le _ _
          _ ≤ ∑ _σ : Fin n, 2 * trRho * (uK L C₀ ^ n * Tm.toReal) :=
                Finset.sum_le_sum (fun σ _ => (hup σ j).1 z hz)
          _ = (n : ℝ) * (2 * trRho * (uK L C₀ ^ n * Tm.toReal)) := by
                simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ((n : ℝ) * (2 * trRho * uK L C₀ ^ n)) * Tm.toReal := by ring
      have hhol : ∀ x y, x ∈ solveSet → y ∈ solveSet →
          ‖uS2 η j x - uS2 η j y‖
            ≤ ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) * Tm.toReal
                * ‖x - y‖ ^ α := by
        intro x y hx hy
        have hx' : uS2 η j x = ∑ σ : Fin n, uPsi η σ j x := by
          simp only [uS2, Finset.sum_apply]
        have hy' : uS2 η j y = ∑ σ : Fin n, uPsi η σ j y := by
          simp only [uS2, Finset.sum_apply]
        have hsub : uS2 η j x - uS2 η j y
            = ∑ σ : Fin n, (uPsi η σ j x - uPsi η σ j y) := by
          rw [hx', hy', ← Finset.sum_sub_distrib]
        rw [hsub]
        calc ‖∑ σ : Fin n, (uPsi η σ j x - uPsi η σ j y)‖
            ≤ ∑ σ : Fin n, ‖uPsi η σ j x - uPsi η σ j y‖ := norm_sum_le _ _
          _ ≤ ∑ _σ : Fin n, 2 * trRho * (2 + L) * (uK L C₀ ^ n * Tm.toReal)
                * ‖x - y‖ ^ α :=
                Finset.sum_le_sum (fun σ _ => (hup σ j).2 x y hx hy)
          _ = (n : ℝ) * (2 * trRho * (2 + L) * (uK L C₀ ^ n * Tm.toReal)
                * ‖x - y‖ ^ α) := by
                simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) * Tm.toReal
                * ‖x - y‖ ^ α := by ring
      have hnorm : holderNorm 0 α (uS2 η j) solveSet
          = iterDerivNorm 0 (uS2 η j) solveSet + holderSeminorm 0 α (uS2 η j) solveSet := by
        simp [holderNorm]
      have hiter : iterDerivNorm 0 (uS2 η j) solveSet
          ≤ ENNReal.ofReal ((n : ℝ) * (2 * trRho * uK L C₀ ^ n)) * Tm := by
        rw [iterDerivNorm_zero]
        refine iSup₂_le fun z hz => ?_
        have h2 : ENNReal.ofReal (((n : ℝ) * (2 * trRho * uK L C₀ ^ n)) * Tm.toReal)
            = ENNReal.ofReal ((n : ℝ) * (2 * trRho * uK L C₀ ^ n)) * Tm := by
          rw [ENNReal.ofReal_mul hC10, heq']
        calc ENNReal.ofReal ‖uS2 η j z‖
            ≤ ENNReal.ofReal (((n : ℝ) * (2 * trRho * uK L C₀ ^ n)) * Tm.toReal) :=
              ENNReal.ofReal_le_ofReal (hsup z hz)
          _ = _ := h2
      have hsem : holderSeminorm 0 α (uS2 η j) solveSet
          ≤ ENNReal.ofReal ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) * Tm := by
        refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
        have hD : ‖iteratedFDerivWithin ℝ 0 (uS2 η j) solveSet x
            - iteratedFDerivWithin ℝ 0 (uS2 η j) solveSet y‖
            = ‖uS2 η j x - uS2 η j y‖ := by
          rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
        rw [hD]
        have hpos : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (by rwa [norm_pos_iff, sub_ne_zero]) α
        have hval : ‖uS2 η j x - uS2 η j y‖ / ‖x - y‖ ^ α
            ≤ ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) * Tm.toReal := by
          rw [div_le_iff₀ hpos]
          exact hhol x y hx hy
        have h2 : ENNReal.ofReal (((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n))
              * Tm.toReal)
            = ENNReal.ofReal ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) * Tm := by
          rw [ENNReal.ofReal_mul hC20, heq']
        calc ENNReal.ofReal (‖uS2 η j x - uS2 η j y‖ / ‖x - y‖ ^ α)
            ≤ ENNReal.ofReal (((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n))
                * Tm.toReal) := ENNReal.ofReal_le_ofReal hval
          _ = _ := h2
      rw [hnorm]
      calc iterDerivNorm 0 (uS2 η j) solveSet + holderSeminorm 0 α (uS2 η j) solveSet
          ≤ ENNReal.ofReal ((n : ℝ) * (2 * trRho * uK L C₀ ^ n)) * Tm
            + ENNReal.ofReal ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) * Tm :=
              add_le_add hiter hsem
        _ = ENNReal.ofReal (((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
              + ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n))) * Tm := by
              rw [ENNReal.ofReal_add hC10 hC20, add_mul]
        _ ≤ ENNReal.ofReal (2 * max ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
              ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n))) * Tm := by
              refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
              linarith [le_max_left ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
                  ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)),
                le_max_right ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
                  ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n))]
        _ ≤ ENNReal.ofReal (2 * max ((n : ℝ) * (2 * trRho * uK L C₀ ^ n))
              ((n : ℝ) * (2 * trRho * (2 + L) * uK L C₀ ^ n)) + 1) * Tm := by
              refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
              linarith

end Work.NN.Final
