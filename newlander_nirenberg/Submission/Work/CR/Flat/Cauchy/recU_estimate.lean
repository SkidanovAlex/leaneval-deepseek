import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Cauchy.cutFbar_mul_bound_uniform
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic

noncomputable section

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ## Bounds coming from the Hölder norm of the data -/

/-- If the sum of the Hölder norms is finite then so is each of them. -/
lemma holderNorm_ne_top_of_sum_ne_top {n : ℕ} {α : ℝ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hS : (∑ j, holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))) ≠ ⊤) :
    ∀ j, holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) ≠ ⊤ := by
  intro j hj
  refine hS ?_
  have hle : holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) ≤
      ∑ i, holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) :=
    Finset.single_le_sum (f := fun i => holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))) (fun i _ => zero_le) (Finset.mem_univ j)
  rw [hj] at hle
  exact top_unique hle

/-- Pointwise bound on `trackSet`: `‖f j z‖` is controlled by the sum of the Hölder norms. -/
lemma norm_le_sum_holderNorm {n : ℕ} {α : ℝ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hS : (∑ j, holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))) ≠ ⊤) :
    ∀ j (z : Fin n → ℂ), z ∈ trackSet → ‖f j z‖ ≤
      ∑ i, (holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal := by
  intro j z hz
  have hHj := holderNorm_ne_top_of_sum_ne_top hS j
  have hz' : z ∈ polydisc (0 : Fin n → ℂ) (fun _ => 1) := trackSet_subset_unit hz
  have h1 : ENNReal.ofReal ‖f j z‖ ≤
      holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) :=
    norm_apply_le_holderNorm 0 α (f j) _ hz'
  have h2 : ‖f j z‖ ≤
      (holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hHj).mp h1
  have h3 : (holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal ≤
      ∑ i, (holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal := by
    rw [← ENNReal.toReal_sum (fun i _ => holderNorm_ne_top_of_sum_ne_top hS i)]
    exact ENNReal.toReal_mono hS
      (Finset.single_le_sum (f := fun i => holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))) (fun i _ => zero_le) (Finset.mem_univ j))
  exact le_trans h2 h3

/-- Hölder bound on `trackSet`, with constant the sum of the Hölder norms. -/
lemma norm_sub_le_sum_holderNorm {n : ℕ} {α : ℝ} (hα : 0 < α)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hS : (∑ j, holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))) ≠ ⊤) :
    ∀ j (x y : Fin n → ℂ), x ∈ trackSet → y ∈ trackSet →
      ‖f j x - f j y‖ ≤
        (∑ i, (holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal)
          * ‖x - y‖ ^ α := by
  intro j x y hx hy
  have hS0 : (0 : ℝ) ≤
      ∑ i, (holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal :=
    Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, norm_zero]
    exact mul_nonneg hS0 (Real.rpow_nonneg (norm_nonneg _) α)
  · have hHj := holderNorm_ne_top_of_sum_ne_top hS j
    have hx' : x ∈ polydisc (0 : Fin n → ℂ) (fun _ => 1) := trackSet_subset_unit hx
    have hy' : y ∈ polydisc (0 : Fin n → ℂ) (fun _ => 1) := trackSet_subset_unit hy
    have hD : ‖iteratedFDerivWithin ℝ 0 (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) x
        - iteratedFDerivWithin ℝ 0 (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) y‖
        = ‖f j x - f j y‖ := by
      rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
    have h1 : ENNReal.ofReal (‖f j x - f j y‖ / ‖x - y‖ ^ α) ≤
        holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
      rw [← hD]
      exact le_trans (le_holderSeminorm 0 α (f j) _ hx' hy' hxy)
        (holderSeminorm_le_holderNorm 0 α (f j) _ (le_refl 0))
    have h2 : ‖f j x - f j y‖ / ‖x - y‖ ^ α ≤
        (holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hHj).mp h1
    have h3 : (holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal ≤
        ∑ i, (holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal := by
      rw [← ENNReal.toReal_sum (fun i _ => holderNorm_ne_top_of_sum_ne_top hS i)]
      exact ENNReal.toReal_mono hS
        (Finset.single_le_sum (f := fun i => holderNorm 0 α (f i) (polydisc (0 : Fin n → ℂ) (fun _ => 1))) (fun i _ => zero_le) (Finset.mem_univ j))
    have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (by rw [norm_pos_iff, sub_ne_zero]; exact hxy) α
    have hmul : (‖f j x - f j y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α = ‖f j x - f j y‖ :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (le_trans h2 h3) (le_of_lt hpos)

/-! ## The fibre Hölder bound for the coordinate cutoff `cutF j` -/

lemma cutF_mul_fiber_holder {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {j : Fin n} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖)
    {F : (Fin n → ℂ) → ℂ} {A : ℝ} (hA0 : 0 ≤ A)
    (hF : ∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A)
    (hFh : ∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
      ‖F x - F y‖ ≤ A * ‖x - y‖ ^ α) :
    ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
      (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
      ‖cutF j a * F a - cutF j a' * F a'‖ ≤ 64 * (1 + L) * A * ‖a - a'‖ ^ α := by
  intro a a' ha ha'
  have hmem : ∀ u : Fin n → ℂ, (∀ l, l ≠ j → ‖u l‖ < trTrack) → ‖u j‖ < cutOut →
      u ∈ trackSet := fun u hu huj l => by
    by_cases hl : l = j
    · subst hl; exact lt_trans huj cutOut_lt_trTrack
    · exact hu l hl
  have hbound : ∀ u : Fin n → ℂ, (∀ l, l ≠ j → ‖u l‖ < trTrack) → ‖cutF j u * F u‖ ≤ A := by
    intro u hu
    by_cases h : ‖u j‖ < cutOut
    · calc ‖cutF j u * F u‖ = ‖cutF j u‖ * ‖F u‖ := norm_mul _ _
        _ ≤ 1 * A := mul_le_mul (norm_cutF_le_one j u) (hF u (hmem u hu h))
            (norm_nonneg _) zero_le_one
        _ = A := one_mul A
    · rw [cutF_eq_zero (not_lt.mp h), zero_mul, norm_zero]; exact hA0
  have ht0 : 0 ≤ ‖a - a'‖ := norm_nonneg _
  have hβ0 : 0 ≤ ‖a - a'‖ ^ α := Real.rpow_nonneg ht0 α
  have hC0 : 0 ≤ 64 * (1 + L) * A := by
    have h1 : (0 : ℝ) ≤ 1 + L := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num) h1) hA0
  have hfinal : ∀ {B : ℝ}, B ≤ (1 + L) * A * ‖a - a'‖ ^ α →
      B ≤ 64 * (1 + L) * A * ‖a - a'‖ ^ α := by
    intro B hB
    have hx : 0 ≤ (1 + L) * A * ‖a - a'‖ ^ α :=
      mul_nonneg (mul_nonneg (by linarith) hA0) hβ0
    have hle : (1 + L) * A * ‖a - a'‖ ^ α ≤ 64 * (1 + L) * A * ‖a - a'‖ ^ α := by
      nlinarith [hx]
    linarith
  rcases le_or_gt (1 / 32 : ℝ) ‖a - a'‖ with hbig | hsmall
  · have hβ : (1 / 32 : ℝ) ≤ ‖a - a'‖ ^ α := by
      have h2 : ((1 / 32 : ℝ)) ^ α ≤ ‖a - a'‖ ^ α :=
        Real.rpow_le_rpow (by norm_num) hbig hα.le
      have h3 : (1 / 32 : ℝ) ≤ ((1 / 32 : ℝ)) ^ α := by
        have h4 : ((1 / 32 : ℝ)) ^ (1 : ℝ) ≤ ((1 / 32 : ℝ)) ^ α :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (le_of_lt hα1)
        rwa [Real.rpow_one] at h4
      linarith
    have h2A : ‖cutF j a * F a - cutF j a' * F a'‖ ≤ 2 * A := by
      calc ‖cutF j a * F a - cutF j a' * F a'‖
          ≤ ‖cutF j a * F a‖ + ‖cutF j a' * F a'‖ := norm_sub_le _ _
        _ ≤ A + A := add_le_add (hbound a ha) (hbound a' ha')
        _ = 2 * A := by ring
    calc ‖cutF j a * F a - cutF j a' * F a'‖ ≤ 2 * A := h2A
      _ ≤ 64 * (1 + L) * A * ‖a - a'‖ ^ α := by
          have hAL : 0 ≤ A * L := mul_nonneg hA0 hL0
          have h1 : 2 * A ≤ 64 * (1 + L) * A * (1 / 32) := by nlinarith [hAL]
          have h2 : 64 * (1 + L) * A * (1 / 32) ≤ 64 * (1 + L) * A * ‖a - a'‖ ^ α :=
            mul_le_mul_of_nonneg_left hβ hC0
          linarith
  · have hβ1 : ‖a - a'‖ ≤ ‖a - a'‖ ^ α := by
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h, Real.zero_rpow (ne_of_gt hα)]
      · have h4 := Real.rpow_le_rpow_of_exponent_ge h (by linarith) (le_of_lt hα1)
        rwa [Real.rpow_one] at h4
    by_cases haj : ‖a j‖ < cutOut
    · by_cases ha'j : ‖a' j‖ < cutOut
      · -- both `j`-coordinates inside `cutOut`
        have hat : a ∈ trackSet := hmem a ha haj
        have ha't : a' ∈ trackSet := hmem a' ha' ha'j
        have hsplit : cutF j a * F a - cutF j a' * F a'
            = cutF j a * (F a - F a') + (cutF j a - cutF j a') * F a' := by ring
        rw [hsplit]
        refine hfinal ?_
        calc ‖cutF j a * (F a - F a') + (cutF j a - cutF j a') * F a'‖
            ≤ ‖cutF j a * (F a - F a')‖ + ‖(cutF j a - cutF j a') * F a'‖ := norm_add_le _ _
          _ = ‖cutF j a‖ * ‖F a - F a'‖ + ‖cutF j a - cutF j a'‖ * ‖F a'‖ := by
              rw [norm_mul, norm_mul]
          _ ≤ 1 * (A * ‖a - a'‖ ^ α) + (L * ‖a - a'‖) * A := by
              gcongr
              · exact norm_cutF_le_one j a
              · exact hFh a a' hat ha't
              · exact norm_cutF_sub_le j hL0 hL a a'
              · exact hF a' ha't
          _ ≤ (1 + L) * A * ‖a - a'‖ ^ α := by
              have hrw : 1 * (A * ‖a - a'‖ ^ α) + (L * ‖a - a'‖) * A
                  = A * ‖a - a'‖ ^ α + (L * A) * ‖a - a'‖ := by ring
              rw [hrw]
              have h2 : (L * A) * ‖a - a'‖ ≤ (L * A) * ‖a - a'‖ ^ α :=
                mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hL0 hA0)
              have h3 : 0 ≤ (1 + L) * A * ‖a - a'‖ ^ α :=
                mul_nonneg (mul_nonneg (by linarith) hA0) hβ0
              nlinarith [h2, h3]
      · -- `a` inside, `a'` outside `cutOut`
        have ha'ge : cutOut ≤ ‖a' j‖ := not_lt.mp ha'j
        have hz : cutF j a' = 0 := cutF_eq_zero ha'ge
        have hat : a ∈ trackSet := hmem a ha haj
        refine hfinal ?_
        calc ‖cutF j a * F a - cutF j a' * F a'‖ = ‖cutF j a * F a‖ := by
              rw [hz, zero_mul, sub_zero]
          _ = ‖cutF j a‖ * ‖F a‖ := norm_mul _ _
          _ ≤ (L * ‖a - a'‖) * A := by
              have hca : ‖cutF j a‖ ≤ L * ‖a - a'‖ := by
                have h := norm_cutF_sub_le j hL0 hL a a'
                rw [hz, sub_zero] at h
                exact h
              exact mul_le_mul hca (hF a hat) (norm_nonneg _) (mul_nonneg hL0 ht0)
          _ ≤ (1 + L) * A * ‖a - a'‖ ^ α := by
              have hrw : (L * ‖a - a'‖) * A = (L * A) * ‖a - a'‖ := by ring
              rw [hrw]
              have h2 : (L * A) * ‖a - a'‖ ≤ (L * A) * ‖a - a'‖ ^ α :=
                mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hL0 hA0)
              have h3 : 0 ≤ (1 + L) * A * ‖a - a'‖ ^ α :=
                mul_nonneg (mul_nonneg (by linarith) hA0) hβ0
              nlinarith [h2, h3]
    · by_cases ha'j : ‖a' j‖ < cutOut
      · -- `a` outside, `a'` inside `cutOut`
        have hage : cutOut ≤ ‖a j‖ := not_lt.mp haj
        have hz : cutF j a = 0 := cutF_eq_zero hage
        have ha't : a' ∈ trackSet := hmem a' ha' ha'j
        refine hfinal ?_
        calc ‖cutF j a * F a - cutF j a' * F a'‖ = ‖cutF j a' * F a'‖ := by
              rw [hz, zero_mul, zero_sub, norm_neg]
          _ = ‖cutF j a'‖ * ‖F a'‖ := norm_mul _ _
          _ ≤ (L * ‖a - a'‖) * A := by
              have hca : ‖cutF j a'‖ ≤ L * ‖a - a'‖ := by
                have h := norm_cutF_sub_le j hL0 hL a a'
                rw [hz, zero_sub, norm_neg] at h
                exact h
              exact mul_le_mul hca (hF a' ha't) (norm_nonneg _) (mul_nonneg hL0 ht0)
          _ ≤ (1 + L) * A * ‖a - a'‖ ^ α := by
              have hrw : (L * ‖a - a'‖) * A = (L * A) * ‖a - a'‖ := by ring
              rw [hrw]
              have h2 : (L * A) * ‖a - a'‖ ≤ (L * A) * ‖a - a'‖ ^ α :=
                mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hL0 hA0)
              have h3 : 0 ≤ (1 + L) * A * ‖a - a'‖ ^ α :=
                mul_nonneg (mul_nonneg (by linarith) hA0) hβ0
              nlinarith [h2, h3]
      · -- both outside `cutOut`
        have hage : cutOut ≤ ‖a j‖ := not_lt.mp haj
        have ha'ge : cutOut ≤ ‖a' j‖ := not_lt.mp ha'j
        rw [cutF_eq_zero hage, cutF_eq_zero ha'ge, zero_mul, zero_mul, sub_zero, norm_zero]
        exact mul_nonneg hC0 hβ0


/-! ## The main estimate

The proof below produces a constant depending only on `n`, `α` and the geometry (the radii
`trRho`/`cutOut` and the two absolute constants `L`, `C₀`), never on the data `f`.  It is
therefore stated first in the form that the rest of the development consumes (the constant
outside the `∀ f`), and the form with `f` fixed by the caller is an immediate corollary. -/

theorem recU_estimate_uniform_aux {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) → IsClosedForm f →
        (∑ j, holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))) ≠ ⊤ →
        (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < eqRad) → ‖recU f z‖ ≤
          C * ∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) ∧
        (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < eqRad) → (∀ l, ‖y l‖ < eqRad) →
          ‖recU f x - recU f y‖ ≤
            C * (∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) * ‖x - y‖ ^ α) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    refine ⟨1, one_pos, ?_⟩
    intro f hf1 hcl hS
    refine ⟨?_, ?_⟩
    · intro z hz
      simp [recU]
    · intro x y hx hy
      simp [recU]
  · -- a size constant for `∂̄χ_j · F` working for every coordinate `j`
    obtain ⟨cχ, -, hcχ⟩ := openCut_props_infty.2.2.2.2.2.2.1
    obtain ⟨cχ', -, hcχ'⟩ := openCut_props_infty.2.2.2.2.2.2.2
    have hcχz : ∀ ζ : ℂ, cutOut ≤ ‖ζ‖ → dbarC openCut ζ = 0 :=
      fun ζ hζ => openCut_props_infty.2.2.2.2.2.1 ζ hζ
    have hex : ∀ j : Fin n, ∃ Ch : ℝ, 0 < Ch ∧
        (∀ {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
          (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
          (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
            ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
          (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
            ‖dbarC openCut (z j) * F z‖ ≤ Ch * A) ∧
          (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
            (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
            ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
              ≤ Ch * (A + H) * ‖a - a'‖ ^ α)) :=
      fun j => cutFbar_mul_bound_uniform (j := j) hα hα1 hcχ hcχz hcχ'
    choose Cfun hCf using hex
    set C0 : ℝ := 1 + ∑ j : Fin n, Cfun j with hC0def
    have hC0le : ∀ j : Fin n, Cfun j ≤ C0 := by
      intro j
      rw [hC0def]
      have h1 : Cfun j ≤ ∑ i : Fin n, Cfun i :=
        Finset.single_le_sum (fun i _ => le_of_lt (hCf i).1) (Finset.mem_univ j)
      linarith
    have hC0pos : 0 < C0 := by
      rw [hC0def]
      have h1 : 0 < Cfun ⟨0, hn⟩ := (hCf ⟨0, hn⟩).1
      have h2 : Cfun ⟨0, hn⟩ ≤ ∑ i : Fin n, Cfun i :=
        Finset.single_le_sum (fun i _ => le_of_lt (hCf i).1) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
      linarith
    have hC0 : ∀ (j : Fin n) {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
        (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
        (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet → ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
        (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
          ‖dbarC openCut (z j) * F z‖ ≤ C0 * A) ∧
        (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
          (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
          ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
            ≤ C0 * (A + H) * ‖a - a'‖ ^ α) := by
      intro j F A H hA hH hFb hHb
      obtain ⟨b1, b2⟩ := (hCf j).2 (F := F) (A := A) (H := H) hA hH hFb hHb
      refine ⟨?_, ?_⟩
      · intro z hz hzj
        calc ‖dbarC openCut (z j) * F z‖ ≤ Cfun j * A := b1 z hz hzj
          _ ≤ C0 * A := mul_le_mul_of_nonneg_right (hC0le j) hA
      · intro a a' ha ha'
        calc ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
              ≤ Cfun j * (A + H) * ‖a - a'‖ ^ α := b2 a a' ha ha'
          _ ≤ C0 * (A + H) * ‖a - a'‖ ^ α := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
              exact mul_le_mul_of_nonneg_right (hC0le j) (by linarith)
    obtain ⟨L, hL0, hL⟩ := openCut_lipschitz
    set K : ℝ := max 1 (4 * trRho * C0) + 1 with hKdef
    have hK1 : 1 ≤ K := by
      rw [hKdef]; linarith [le_max_left (1 : ℝ) (4 * trRho * C0)]
    have hK4 : 4 * trRho * C0 ≤ K := by
      rw [hKdef]; linarith [le_max_right (1 : ℝ) (4 * trRho * C0)]
    have hKnn : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
    refine ⟨2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1, ?_, ?_⟩
    · -- the constant is positive (it does not involve the data `f`)
      have h1 : (0 : ℝ) ≤ 2 * trRho := by linarith [trRho_pos]
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h3 : (0 : ℝ) ≤ K ^ n := pow_nonneg hKnn n
      have h4 : (0 : ℝ) ≤ 1 + 64 * (1 + L) := by linarith
      have := mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
      linarith
    · intro f hf1 hcl hS
      set S : ℝ :=
        ∑ j, (holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1))).toReal with hSdef
      have hS0 : (0 : ℝ) ≤ S := by
        rw [hSdef]; exact Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
      have hbase1 : ∀ j (z : Fin n → ℂ), z ∈ trackSet → ‖f j z‖ ≤ S := by
        intro j z hz
        have h := norm_le_sum_holderNorm hS j z hz
        rwa [← hSdef] at h
      have hbase2 : ∀ j (x y : Fin n → ℂ), x ∈ trackSet → y ∈ trackSet →
          ‖f j x - f j y‖ ≤ S * ‖x - y‖ ^ α := by
        intro j x y hx hy
        have h := norm_sub_le_sum_holderNorm hα hS j x y hx hy
        rwa [← hSdef] at h
      -- the induction over the stages of the recursion
      have key : ∀ m : ℕ, ∀ k : Fin n,
          (∀ z : Fin n → ℂ, z ∈ trackSet → ‖recF f m k z‖ ≤ K ^ m * S) ∧
          (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
            ‖recF f m k x - recF f m k y‖ ≤ K ^ m * S * ‖x - y‖ ^ α) := by
        intro m
        induction m with
        | zero =>
            intro k
            rw [recF_zero]
            exact ⟨fun z hz => by simpa using hbase1 k z hz,
                   fun x y hx hy => by simpa using hbase2 k x y hx hy⟩
        | succ m ih =>
            intro k
            by_cases hlt : m < n
            · set j : Fin n := ⟨m, hlt⟩ with hjdef
              have hrec : recF f (m + 1) k =
                  dbarTransform trRho j (fun y => cutFbar j y * recF f m k y) := by
                rw [recF_succ_of_lt f hlt]
                rw [show (⟨m, hlt⟩ : Fin n) = j from hjdef.symm]
                rfl
              have hmn : m ≤ n := le_of_lt hlt
              have hsm : ∀ i : Fin n, ContDiff ℝ 1 (recF f m i) :=
                (recF_inv (k := 0) hf1 hcl m hmn).1
              have hcont : Continuous (fun y => cutFbar j y * recF f m k y) :=
                ((contDiff_cutFbar_of_le j 1).continuous).mul ((hsm k).continuous)
              have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y j‖ →
                  cutFbar j y * recF f m k y = 0 :=
                fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul]
              have hA0 : 0 ≤ K ^ m * S := mul_nonneg (pow_nonneg hKnn m) hS0
              have hb1 : ∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) →
                  ‖z j‖ ≤ cutOut →
                  ‖dbarC openCut (z j) * recF f m k z‖ ≤ C0 * (K ^ m * S) :=
                (hC0 j (F := recF f m k) (A := K ^ m * S) (H := K ^ m * S) hA0 hA0
                  (fun z hz => (ih k).1 z hz)
                  (fun x y hx hy => (ih k).2 x y hx hy)).1
              have hb2 : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
                  (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
                  ‖dbarC openCut (a j) * recF f m k a - dbarC openCut (a' j) * recF f m k a'‖
                    ≤ C0 * (K ^ m * S + K ^ m * S) * ‖a - a'‖ ^ α :=
                (hC0 j (F := recF f m k) (A := K ^ m * S) (H := K ^ m * S) hA0 hA0
                  (fun z hz => (ih k).1 z hz)
                  (fun x y hx hy => (ih k).2 x y hx hy)).2
              have hcoef2 : 2 * trRho * C0 ≤ 4 * trRho * C0 := by
                nlinarith [mul_nonneg (le_of_lt trRho_pos) (le_of_lt hC0pos)]
              constructor
              · intro z hz
                rw [hrec]
                have hfib : ∀ y : Fin n → ℂ, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ cutOut →
                    ‖cutFbar j y * recF f m k y‖ ≤ C0 * (K ^ m * S) := by
                  intro y hyl hyj
                  exact hb1 y (fun l hl => (trackSet_update hz hyl
                    (lt_of_le_of_lt hyj cutOut_lt_trTrack)) l) hyj
                calc ‖dbarTransform trRho j (fun y => cutFbar j y * recF f m k y) z‖
                    ≤ 2 * trRho * (C0 * (K ^ m * S)) :=
                      (dbarTransform_basic trRho_pos (le_of_lt cutOut_pos)).1
                        hcont hsupp (C0 * (K ^ m * S)) z hfib
                  _ ≤ K ^ (m + 1) * S := by
                      have hstep : 2 * trRho * (C0 * (K ^ m * S)) ≤ K * (K ^ m * S) := by
                        calc 2 * trRho * (C0 * (K ^ m * S))
                            = (2 * trRho * C0) * (K ^ m * S) := by ring
                          _ ≤ K * (K ^ m * S) :=
                              mul_le_mul_of_nonneg_right (le_trans hcoef2 hK4) hA0
                      calc 2 * trRho * (C0 * (K ^ m * S)) ≤ K * (K ^ m * S) := hstep
                        _ = K ^ (m + 1) * S := by rw [pow_succ]; ring
              · intro x y hx hy
                rw [hrec]
                have hfib2 : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → a l = x l) →
                    (∀ l, l ≠ j → a' l = y l) →
                    ‖cutFbar j a * recF f m k a - cutFbar j a' * recF f m k a'‖
                      ≤ (C0 * (K ^ m * S + K ^ m * S)) * ‖a - a'‖ ^ α := by
                  intro a a' hal ha'l
                  exact hb2 a a' (fun l hl => by rw [hal l hl]; exact hx l)
                    (fun l hl => by rw [ha'l l hl]; exact hy l)
                calc ‖dbarTransform trRho j (fun y => cutFbar j y * recF f m k y) x
                      - dbarTransform trRho j (fun y => cutFbar j y * recF f m k y) y‖
                    ≤ 2 * trRho * (C0 * (K ^ m * S + K ^ m * S)) * ‖x - y‖ ^ α :=
                      (dbarTransform_basic trRho_pos (le_of_lt cutOut_pos)).2.1
                        hcont hsupp α _ x y hfib2
                  _ ≤ K ^ (m + 1) * S * ‖x - y‖ ^ α := by
                      have hcoef : 2 * trRho * (C0 * (K ^ m * S + K ^ m * S))
                          ≤ K * (K ^ m * S) := by
                        have h4 := mul_le_mul_of_nonneg_right hK4 hA0
                        nlinarith [h4]
                      calc 2 * trRho * (C0 * (K ^ m * S + K ^ m * S)) * ‖x - y‖ ^ α
                          ≤ (K * (K ^ m * S)) * ‖x - y‖ ^ α :=
                            mul_le_mul_of_nonneg_right hcoef
                              (Real.rpow_nonneg (norm_nonneg _) α)
                        _ = K ^ (m + 1) * S * ‖x - y‖ ^ α := by rw [pow_succ]; ring
            · have hrec : recF f (m + 1) = recF f m := by rw [recF_succ]; simp [hlt]
              have hmono : K ^ m * S ≤ K ^ (m + 1) * S :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 (Nat.le_succ m)) hS0
              constructor
              · intro z hz
                rw [hrec]
                exact le_trans ((ih k).1 z hz) hmono
              · intro x y hx hy
                rw [hrec]
                exact le_trans ((ih k).2 x y hx hy)
                  (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (norm_nonneg _) α))
      refine ⟨?_, ?_⟩
      · -- uniform bound
        intro z hz
        have hzt : z ∈ trackSet := trackSet_of_solveSet hz
        have hterm : ∀ j : Fin n,
            ‖dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z‖
              ≤ 2 * trRho * (K ^ n * S) := by
          intro j
          have hm : (j : ℕ) ≤ n := j.isLt.le
          have hcont : Continuous (fun y => cutF j y * recF f (j : ℕ) j y) :=
            ((contDiff_cutF_of_le j 1).continuous).mul
              (((recF_inv (k := 0) hf1 hcl (j : ℕ) hm).1 j).continuous)
          have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y j‖ →
              cutF j y * recF f (j : ℕ) j y = 0 :=
            fun y hy => by rw [cutF_eq_zero hy, zero_mul]
          have hfib : ∀ y : Fin n → ℂ, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ cutOut →
              ‖cutF j y * recF f (j : ℕ) j y‖ ≤ K ^ (j : ℕ) * S := by
            intro y hyl hyj
            have hyt : y ∈ trackSet :=
              trackSet_update hzt hyl (lt_of_le_of_lt hyj cutOut_lt_trTrack)
            have h1 : ‖cutF j y‖ ≤ 1 := norm_cutF_le_one j y
            have h2 : ‖recF f (j : ℕ) j y‖ ≤ K ^ (j : ℕ) * S := (key (j : ℕ) j).1 y hyt
            calc ‖cutF j y * recF f (j : ℕ) j y‖
                = ‖cutF j y‖ * ‖recF f (j : ℕ) j y‖ := norm_mul _ _
              _ ≤ 1 * (K ^ (j : ℕ) * S) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
              _ = K ^ (j : ℕ) * S := one_mul _
          have hb := (dbarTransform_basic trRho_pos (le_of_lt cutOut_pos)).1
            hcont hsupp (K ^ (j : ℕ) * S) z hfib
          refine le_trans hb ?_
          have hmul : K ^ (j : ℕ) * S ≤ K ^ n * S :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hm) hS0
          exact mul_le_mul_of_nonneg_left hmul (by linarith [trRho_pos])
        have hmain : ‖recU f z‖ ≤
            (2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1) * S := by
          rw [show recU f z = ∑ j : Fin n,
            dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z from rfl]
          calc ‖∑ j : Fin n, dbarTransform trRho j
                  (fun y => cutF j y * recF f (j : ℕ) j y) z‖
              ≤ ∑ j : Fin n, ‖dbarTransform trRho j
                  (fun y => cutF j y * recF f (j : ℕ) j y) z‖ := norm_sum_le _ _
            _ ≤ ∑ _j : Fin n, 2 * trRho * (K ^ n * S) :=
                Finset.sum_le_sum (fun j _ => hterm j)
            _ = (n : ℝ) * (2 * trRho * (K ^ n * S)) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ (2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1) * S := by
                have hx0 : 0 ≤ 2 * trRho * (n : ℝ) * K ^ n :=
                  mul_nonneg (mul_nonneg (by linarith [trRho_pos]) (Nat.cast_nonneg n))
                    (pow_nonneg hKnn n)
                have hprod : 0 ≤ 2 * trRho * (n : ℝ) * K ^ n * (64 * (1 + L)) :=
                  mul_nonneg hx0 (by linarith)
                have hx : 2 * trRho * (n : ℝ) * K ^ n ≤
                    2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1 := by
                  nlinarith [hprod]
                calc (n : ℝ) * (2 * trRho * (K ^ n * S))
                    = (2 * trRho * (n : ℝ) * K ^ n) * S := by ring
                  _ ≤ (2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1) * S :=
                      mul_le_mul_of_nonneg_right hx hS0
        rwa [hSdef] at hmain
      · -- Hölder bound
        intro x y hx hy
        have hxt : x ∈ trackSet := trackSet_of_solveSet hx
        have hyt : y ∈ trackSet := trackSet_of_solveSet hy
        have hterm : ∀ j : Fin n,
            ‖dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') x
              - dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y‖
              ≤ 2 * trRho * (64 * (1 + L) * (K ^ n * S)) * ‖x - y‖ ^ α := by
          intro j
          have hm : (j : ℕ) ≤ n := j.isLt.le
          have hcont : Continuous (fun y' => cutF j y' * recF f (j : ℕ) j y') :=
            ((contDiff_cutF_of_le j 1).continuous).mul
              (((recF_inv (k := 0) hf1 hcl (j : ℕ) hm).1 j).continuous)
          have hsupp : ∀ y' : Fin n → ℂ, cutOut ≤ ‖y' j‖ →
              cutF j y' * recF f (j : ℕ) j y' = 0 :=
            fun y' hy' => by rw [cutF_eq_zero hy', zero_mul]
          have hAj0 : 0 ≤ K ^ (j : ℕ) * S := mul_nonneg (pow_nonneg hKnn (j : ℕ)) hS0
          have hfib : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → a l = x l) →
              (∀ l, l ≠ j → a' l = y l) →
              ‖cutF j a * recF f (j : ℕ) j a - cutF j a' * recF f (j : ℕ) j a'‖
                ≤ (64 * (1 + L) * (K ^ (j : ℕ) * S)) * ‖a - a'‖ ^ α := by
            intro a a' hal ha'l
            exact cutF_mul_fiber_holder (F := recF f (j : ℕ) j) hα hα1 hL0 hL hAj0
              (fun z hz => (key (j : ℕ) j).1 z hz)
              (fun z z' hz hz' => (key (j : ℕ) j).2 z z' hz hz') a a'
              (fun l hl => by rw [hal l hl]; exact hxt l)
              (fun l hl => by rw [ha'l l hl]; exact hyt l)
          have hb := (dbarTransform_basic trRho_pos (le_of_lt cutOut_pos)).2.1
            hcont hsupp α _ x y hfib
          refine le_trans hb ?_
          have hmul : K ^ (j : ℕ) * S ≤ K ^ n * S :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hm) hS0
          have hfac : 0 ≤ 64 * (1 + L) := by linarith
          have hmono : 2 * trRho * (64 * (1 + L) * (K ^ (j : ℕ) * S))
              ≤ 2 * trRho * (64 * (1 + L) * (K ^ n * S)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmul hfac)
              (by linarith [trRho_pos])
          exact mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (norm_nonneg _) α)
        have hmain : ‖recU f x - recU f y‖ ≤
            (2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1) * S * ‖x - y‖ ^ α := by
          rw [show recU f x = ∑ j : Fin n,
                dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') x from rfl,
              show recU f y = ∑ j : Fin n,
                dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y from rfl,
              ← Finset.sum_sub_distrib]
          calc ‖∑ j : Fin n, (dbarTransform trRho j
                  (fun y' => cutF j y' * recF f (j : ℕ) j y') x
                - dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y)‖
              ≤ ∑ j : Fin n, ‖dbarTransform trRho j
                    (fun y' => cutF j y' * recF f (j : ℕ) j y') x
                  - dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _j : Fin n, 2 * trRho * (64 * (1 + L) * (K ^ n * S)) * ‖x - y‖ ^ α :=
                Finset.sum_le_sum (fun j _ => hterm j)
            _ = (n : ℝ) * (2 * trRho * (64 * (1 + L) * (K ^ n * S)) * ‖x - y‖ ^ α) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ (2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1) * S
                  * ‖x - y‖ ^ α := by
                have hx0 : 0 ≤ 2 * trRho * (n : ℝ) * K ^ n :=
                  mul_nonneg (mul_nonneg (by linarith [trRho_pos]) (Nat.cast_nonneg n))
                    (pow_nonneg hKnn n)
                have hx : (n : ℝ) * 2 * trRho * 64 * (1 + L) * K ^ n ≤
                    2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1 := by
                  have hprod : 0 ≤ 2 * trRho * (n : ℝ) * K ^ n * (64 * (1 + L)) :=
                    mul_nonneg hx0 (by linarith)
                  nlinarith [hprod]
                calc (n : ℝ) * (2 * trRho * (64 * (1 + L) * (K ^ n * S)) * ‖x - y‖ ^ α)
                    = ((n : ℝ) * 2 * trRho * 64 * (1 + L) * K ^ n) * S * ‖x - y‖ ^ α := by ring
                  _ ≤ (2 * trRho * (n : ℝ) * K ^ n * (1 + 64 * (1 + L)) + 1) * S
                        * ‖x - y‖ ^ α := by
                      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
                      exact mul_le_mul_of_nonneg_right hx hS0
        rwa [hSdef] at hmain

/-- The estimate for the explicit solution `recU f` on the polydisc of radius `eqRad`, with a
constant allowed to depend on the data `f`. -/
theorem recU_estimate {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf1 : ∀ j, ContDiff ℝ 1 (f j)) (hcl : IsClosedForm f)
    (hS : (∑ j, holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))) ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < eqRad) → ‖recU f z‖ ≤
        C * ∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) ∧
      (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < eqRad) → (∀ l, ‖y l‖ < eqRad) →
        ‖recU f x - recU f y‖ ≤
          C * (∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) * ‖x - y‖ ^ α) := by
  obtain ⟨C, hCpos, hC⟩ := recU_estimate_uniform_aux (n := n) (α := α) hα hα1
  exact ⟨C, hCpos, hC f hf1 hcl hS⟩

end Work.CR.Flat.Cauchy
