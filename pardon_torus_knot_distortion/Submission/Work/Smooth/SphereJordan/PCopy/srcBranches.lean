import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.annulusCuts

/-!
# The branch values of the source boundary curves `pcsrcUpB`, `pcsrcDnB`

`pcsrcUpB` and `pcsrcDnB` are the `2π`-periodic parametrisations of the two halves of the
boundary of the model half-pcannulus (`1/2 ≤ ‖z‖ ≤ 1`, `0 ≤ Im (z/u)` respectively
`Im (z/u) ≤ 0`).  They are defined by reducing the parameter modulo `2π` (via `pcperPt`) and
then dispatching on which quarter of the period the reduced parameter lies in.

This file records the values that these two functions take on the four consecutive
quarter-periods, for parameters in the *closed* quarter intervals
`[0, π/2]`, `[π/2, π]`, `[π, 3π/2]` and `[3π/2, 2π]`.

Because the quarter conditions in the definitions are stated with `≤`, the endpoints are
shared between consecutive branches; at each shared endpoint the two branch formulas agree,
and the lemmas below record that agreement explicitly.  The parameter `3π/2 + π/2 = 2π` is
additionally wrapped to `0` by `pcperPt`, so the fourth quarter of the period is handled by the
first branch there.
-/

namespace Work.SphereJordan

open Work.Smooth.SphereJordan

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Elementary facts about the period reduction `pcperPt` -/

private lemma pcperPtIco {τ : ℝ} (h : τ ∈ Set.Ico (0:ℝ) (2 * Real.pi)) :
    Work.Smooth.SphereJordan.pcperPt τ = τ := by
  rw [Work.Smooth.SphereJordan.pcperPt]
  have : ⌊τ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg h.1 (by positivity), (div_lt_one (by positivity)).mpr h.2⟩
  rw [this]; ring

private lemma pcperPt_two_pi : Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) = 0 := by
  rw [Work.Smooth.SphereJordan.pcperPt, div_self (by positivity : (0:ℝ) < 2 * Real.pi).ne',
    Int.floor_one]
  ring

/-! ## Branch values of `pcsrcUpB` -/

private lemma pcsrcUpB_b1 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : τ ≤ Real.pi / 2) :
    pcsrcUpB S τ = pcsrcOuterUp S (τ / (Real.pi / 2)) := by
  simp only [pcsrcUpB, hσ]; rw [if_pos h1]

private lemma pcsrcUpB_b2 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : τ ≤ Real.pi) :
    pcsrcUpB S τ = ((-1 + (τ - Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * pccutDir S := by
  simp only [pcsrcUpB, hσ]; rw [if_neg h1, if_pos h2, Complex.real_smul]

private lemma pcsrcUpB_b3 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : τ ≤ 3 * Real.pi / 2) :
    pcsrcUpB S τ = pcsrcInnerUp S ((τ - Real.pi) / (Real.pi / 2)) := by
  simp only [pcsrcUpB, hσ]; rw [if_neg h1, if_neg h2, if_pos h3]

private lemma pcsrcUpB_b4 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : ¬ τ ≤ 3 * Real.pi / 2) :
    pcsrcUpB S τ = ((1 / 2 + (τ - 3 * Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * pccutDir S := by
  simp only [pcsrcUpB, hσ]; rw [if_neg h1, if_neg h2, if_neg h3, Complex.real_smul]

/-! ## Branch values of `pcsrcDnB` -/

private lemma pcsrcDnB_b1 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : τ ≤ Real.pi / 2) :
    pcsrcDnB S τ = pcsrcOuterDn S (τ / (Real.pi / 2)) := by
  simp only [pcsrcDnB, hσ]; rw [if_pos h1]

private lemma pcsrcDnB_b2 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : τ ≤ Real.pi) :
    pcsrcDnB S τ = ((1 - (τ - Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * pccutDir S := by
  simp only [pcsrcDnB, hσ]; rw [if_neg h1, if_pos h2, Complex.real_smul]

private lemma pcsrcDnB_b3 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : τ ≤ 3 * Real.pi / 2) :
    pcsrcDnB S τ = pcsrcInnerDn S ((τ - Real.pi) / (Real.pi / 2)) := by
  simp only [pcsrcDnB, hσ]; rw [if_neg h1, if_neg h2, if_pos h3]

private lemma pcsrcDnB_b4 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.pcperPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : ¬ τ ≤ 3 * Real.pi / 2) :
    pcsrcDnB S τ = ((-(1 / 2) - (τ - 3 * Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * pccutDir S := by
  simp only [pcsrcDnB, hσ]; rw [if_neg h1, if_neg h2, if_neg h3, Complex.real_smul]

/-! ## The four model points where consecutive branches meet -/

private lemma pcsrcOuterUp_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcOuterUp S 1 = (-1 : ℂ) * pccutDir S := by
  simp only [pcsrcOuterUp, mul_one]; rw [Complex.exp_pi_mul_I]; ring

private lemma pcsrcOuterUp_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcOuterUp S 0 = pccutDir S := by
  simp only [pcsrcOuterUp, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]

private lemma pcsrcInnerUp_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcInnerUp S 1 = (1 / 2 : ℂ) * pccutDir S := by
  simp only [pcsrcInnerUp, sub_self, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one]

private lemma pcsrcInnerUp_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcInnerUp S 0 = (-(1 / 2) : ℂ) * pccutDir S := by
  simp only [pcsrcInnerUp, sub_zero, mul_one]; rw [Complex.exp_pi_mul_I]; ring

private lemma pcsrcOuterDn_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcOuterDn S 1 = pccutDir S := by
  simp only [pcsrcOuterDn, mul_one]; rw [Complex.exp_pi_mul_I]; ring

private lemma pcsrcOuterDn_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcOuterDn S 0 = (-1 : ℂ) * pccutDir S := by
  simp only [pcsrcOuterDn, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  ring

private lemma pcsrcInnerDn_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcInnerDn S 1 = (-(1 / 2) : ℂ) * pccutDir S := by
  simp only [pcsrcInnerDn, mul_one]
  rw [show ((↑(-Real.pi) : ℂ) * Complex.I) = -(↑Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

private lemma pcsrcInnerDn_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcsrcInnerDn S 0 = (1 / 2 : ℂ) * pccutDir S := by
  simp only [pcsrcInnerDn, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one]

theorem pcsrcBranches {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcUpB S x =
          Work.Smooth.SphereJordan.pcsrcOuterUp S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcUpB S (Real.pi / 2 + x) =
          ((-1 + (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcUpB S (Real.pi + x) =
          Work.Smooth.SphereJordan.pcsrcInnerUp S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcUpB S (3 * Real.pi / 2 + x) =
          ((1 / 2 + (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcDnB S x =
          Work.Smooth.SphereJordan.pcsrcOuterDn S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcDnB S (Real.pi / 2 + x) =
          ((1 - (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcDnB S (Real.pi + x) =
          Work.Smooth.SphereJordan.pcsrcInnerDn S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.pcsrcDnB S (3 * Real.pi / 2 + x) =
          ((-(1 / 2) - (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) *
            Work.Smooth.SphereJordan.pccutDir S) := by
  refine ⟨fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_,
    fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_,
    fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_⟩
  · have hσ : Work.Smooth.SphereJordan.pcperPt x = x :=
      pcperPtIco ⟨hx0, by linarith [Real.pi_pos]⟩
    rw [pcsrcUpB_b1 S hσ hx1]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.pcperPt (Real.pi / 2) = Real.pi / 2 :=
        pcperPtIco ⟨by positivity, by linarith [Real.pi_pos]⟩
      rw [pcsrcUpB_b1 S hσ (le_refl _), div_self (by positivity : (0:ℝ) < Real.pi / 2).ne',
        pcsrcOuterUp_one, zero_div]
      norm_num
    · have hτ : Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by positivity, by linarith [Real.pi_pos, hx1]⟩
      have hσ := pcperPtIco hτ
      have h1 : ¬ Real.pi / 2 + x ≤ Real.pi / 2 := by linarith
      have h2 : Real.pi / 2 + x ≤ Real.pi := by linarith
      rw [pcsrcUpB_b2 S hσ h1 h2]
      simp only [add_sub_cancel_left]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.pcperPt Real.pi = Real.pi :=
        pcperPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have h1 : ¬ Real.pi ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h2 : Real.pi ≤ Real.pi := le_refl _
      rw [pcsrcUpB_b2 S hσ h1 h2,
        show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne']
      rw [zero_div, pcsrcInnerUp_zero]
      norm_num
    · have hτ : Real.pi + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, hx1]⟩
      have hσ := pcperPtIco hτ
      have h1 : ¬ Real.pi + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h2 : ¬ Real.pi + x ≤ Real.pi := by linarith
      have h3 : Real.pi + x ≤ 3 * Real.pi / 2 := by linarith
      rw [pcsrcUpB_b3 S hσ h1 h2 h3]
      simp only [add_sub_cancel_left]
  · rcases lt_or_eq_of_le hx1 with hxlt | hxeq
    · rcases eq_or_lt_of_le hx0 with hx | hx
      · rw [← hx, add_zero]
        have hσ : Work.Smooth.SphereJordan.pcperPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
          pcperPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have h1 : ¬ 3 * Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
        rw [pcsrcUpB_b3 S hσ h1 h2 (le_refl _),
          show 3 * Real.pi / 2 - Real.pi = Real.pi / 2 by ring,
          div_self (by positivity : (0:ℝ) < Real.pi / 2).ne', pcsrcInnerUp_one]
        norm_num
      · have hτ : 3 * Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
          ⟨by linarith [Real.pi_pos], by linarith⟩
        have hσ := pcperPtIco hτ
        have h1 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi := by linarith [Real.pi_pos]
        have h3 : ¬ 3 * Real.pi / 2 + x ≤ 3 * Real.pi / 2 := by linarith
        rw [pcsrcUpB_b4 S hσ h1 h2 h3]
        simp only [add_sub_cancel_left]
    · rw [hxeq, show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring]
      simp only [pcsrcUpB, pcperPt_two_pi]
      rw [if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2), zero_div, pcsrcOuterUp_zero,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne']
      norm_num
  · have hσ : Work.Smooth.SphereJordan.pcperPt x = x :=
      pcperPtIco ⟨hx0, by linarith [Real.pi_pos]⟩
    rw [pcsrcDnB_b1 S hσ hx1]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.pcperPt (Real.pi / 2) = Real.pi / 2 :=
        pcperPtIco ⟨by positivity, by linarith [Real.pi_pos]⟩
      rw [pcsrcDnB_b1 S hσ (le_refl _), div_self (by positivity : (0:ℝ) < Real.pi / 2).ne',
        pcsrcOuterDn_one, zero_div]
      norm_num
    · have hτ : Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by positivity, by linarith [Real.pi_pos, hx1]⟩
      have hσ := pcperPtIco hτ
      have h1 : ¬ Real.pi / 2 + x ≤ Real.pi / 2 := by linarith
      have h2 : Real.pi / 2 + x ≤ Real.pi := by linarith
      rw [pcsrcDnB_b2 S hσ h1 h2]
      simp only [add_sub_cancel_left]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.pcperPt Real.pi = Real.pi :=
        pcperPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have h1 : ¬ Real.pi ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      rw [pcsrcDnB_b2 S hσ h1 (le_refl _),
        show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne', zero_div, pcsrcInnerDn_zero]
      norm_num
    · have hτ : Real.pi + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, hx1]⟩
      have hσ := pcperPtIco hτ
      have h1 : ¬ Real.pi + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h2 : ¬ Real.pi + x ≤ Real.pi := by linarith
      have h3 : Real.pi + x ≤ 3 * Real.pi / 2 := by linarith
      rw [pcsrcDnB_b3 S hσ h1 h2 h3]
      simp only [add_sub_cancel_left]
  · rcases lt_or_eq_of_le hx1 with hxlt | hxeq
    · rcases eq_or_lt_of_le hx0 with hx | hx
      · rw [← hx, add_zero]
        have hσ : Work.Smooth.SphereJordan.pcperPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
          pcperPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have h1 : ¬ 3 * Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
        rw [pcsrcDnB_b3 S hσ h1 h2 (le_refl _),
          show 3 * Real.pi / 2 - Real.pi = Real.pi / 2 by ring,
          div_self (by positivity : (0:ℝ) < Real.pi / 2).ne', pcsrcInnerDn_one, zero_div]
        norm_num
      · have hτ : 3 * Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
          ⟨by linarith [Real.pi_pos], by linarith⟩
        have hσ := pcperPtIco hτ
        have h1 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi := by linarith [Real.pi_pos]
        have h3 : ¬ 3 * Real.pi / 2 + x ≤ 3 * Real.pi / 2 := by linarith
        rw [pcsrcDnB_b4 S hσ h1 h2 h3]
        simp only [add_sub_cancel_left]
    · rw [hxeq, show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring]
      simp only [pcsrcDnB, pcperPt_two_pi]
      rw [if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2), zero_div, pcsrcOuterDn_zero,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne']
      norm_num

end Work.SphereJordan
