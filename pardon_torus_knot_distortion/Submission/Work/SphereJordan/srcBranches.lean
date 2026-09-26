import Mathlib
import Submission.Work.Smooth.SphereJordan.annulusCuts

/-!
# The branch values of the source boundary curves `srcUpB`, `srcDnB`

`srcUpB` and `srcDnB` are the `2π`-periodic parametrisations of the two halves of the
boundary of the model half-annulus (`1/2 ≤ ‖z‖ ≤ 1`, `0 ≤ Im (z/u)` respectively
`Im (z/u) ≤ 0`).  They are defined by reducing the parameter modulo `2π` (via `perPt`) and
then dispatching on which quarter of the period the reduced parameter lies in.

This file records the values that these two functions take on the four consecutive
quarter-periods, for parameters in the *closed* quarter intervals
`[0, π/2]`, `[π/2, π]`, `[π, 3π/2]` and `[3π/2, 2π]`.

Because the quarter conditions in the definitions are stated with `≤`, the endpoints are
shared between consecutive branches; at each shared endpoint the two branch formulas agree,
and the lemmas below record that agreement explicitly.  The parameter `3π/2 + π/2 = 2π` is
additionally wrapped to `0` by `perPt`, so the fourth quarter of the period is handled by the
first branch there.
-/

namespace Work.SphereJordan

open Work.Smooth.SphereJordan

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Elementary facts about the period reduction `perPt` -/

private lemma perPtIco {τ : ℝ} (h : τ ∈ Set.Ico (0:ℝ) (2 * Real.pi)) :
    Work.Smooth.SphereJordan.perPt τ = τ := by
  rw [Work.Smooth.SphereJordan.perPt]
  have : ⌊τ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg h.1 (by positivity), (div_lt_one (by positivity)).mpr h.2⟩
  rw [this]; ring

private lemma perPt_two_pi : Work.Smooth.SphereJordan.perPt (2 * Real.pi) = 0 := by
  rw [Work.Smooth.SphereJordan.perPt, div_self (by positivity : (0:ℝ) < 2 * Real.pi).ne',
    Int.floor_one]
  ring

/-! ## Branch values of `srcUpB` -/

private lemma srcUpB_b1 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : τ ≤ Real.pi / 2) :
    srcUpB S τ = srcOuterUp S (τ / (Real.pi / 2)) := by
  simp only [srcUpB, hσ]; rw [if_pos h1]

private lemma srcUpB_b2 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : τ ≤ Real.pi) :
    srcUpB S τ = ((-1 + (τ - Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * cutDir S := by
  simp only [srcUpB, hσ]; rw [if_neg h1, if_pos h2, Complex.real_smul]

private lemma srcUpB_b3 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : τ ≤ 3 * Real.pi / 2) :
    srcUpB S τ = srcInnerUp S ((τ - Real.pi) / (Real.pi / 2)) := by
  simp only [srcUpB, hσ]; rw [if_neg h1, if_neg h2, if_pos h3]

private lemma srcUpB_b4 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : ¬ τ ≤ 3 * Real.pi / 2) :
    srcUpB S τ = ((1 / 2 + (τ - 3 * Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * cutDir S := by
  simp only [srcUpB, hσ]; rw [if_neg h1, if_neg h2, if_neg h3, Complex.real_smul]

/-! ## Branch values of `srcDnB` -/

private lemma srcDnB_b1 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : τ ≤ Real.pi / 2) :
    srcDnB S τ = srcOuterDn S (τ / (Real.pi / 2)) := by
  simp only [srcDnB, hσ]; rw [if_pos h1]

private lemma srcDnB_b2 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : τ ≤ Real.pi) :
    srcDnB S τ = ((1 - (τ - Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * cutDir S := by
  simp only [srcDnB, hσ]; rw [if_neg h1, if_pos h2, Complex.real_smul]

private lemma srcDnB_b3 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : τ ≤ 3 * Real.pi / 2) :
    srcDnB S τ = srcInnerDn S ((τ - Real.pi) / (Real.pi / 2)) := by
  simp only [srcDnB, hσ]; rw [if_neg h1, if_neg h2, if_pos h3]

private lemma srcDnB_b4 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {τ : ℝ}
    (hσ : Work.Smooth.SphereJordan.perPt τ = τ) (h1 : ¬ τ ≤ Real.pi / 2)
    (h2 : ¬ τ ≤ Real.pi) (h3 : ¬ τ ≤ 3 * Real.pi / 2) :
    srcDnB S τ = ((-(1 / 2) - (τ - 3 * Real.pi / 2) / (Real.pi / 2) / 2 : ℝ) : ℂ) * cutDir S := by
  simp only [srcDnB, hσ]; rw [if_neg h1, if_neg h2, if_neg h3, Complex.real_smul]

/-! ## The four model points where consecutive branches meet -/

private lemma srcOuterUp_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcOuterUp S 1 = (-1 : ℂ) * cutDir S := by
  simp only [srcOuterUp, mul_one]; rw [Complex.exp_pi_mul_I]; ring

private lemma srcOuterUp_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcOuterUp S 0 = cutDir S := by
  simp only [srcOuterUp, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]

private lemma srcInnerUp_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcInnerUp S 1 = (1 / 2 : ℂ) * cutDir S := by
  simp only [srcInnerUp, sub_self, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one]

private lemma srcInnerUp_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcInnerUp S 0 = (-(1 / 2) : ℂ) * cutDir S := by
  simp only [srcInnerUp, sub_zero, mul_one]; rw [Complex.exp_pi_mul_I]; ring

private lemma srcOuterDn_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcOuterDn S 1 = cutDir S := by
  simp only [srcOuterDn, mul_one]; rw [Complex.exp_pi_mul_I]; ring

private lemma srcOuterDn_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcOuterDn S 0 = (-1 : ℂ) * cutDir S := by
  simp only [srcOuterDn, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  ring

private lemma srcInnerDn_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcInnerDn S 1 = (-(1 / 2) : ℂ) * cutDir S := by
  simp only [srcInnerDn, mul_one]
  rw [show ((↑(-Real.pi) : ℂ) * Complex.I) = -(↑Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

private lemma srcInnerDn_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    srcInnerDn S 0 = (1 / 2 : ℂ) * cutDir S := by
  simp only [srcInnerDn, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one]

theorem srcBranches {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcUpB S x =
          Work.Smooth.SphereJordan.srcOuterUp S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcUpB S (Real.pi / 2 + x) =
          ((-1 + (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) * Work.Smooth.SphereJordan.cutDir S) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcUpB S (Real.pi + x) =
          Work.Smooth.SphereJordan.srcInnerUp S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcUpB S (3 * Real.pi / 2 + x) =
          ((1 / 2 + (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) * Work.Smooth.SphereJordan.cutDir S) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcDnB S x =
          Work.Smooth.SphereJordan.srcOuterDn S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcDnB S (Real.pi / 2 + x) =
          ((1 - (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) * Work.Smooth.SphereJordan.cutDir S) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcDnB S (Real.pi + x) =
          Work.Smooth.SphereJordan.srcInnerDn S (x / (Real.pi / 2))) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 →
        Work.Smooth.SphereJordan.srcDnB S (3 * Real.pi / 2 + x) =
          ((-(1 / 2) - (x / (Real.pi / 2)) / 2 : ℝ) : ℂ) *
            Work.Smooth.SphereJordan.cutDir S) := by
  refine ⟨fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_,
    fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_,
    fun x hx0 hx1 => ?_, fun x hx0 hx1 => ?_⟩
  · have hσ : Work.Smooth.SphereJordan.perPt x = x :=
      perPtIco ⟨hx0, by linarith [Real.pi_pos]⟩
    rw [srcUpB_b1 S hσ hx1]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.perPt (Real.pi / 2) = Real.pi / 2 :=
        perPtIco ⟨by positivity, by linarith [Real.pi_pos]⟩
      rw [srcUpB_b1 S hσ (le_refl _), div_self (by positivity : (0:ℝ) < Real.pi / 2).ne',
        srcOuterUp_one, zero_div]
      norm_num
    · have hτ : Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by positivity, by linarith [Real.pi_pos, hx1]⟩
      have hσ := perPtIco hτ
      have h1 : ¬ Real.pi / 2 + x ≤ Real.pi / 2 := by linarith
      have h2 : Real.pi / 2 + x ≤ Real.pi := by linarith
      rw [srcUpB_b2 S hσ h1 h2]
      simp only [add_sub_cancel_left]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.perPt Real.pi = Real.pi :=
        perPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have h1 : ¬ Real.pi ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h2 : Real.pi ≤ Real.pi := le_refl _
      rw [srcUpB_b2 S hσ h1 h2,
        show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne']
      rw [zero_div, srcInnerUp_zero]
      norm_num
    · have hτ : Real.pi + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, hx1]⟩
      have hσ := perPtIco hτ
      have h1 : ¬ Real.pi + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h2 : ¬ Real.pi + x ≤ Real.pi := by linarith
      have h3 : Real.pi + x ≤ 3 * Real.pi / 2 := by linarith
      rw [srcUpB_b3 S hσ h1 h2 h3]
      simp only [add_sub_cancel_left]
  · rcases lt_or_eq_of_le hx1 with hxlt | hxeq
    · rcases eq_or_lt_of_le hx0 with hx | hx
      · rw [← hx, add_zero]
        have hσ : Work.Smooth.SphereJordan.perPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
          perPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have h1 : ¬ 3 * Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
        rw [srcUpB_b3 S hσ h1 h2 (le_refl _),
          show 3 * Real.pi / 2 - Real.pi = Real.pi / 2 by ring,
          div_self (by positivity : (0:ℝ) < Real.pi / 2).ne', srcInnerUp_one]
        norm_num
      · have hτ : 3 * Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
          ⟨by linarith [Real.pi_pos], by linarith⟩
        have hσ := perPtIco hτ
        have h1 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi := by linarith [Real.pi_pos]
        have h3 : ¬ 3 * Real.pi / 2 + x ≤ 3 * Real.pi / 2 := by linarith
        rw [srcUpB_b4 S hσ h1 h2 h3]
        simp only [add_sub_cancel_left]
    · rw [hxeq, show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring]
      simp only [srcUpB, perPt_two_pi]
      rw [if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2), zero_div, srcOuterUp_zero,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne']
      norm_num
  · have hσ : Work.Smooth.SphereJordan.perPt x = x :=
      perPtIco ⟨hx0, by linarith [Real.pi_pos]⟩
    rw [srcDnB_b1 S hσ hx1]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.perPt (Real.pi / 2) = Real.pi / 2 :=
        perPtIco ⟨by positivity, by linarith [Real.pi_pos]⟩
      rw [srcDnB_b1 S hσ (le_refl _), div_self (by positivity : (0:ℝ) < Real.pi / 2).ne',
        srcOuterDn_one, zero_div]
      norm_num
    · have hτ : Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by positivity, by linarith [Real.pi_pos, hx1]⟩
      have hσ := perPtIco hτ
      have h1 : ¬ Real.pi / 2 + x ≤ Real.pi / 2 := by linarith
      have h2 : Real.pi / 2 + x ≤ Real.pi := by linarith
      rw [srcDnB_b2 S hσ h1 h2]
      simp only [add_sub_cancel_left]
  · rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, add_zero]
      have hσ : Work.Smooth.SphereJordan.perPt Real.pi = Real.pi :=
        perPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have h1 : ¬ Real.pi ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      rw [srcDnB_b2 S hσ h1 (le_refl _),
        show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne', zero_div, srcInnerDn_zero]
      norm_num
    · have hτ : Real.pi + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, hx1]⟩
      have hσ := perPtIco hτ
      have h1 : ¬ Real.pi + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have h2 : ¬ Real.pi + x ≤ Real.pi := by linarith
      have h3 : Real.pi + x ≤ 3 * Real.pi / 2 := by linarith
      rw [srcDnB_b3 S hσ h1 h2 h3]
      simp only [add_sub_cancel_left]
  · rcases lt_or_eq_of_le hx1 with hxlt | hxeq
    · rcases eq_or_lt_of_le hx0 with hx | hx
      · rw [← hx, add_zero]
        have hσ : Work.Smooth.SphereJordan.perPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
          perPtIco ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have h1 : ¬ 3 * Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
        rw [srcDnB_b3 S hσ h1 h2 (le_refl _),
          show 3 * Real.pi / 2 - Real.pi = Real.pi / 2 by ring,
          div_self (by positivity : (0:ℝ) < Real.pi / 2).ne', srcInnerDn_one, zero_div]
        norm_num
      · have hτ : 3 * Real.pi / 2 + x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
          ⟨by linarith [Real.pi_pos], by linarith⟩
        have hσ := perPtIco hτ
        have h1 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have h2 : ¬ 3 * Real.pi / 2 + x ≤ Real.pi := by linarith [Real.pi_pos]
        have h3 : ¬ 3 * Real.pi / 2 + x ≤ 3 * Real.pi / 2 := by linarith
        rw [srcDnB_b4 S hσ h1 h2 h3]
        simp only [add_sub_cancel_left]
    · rw [hxeq, show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring]
      simp only [srcDnB, perPt_two_pi]
      rw [if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2), zero_div, srcOuterDn_zero,
        div_self (by positivity : (0:ℝ) < Real.pi / 2).ne']
      norm_num

end Work.SphereJordan
