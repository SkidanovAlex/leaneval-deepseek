import Mathlib
import Submission.Work.KMTPlan.A6.iwP_element_le_sharp
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

/-!
# Separation of the Ionescu–Wainger arithmetic frequency set `(ℚ/ℤ)_{≤l}` (sharp form)

Appendix A of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages* (Annals of Math. 195 (2022)), needs to know that two distinct elements of
the arithmetic frequency set `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` are well separated in the circle
`ℝ ⧸ ℤ`.  The sibling module `Submission.Work.Analysis.IonescuWainger.iw_height_separated`
proves the coarser statement `iw_height_separated`, whose separation radius
`2^{-C 2^{ρ l}}` is governed by the *coarse* element bound `iwP_element_le`.

Here we prove the **sharp** form, whose separation radius
`2^{-C (1 + l 2^{ρ l / 2} + l)}` is governed by the sharp element bound
`Work.KMTPlan.A6.iwP_element_le_sharp` proved in the sibling module: every element of
`P_{≤l}` is at most `2^{C (1 + l 2^{ρ l/2} + l)}`.

The argument is elementary once that bound is available.  Each `α ∈ (ℚ/ℤ)_{≤l}` is killed by
some positive denominator `q ∈ P_{≤l}` (this is `iwArithFreqs_exists_den`).  For `α ≠ β` with
killers `q, q'`, the difference `α - β` is a non-zero torsion point of order dividing `q q'`,
so `1 ≤ (q q') ‖α - β‖` (Mathlib's
`AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder`), whence

`1 / (q q') ≤ ‖α - β‖`.

Since `q, q' ≤ 2^{C (1 + l 2^{ρ l/2} + l)}` we get `q q' ≤ 2^{2C (1 + l 2^{ρ l/2} + l)}`, and
the claim follows with the constant `2C + 1`.

## Main result

* `Work.KMTPlan.A6.iwArithFreqs_separated`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

/-- **Separation of the Ionescu–Wainger arithmetic frequency set** (sharp form).  Two distinct
elements of `(ℚ/ℤ)_{≤l}` are at distance at least `2^{-C (1 + l 2^{ρ l/2} + l)}` in the circle
`ℝ ⧸ ℤ`. -/
theorem iwArithFreqs_separated (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l (α β : Work.Analysis.IonescuWainger.Circle),
      α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l →
      β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l → α ≠ β →
      (2 : ℝ) ^ (-(C * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)))) ≤ ‖α - β‖ := by
  obtain ⟨K, hKpos, hKelem⟩ := iwP_element_le_sharp ρ hρ hρ1
  refine ⟨2 * K + 1, by linarith, ?_⟩
  intro l α β hα hβ hne
  obtain ⟨q, hqpos, hqP, hqα⟩ := iwArithFreqs_exists_den hα
  obtain ⟨q', hq'pos, hq'P, hq'β⟩ := iwArithFreqs_exists_den hβ
  set S : ℝ := 1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ) with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    have ht : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hprod : 0 ≤ (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := mul_nonneg hl ht
    linarith
  have hqb : (q : ℝ) ≤ (2 : ℝ) ^ (K * S) := by rw [hS]; exact hKelem l q hqP
  have hq'b : (q' : ℝ) ≤ (2 : ℝ) ^ (K * S) := by rw [hS]; exact hKelem l q' hq'P
  have hQb : ((q * q' : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((2 * K) * S) := by
    rw [Nat.cast_mul]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (K * S) := Real.rpow_pos_of_pos (by norm_num) _
    calc (q : ℝ) * (q' : ℝ)
        ≤ (2 : ℝ) ^ (K * S) * (2 : ℝ) ^ (K * S) :=
          mul_le_mul hqb hq'b (by positivity) hp.le
      _ = (2 : ℝ) ^ ((2 * K) * S) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
  have hposQ : (0 : ℝ) < ((q * q' : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hqpos hq'pos
  have hkey : (2 : ℝ) ^ (-((2 * K) * S)) ≤ (1 : ℝ) / ((q * q' : ℕ) : ℝ) := by
    rw [Real.rpow_neg (by norm_num), inv_eq_one_div]
    exact one_div_le_one_div_of_le hposQ hQb
  have hexp : -((2 * K + 1) * S) ≤ -((2 * K) * S) := by
    have : (2 * K) * S ≤ (2 * K + 1) * S := by nlinarith [hSnn]
    linarith
  have hstep : (2 : ℝ) ^ (-((2 * K + 1) * S)) ≤ (2 : ℝ) ^ (-((2 * K) * S)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hexp
  have hkill1 : (q * q') • α = 0 := by
    rw [mul_smul, smul_comm q q' α, hqα, smul_zero]
  have hkill2 : (q * q') • β = 0 := by rw [mul_smul, hq'β, smul_zero]
  have hsep : (1 : ℝ) / ((q * q' : ℕ) : ℝ) ≤ ‖α - β‖ :=
    one_div_le_norm_of_ne (Nat.mul_pos hqpos hq'pos) hkill1 hkill2 hne
  exact le_trans hstep (le_trans hkey hsep)

end Work.KMTPlan.A6
