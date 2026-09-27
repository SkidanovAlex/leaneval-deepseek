import Mathlib
import Submission.Work.EQ.LocModelDefs

/-!
# Elementary estimates for the local model: `lmU`, `lmSig` on the box `lmBox`

These are the estimates on which the Lipschitz/size bounds of the local model rest.
On the box `|ξ|, |η| ≤ lmH a a₀ = min s t / 16` one has `u = ξ - s ∈ (-17s/16, -15s/16)`, so
`|u| ∈ [15s/16, 17s/16]`, and `σ = √(u²+η²)` is sandwiched between `|u|` and `|u| + |η|`.
Consequences recorded here:

* `lmU a a₀ ξ < 0`, and `15 s / 16 ≤ σ ≤ |u| + |η|`;
* `|η| / |u| ≤ 16 lmH / (15 s)`;
* `1 - |η|/|u| ≤ -u/σ ≤ 1`.

These are exactly the estimates needed to control the ratio `η/σ` and the displacement
`(s - ξ)/σ` appearing in the normal form of `eqT` near the real fixed point `A = a₀`.
-/

set_option linter.unusedVariables false

namespace Work.EQ

theorem lmSigAux {a a₀ ξ η : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ Work.EQ.lmH a a₀) (hη : |η| ≤ Work.EQ.lmH a a₀) :
    Work.EQ.lmU a a₀ ξ < 0 ∧
    15 * Work.EQ.lmS a a₀ / 16 ≤ Work.EQ.lmSig a a₀ ξ η ∧
    Work.EQ.lmSig a a₀ ξ η ≤ |Work.EQ.lmU a a₀ ξ| + |η| ∧
    |η| / |Work.EQ.lmU a a₀ ξ| ≤ 16 * Work.EQ.lmH a a₀ / (15 * Work.EQ.lmS a a₀) ∧
    1 - |η| / |Work.EQ.lmU a a₀ ξ| ≤ -(Work.EQ.lmU a a₀ ξ) / Work.EQ.lmSig a a₀ ξ η ∧
    -(Work.EQ.lmU a a₀ ξ) / Work.EQ.lmSig a a₀ ξ η ≤ 1 := by
  have hs : 0 < lmS a a₀ := by rw [lmS]; linarith
  have hHle : lmH a a₀ ≤ lmS a a₀ / 16 := by
    rw [lmH]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hxi : |ξ| ≤ lmS a a₀ / 16 := le_trans hξ hHle
  have heta : |η| ≤ lmS a a₀ / 16 := le_trans hη hHle
  have hξle : ξ ≤ lmS a a₀ / 16 := (abs_le.mp hxi).2
  have hu_neg : lmU a a₀ ξ < 0 := by rw [lmU_eq]; linarith
  have hu_abs : |lmU a a₀ ξ| = lmS a a₀ - ξ := by
    rw [abs_of_neg hu_neg, lmU_eq]; ring
  have hu_ge : 15 * lmS a a₀ / 16 ≤ |lmU a a₀ ξ| := by rw [hu_abs]; linarith
  have hu_pos : 0 < |lmU a a₀ ξ| := lt_of_lt_of_le (by linarith) hu_ge
  have h15 : (0:ℝ) ≤ 15 * lmS a a₀ / 16 := by linarith
  have h2sig : 15 * lmS a a₀ / 16 ≤ lmSig a a₀ ξ η := by
    rw [lmSig]
    refine (Real.le_sqrt h15 (by positivity)).mpr ?_
    have hsq : (15 * lmS a a₀ / 16)^2 ≤ (lmU a a₀ ξ)^2 := by
      have hh := pow_le_pow_left₀ h15 hu_ge 2
      rwa [sq_abs] at hh
    nlinarith [sq_nonneg η]
  have hσpos : 0 < lmSig a a₀ ξ η := lt_of_lt_of_le (by linarith) h2sig
  have h3sig : lmSig a a₀ ξ η ≤ |lmU a a₀ ξ| + |η| := by
    rw [lmSig]
    refine (Real.sqrt_le_left (by positivity)).mpr ?_
    nlinarith [sq_abs (lmU a a₀ ξ), sq_abs η,
      mul_nonneg (abs_nonneg (lmU a a₀ ξ)) (abs_nonneg η)]
  have h4 : |η| / |lmU a a₀ ξ| ≤ 16 * lmH a a₀ / (15 * lmS a a₀) := by
    have hkey : |η| * (15 * lmS a a₀) ≤ 16 * lmH a a₀ * |lmU a a₀ ξ| := by
      have hlmH : 0 ≤ lmH a a₀ := le_trans (abs_nonneg η) hη
      have h1' : |η| * (15 * lmS a a₀) ≤ lmH a a₀ * (15 * lmS a a₀) :=
        mul_le_mul_of_nonneg_right hη (by linarith)
      have h2' : lmH a a₀ * (15 * lmS a a₀) ≤ 16 * lmH a a₀ * |lmU a a₀ ξ| := by
        have h3' := mul_le_mul_of_nonneg_left hu_ge (by linarith : (0:ℝ) ≤ 16 * lmH a a₀)
        linarith
      linarith
    rw [div_le_iff₀ hu_pos]
    rw [show (16 * lmH a a₀ / (15 * lmS a a₀)) * |lmU a a₀ ξ|
          = 16 * lmH a a₀ * |lmU a a₀ ξ| / (15 * lmS a a₀) by ring]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 15 * lmS a a₀)]
    exact hkey
  have hden : 0 < |lmU a a₀ ξ| + |η| := by
    have := abs_nonneg η; linarith
  have hA : 1 - |η| / |lmU a a₀ ξ| ≤ |lmU a a₀ ξ| / (|lmU a a₀ ξ| + |η|) := by
    rw [le_div_iff₀ hden]
    have huu : (1 - |η| / |lmU a a₀ ξ|) * (|lmU a a₀ ξ| + |η|) * |lmU a a₀ ξ|
        = (|lmU a a₀ ξ| - |η|) * (|lmU a a₀ ξ| + |η|) := by
      field_simp
    rw [← mul_le_mul_iff_of_pos_right hu_pos, huu]
    nlinarith [sq_abs (lmU a a₀ ξ), sq_abs η]
  have hB : |lmU a a₀ ξ| / (|lmU a a₀ ξ| + |η|) ≤ |lmU a a₀ ξ| / lmSig a a₀ ξ η :=
    div_le_div_of_nonneg_left (abs_nonneg _) hσpos h3sig
  have hneg : -(lmU a a₀ ξ) / lmSig a a₀ ξ η = |lmU a a₀ ξ| / lmSig a a₀ ξ η := by
    rw [abs_of_neg hu_neg]
  refine ⟨hu_neg, h2sig, h3sig, h4, ?_, ?_⟩
  · rw [hneg]; exact le_trans hA hB
  · rw [hneg, div_le_one hσpos, lmSig]
    refine (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr ?_
    nlinarith [sq_abs (lmU a a₀ ξ), sq_nonneg η]

end Work.EQ
