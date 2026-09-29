import Mathlib
import Submission.Work.TMC16Core.Trig.abs_log_sub_log_le

namespace Work.TMC16Core.Core

/-! ## The sharp logarithmic comparison sum

Same structure as `comp_sum_le`, but the bad-block pointwise bound is sharpened from the
constant `4` to `Real.log (1 + 20 π η L / 3)`, which is what the sharp finale needs. -/

/-- **Good-block pointwise bound.**  If `0 < τ ≤ 1/2`, `0 < ν ≤ 1/2`, `|τ - ν| ≤ η`, `η ≥ 0`
and the sine factor dominates the shift, `2 π η ≤ sin (π ν)`, then
`|log (sin (π τ)) - log (sin (π ν))| ≤ 2 π η / sin (π ν)`. -/
private lemma good_log_bound {τ ν η : ℝ} (hη : 0 ≤ η) (hτ0 : 0 < τ) (hτh : τ ≤ 1 / 2)
    (hν0 : 0 < ν) (hνh : ν ≤ 1 / 2) (hdiff : |τ - ν| ≤ η)
    (hgood : 2 * Real.pi * η ≤ Real.sin (Real.pi * ν)) :
    |Real.log (Real.sin (Real.pi * τ)) - Real.log (Real.sin (Real.pi * ν))|
      ≤ 2 * Real.pi * η * (Real.sin (Real.pi * ν))⁻¹ := by
  have ha : 0 < Real.sin (Real.pi * τ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hτ0)
      (by nlinarith [Real.pi_pos, hτh])
  have hb : 0 < Real.sin (Real.pi * ν) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hν0)
      (by nlinarith [Real.pi_pos, hνh])
  have hc : 0 ≤ Real.pi * η := mul_nonneg Real.pi_pos.le hη
  have hab : |Real.sin (Real.pi * τ) - Real.sin (Real.pi * ν)| ≤ Real.pi * η := by
    have h1 := Real.abs_sin_sub_sin_le (Real.pi * τ) (Real.pi * ν)
    rw [show Real.pi * τ - Real.pi * ν = Real.pi * (τ - ν) by ring, abs_mul,
        abs_of_pos Real.pi_pos] at h1
    linarith [mul_le_mul_of_nonneg_left hdiff Real.pi_pos.le]
  have hcb : Real.pi * η ≤ Real.sin (Real.pi * ν) / 2 := by linarith
  have h := Work.TMC16Core.Trig.abs_log_sub_log_le ha hb hc hab hcb
  rwa [show 2 * (Real.pi * η) * (Real.sin (Real.pi * ν))⁻¹
      = 2 * Real.pi * η * (Real.sin (Real.pi * ν))⁻¹ by ring] at h

/-- **Bad-block pointwise bound (sharp).** -/
private lemma bad_log_bound {L : ℕ} (hL : 1 ≤ L) {τ ν η : ℝ}
    (hη : 0 < η) (_hηL : η * (L : ℝ) ≤ 11 / 10)
    (hτ0 : 0 < τ) (hτh : τ ≤ 1 / 2) (hτsep : 3 / (20 * (L : ℝ)) ≤ τ)
    (hν0 : 0 < ν) (hνh : ν ≤ 1 / 2) (hνsep : 1 / (2 * (L : ℝ)) ≤ ν)
    (hdiff : |τ - ν| ≤ η)
    (hbad : Real.sin (Real.pi * ν) ≤ 2 * Real.pi * η) :
    |Real.log (Real.sin (Real.pi * τ)) - Real.log (Real.sin (Real.pi * ν))|
      ≤ Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) := by
  have hLR : (0:ℝ) < (L:ℝ) := by exact_mod_cast (show 0 < L by omega)
  have ha : 0 < Real.sin (Real.pi * τ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hτ0) (by nlinarith [Real.pi_pos, hτh])
  have hb : 0 < Real.sin (Real.pi * ν) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hν0) (by nlinarith [Real.pi_pos, hνh])
  have ha2 : 2 * τ ≤ Real.sin (Real.pi * τ) := by
    have h := Real.mul_le_sin (show (0:ℝ) ≤ Real.pi * τ by positivity)
      (show Real.pi * τ ≤ Real.pi / 2 by nlinarith [Real.pi_pos, hτh])
    have h' : (2 / Real.pi) * (Real.pi * τ) = 2 * τ := by field_simp
    linarith [h, h']
  have hb2 : 2 * ν ≤ Real.sin (Real.pi * ν) := by
    have h := Real.mul_le_sin (show (0:ℝ) ≤ Real.pi * ν by positivity)
      (show Real.pi * ν ≤ Real.pi / 2 by nlinarith [Real.pi_pos, hνh])
    have h' : (2 / Real.pi) * (Real.pi * ν) = 2 * ν := by field_simp
    linarith [h, h']
  have h3τ : 3 / (10 * (L:ℝ)) ≤ Real.sin (Real.pi * τ) := by
    have hle : 3 / (10 * (L:ℝ)) ≤ 2 * τ := by
      rw [div_le_iff₀ (show (0:ℝ) < 10 * (L:ℝ) by positivity)]
      have hsep := hτsep
      rw [div_le_iff₀ (show (0:ℝ) < 20 * (L:ℝ) by positivity)] at hsep
      nlinarith [hsep]
    linarith [ha2, hle]
  have h2νL : 1 ≤ 2 * ν * (L:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hνsep (show (0:ℝ) ≤ 2 * (L:ℝ) by positivity)
    have h' : 1 / (2 * (L:ℝ)) * (2 * (L:ℝ)) = 1 := by field_simp
    linarith [h, h']
  have h3ν : 3 / (10 * (L:ℝ)) ≤ Real.sin (Real.pi * ν) := by
    have hle : 3 / (10 * (L:ℝ)) ≤ 2 * ν := by
      rw [div_le_iff₀ (show (0:ℝ) < 10 * (L:ℝ) by positivity)]
      nlinarith [h2νL]
    linarith [hb2, hle]
  have hnum : |Real.sin (Real.pi * τ) - Real.sin (Real.pi * ν)| ≤ Real.pi * η := by
    have h1 := Real.abs_sin_sub_sin_le (Real.pi * τ) (Real.pi * ν)
    rw [show Real.pi * τ - Real.pi * ν = Real.pi * (τ - ν) by ring, abs_mul,
        abs_of_pos Real.pi_pos] at h1
    linarith [mul_le_mul_of_nonneg_left hdiff Real.pi_pos.le]
  have hcoef : (0:ℝ) ≤ 20 * Real.pi * η * (L:ℝ) / 3 := by positivity
  have hkey : ∀ {X : ℝ}, 3 / (10 * (L:ℝ)) ≤ X →
      Real.pi * η ≤ (20 * Real.pi * η * (L:ℝ) / 3) * X := by
    intro X hX
    have hmul := mul_le_mul_of_nonneg_left hX hcoef
    have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLR
    have he : (20 * Real.pi * η * (L:ℝ) / 3) * (3 / (10 * (L:ℝ))) = 2 * (Real.pi * η) := by
      field_simp
      ring
    linarith [hmul, he, hη]
  rcases le_total (Real.sin (Real.pi * ν)) (Real.sin (Real.pi * τ)) with hge | hle
  · have hratio : Real.sin (Real.pi * τ) / Real.sin (Real.pi * ν)
        ≤ 1 + 20 * Real.pi * η * (L:ℝ) / 3 := by
      rw [div_le_iff₀ hb]
      have hX := hkey h3ν
      have hle' : Real.sin (Real.pi * τ) - Real.sin (Real.pi * ν) ≤ Real.pi * η :=
        le_trans (le_abs_self _) hnum
      nlinarith [hX, hle']
    have hlogeq : |Real.log (Real.sin (Real.pi * τ)) - Real.log (Real.sin (Real.pi * ν))|
        = Real.log (Real.sin (Real.pi * τ)) - Real.log (Real.sin (Real.pi * ν)) :=
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hge))
    have hsub : Real.log (Real.sin (Real.pi * τ)) - Real.log (Real.sin (Real.pi * ν))
        = Real.log (Real.sin (Real.pi * τ) / Real.sin (Real.pi * ν)) :=
      (Real.log_div ha.ne' hb.ne').symm
    rw [hlogeq, hsub]
    exact Real.log_le_log (div_pos ha hb) hratio
  · have hratio : Real.sin (Real.pi * ν) / Real.sin (Real.pi * τ)
        ≤ 1 + 20 * Real.pi * η * (L:ℝ) / 3 := by
      rw [div_le_iff₀ ha]
      have hX := hkey h3τ
      have hnum' : |Real.sin (Real.pi * ν) - Real.sin (Real.pi * τ)| ≤ Real.pi * η := by
        rw [abs_sub_comm]; exact hnum
      have hle' : Real.sin (Real.pi * ν) - Real.sin (Real.pi * τ) ≤ Real.pi * η :=
        le_trans (le_abs_self _) hnum'
      nlinarith [hX, hle']
    have hlogeq : |Real.log (Real.sin (Real.pi * τ)) - Real.log (Real.sin (Real.pi * ν))|
        = Real.log (Real.sin (Real.pi * ν)) - Real.log (Real.sin (Real.pi * τ)) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hle))]
      ring
    have hsub : Real.log (Real.sin (Real.pi * ν)) - Real.log (Real.sin (Real.pi * τ))
        = Real.log (Real.sin (Real.pi * ν) / Real.sin (Real.pi * τ)) :=
      (Real.log_div hb.ne' ha.ne').symm
    rw [hlogeq, hsub]
    exact Real.log_le_log (div_pos hb ha) hratio

theorem comp_sum_sharp {L : ℕ} (hL : 2 ≤ L) {G : Finset ℕ} {τ ν : ℕ → ℝ} {η : ℝ} {bad : Finset ℕ}
    (hbadsub : bad ⊆ G) (hη : 0 < η) (hηL : η * (L : ℝ) ≤ 11 / 10)
    (hτ0 : ∀ j ∈ G, 0 < τ j) (hτh : ∀ j ∈ G, τ j ≤ 1 / 2)
    (hτsep : ∀ j ∈ G, 3 / (20 * (L : ℝ)) ≤ τ j)
    (hν0 : ∀ j ∈ G, 0 < ν j) (hνh : ∀ j ∈ G, ν j ≤ 1 / 2)
    (hνsep : ∀ j ∈ G, 1 / (2 * (L : ℝ)) ≤ ν j)
    (hdiff : ∀ j ∈ G, |τ j - ν j| ≤ η)
    (hgood : ∀ j ∈ G, j ∉ bad → 2 * Real.pi * η ≤ Real.sin (Real.pi * ν j))
    (hbad : ∀ j ∈ bad, Real.sin (Real.pi * ν j) ≤ 2 * Real.pi * η) :
    |∑ j ∈ G, (Real.log (Real.sin (Real.pi * τ j)) - Real.log (Real.sin (Real.pi * ν j)))|
      ≤ 2 * Real.pi * η * (∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹)
        + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ) := by
  set f : ℕ → ℝ :=
    fun j => Real.log (Real.sin (Real.pi * τ j)) - Real.log (Real.sin (Real.pi * ν j)) with hf
  have hsplit : ∑ j ∈ G, |f j| = ∑ j ∈ G \ bad, |f j| + ∑ j ∈ bad, |f j| := by
    have h := Finset.sum_sdiff (f := fun j => |f j|) hbadsub
    linarith
  have hgood_sum : ∑ j ∈ G \ bad, |f j|
      ≤ 2 * Real.pi * η * (∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹) := by
    have h1 : ∑ j ∈ G \ bad, |f j|
        ≤ ∑ j ∈ G \ bad, 2 * Real.pi * η * (Real.sin (Real.pi * ν j))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjG : j ∈ G := (Finset.mem_sdiff.mp hj).1
      have hjnb : j ∉ bad := (Finset.mem_sdiff.mp hj).2
      have h := good_log_bound hη.le (hτ0 j hjG) (hτh j hjG) (hν0 j hjG) (hνh j hjG)
        (hdiff j hjG) (hgood j hjG hjnb)
      simpa [hf] using h
    have h2 : ∑ j ∈ G \ bad, 2 * Real.pi * η * (Real.sin (Real.pi * ν j))⁻¹
        = 2 * Real.pi * η * ∑ j ∈ G \ bad, (Real.sin (Real.pi * ν j))⁻¹ := by
      rw [Finset.mul_sum]
    have h3 : ∑ j ∈ G \ bad, (Real.sin (Real.pi * ν j))⁻¹
        ≤ ∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      intro j hjG _
      exact inv_nonneg.mpr (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hν0 j hjG))
        (by nlinarith [Real.pi_pos, hνh j hjG])))
    calc ∑ j ∈ G \ bad, |f j|
        ≤ 2 * Real.pi * η * ∑ j ∈ G \ bad, (Real.sin (Real.pi * ν j))⁻¹ := by
          rw [← h2]; exact h1
      _ ≤ 2 * Real.pi * η * ∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹ :=
          mul_le_mul_of_nonneg_left h3
            (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi) hη.le)
  have hbad_sum : ∑ j ∈ bad, |f j|
      ≤ Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ) := by
    have h1 : ∑ j ∈ bad, |f j|
        ≤ ∑ j ∈ bad, Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjG : j ∈ G := hbadsub hj
      have h := bad_log_bound (by omega : 1 ≤ L) hη hηL (hτ0 j hjG) (hτh j hjG)
        (hτsep j hjG) (hν0 j hjG) (hνh j hjG) (hνsep j hjG) (hdiff j hjG) (hbad j hj)
      simpa [hf] using h
    have h2 : ∑ j ∈ bad, Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3)
        = Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    linarith
  calc |∑ j ∈ G, f j| ≤ ∑ j ∈ G, |f j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ G \ bad, |f j| + ∑ j ∈ bad, |f j| := hsplit
    _ ≤ 2 * Real.pi * η * (∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹)
          + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ) := by
        linarith [hgood_sum, hbad_sum]

end Work.TMC16Core.Core
