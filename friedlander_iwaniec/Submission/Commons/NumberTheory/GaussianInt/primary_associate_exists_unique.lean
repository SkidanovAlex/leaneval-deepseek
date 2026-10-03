import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.units_classification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

set_option linter.unusedVariables false

/-- An even integer reduces to `0` or `2` modulo `4`. -/
theorem even_cast_zmod4 (n : ℤ) (h : Even n) : (n : ZMod 4) = 0 ∨ (n : ZMod 4) = 2 := by
  obtain ⟨e, rfl⟩ := h
  rcases Int.even_or_odd e with he | he
  · left
    show (((e + e : ℤ)) : ZMod 4) = (((0 : ℤ)) : ZMod 4)
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    obtain ⟨k, rfl⟩ := he
    use -k; ring
  · right
    show (((e + e : ℤ)) : ZMod 4) = (((2 : ℤ)) : ZMod 4)
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    obtain ⟨k, rfl⟩ := he
    use -k; ring

/-- `a ^ 2 + b ^ 2` is odd exactly when `a` and `b` have opposite parity. -/
theorem odd_sq_add_sq {a b : ℤ} (h : Odd (a ^ 2 + b ^ 2)) :
    (Odd a ∧ Even b) ∨ (Even a ∧ Odd b) := by
  have h1 : Odd (a ^ 2) ↔ Odd a := by rw [Int.odd_pow]; simp
  have h2 : Even (b ^ 2) ↔ Even b := by
    constructor
    · intro hb2
      by_contra hb
      have hbo : Odd b := Int.not_even_iff_odd.mp hb
      have hb2' : Odd (b ^ 2) := hbo.pow
      exact (Int.not_even_iff_odd.mpr hb2') hb2
    · intro hb
      rw [pow_two]
      exact hb.mul_right b
  have h3 : Odd (a ^ 2) ↔ Even (b ^ 2) := Int.odd_add.mp h
  have hab : Odd a ↔ Even b := h1.symm.trans (h3.trans h2)
  rcases Int.even_or_odd a with ha | ha
  · right
    exact ⟨ha, Int.not_even_iff_odd.mp (hab.not.mp (Int.not_odd_iff_even.mpr ha))⟩
  · left
    exact ⟨ha, hab.mp ha⟩

/-- The element `i` of `ℤ[i]` is a unit. -/
theorem isUnit_sqrtd : IsUnit (⟨0, 1⟩ : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_one_iff (x := (⟨0, 1⟩ : GaussianInt))]
  decide

/-- The element `-i` of `ℤ[i]` is a unit. -/
theorem isUnit_neg_sqrtd : IsUnit (⟨0, -1⟩ : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_one_iff (x := (⟨0, -1⟩ : GaussianInt))]
  decide

/-- If `u` is a unit then `u * z` is associated to `z`. -/
theorem associated_of_isUnit_mul_left {u z : GaussianInt} (hu : IsUnit u) :
    Associated (u * z) z := by
  have h : Associated u 1 := associated_one_iff_isUnit.mpr hu
  simpa [mul_comm] using h.mul_left z

/-- If `w` is a primary element (odd real part, and `im ≡ re - 1 (mod 4)`) then the only
unit `ε` for which `w * ε` is again primary is `ε = 1`. -/
theorem unit_eq_one_of_primary {w : GaussianInt} (hwre : Odd w.re) (hwe : Even w.im)
    (hwc : (w.im : ZMod 4) = (w.re : ZMod 4) - 1)
    {ε : GaussianIntˣ} (hεre : Odd (w * ↑ε).re)
    (hεc : ((w * ↑ε).im : ZMod 4) = ((w * ↑ε).re : ZMod 4) - 1) :
    (↑ε : GaussianInt) = 1 := by
  have hunit : IsUnit (↑ε : GaussianInt) := Units.isUnit ε
  rw [units_classification] at hunit
  rcases hunit with h1 | h1 | h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hεre hεc
    simp only [mul_neg, mul_one, Zsqrtd.re_neg, Zsqrtd.im_neg] at hεre hεc
    push_cast at hεc
    have hwc' : -(w.im : ZMod 4) = -(w.re : ZMod 4) + 1 := by rw [hwc]; ring
    rw [hwc'] at hεc
    have : (1 : ZMod 4) = -1 := by linear_combination hεc
    exact absurd this (by decide)
  · exfalso
    rw [h1] at hεre
    simp only [Zsqrtd.re_mul, mul_zero, mul_one, zero_add, neg_one_mul] at hεre
    exact (Int.not_even_iff_odd.mpr hεre) (hwe.neg)
  · exfalso
    rw [h1] at hεre
    simp only [Zsqrtd.re_mul, mul_zero, mul_one, zero_add, neg_one_mul, neg_neg, mul_neg] at hεre
    exact (Int.not_even_iff_odd.mpr hεre) hwe

/-- Every nonzero Gaussian integer of odd norm has a unique **primary** associate, i.e. an
associate `w` with `w.re` odd, `w.im` even and `w.im ≡ w.re - 1 (mod 4)`. -/
theorem primary_associate_exists_unique {z : GaussianInt} (hz : z ≠ 0)
    (hodd : Odd z.norm.natAbs) :
    ∃! w : GaussianInt, Associated w z ∧ Odd w.re ∧ Even w.im ∧ (w.im : ZMod 4) = ((w.re : ZMod 4) - 1) := by
  have hodd' : Odd z.norm := Int.natAbs_odd.mp hodd
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by
    rw [Zsqrtd.norm_def]; ring
  have hpar : (Odd z.re ∧ Even z.im) ∨ (Even z.re ∧ Odd z.im) :=
    odd_sq_add_sq (hnorm ▸ hodd')
  obtain ⟨w0, hw0⟩ : ∃ w : GaussianInt,
      (Associated w z ∧ Odd w.re ∧ Even w.im ∧ (w.im : ZMod 4) = (w.re : ZMod 4) - 1) := by
    rcases hpar with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `z.re` odd, `z.im` even
      have hf : Even (z.im - z.re + 1) := (hb.sub_odd ha).add_odd odd_one
      rcases even_cast_zmod4 (z.im - z.re + 1) hf with hf0 | hf2
      · exact ⟨z, Associated.refl z, ha, hb, by
          push_cast at hf0 ⊢
          linear_combination hf0⟩
      · refine ⟨-z, ?_, ha.neg, hb.neg, ?_⟩
        · simpa using associated_of_isUnit_mul_left (z := z) isUnit_neg_one
        · simp only [Zsqrtd.re_neg, Zsqrtd.im_neg]
          push_cast at hf2 ⊢
          linear_combination -hf2
    · -- `z.re` even, `z.im` odd
      have hf : Even (z.re + z.im + 1) := (ha.add_odd hb).add_odd odd_one
      rcases even_cast_zmod4 (z.re + z.im + 1) hf with hf0 | hf2
      · refine ⟨(⟨0, 1⟩ : GaussianInt) * z, associated_of_isUnit_mul_left (z := z) isUnit_sqrtd,
          ?_, ?_, ?_⟩
        · rw [show ((⟨0, 1⟩ : GaussianInt) * z).re = -z.im by simp [Zsqrtd.re_mul]]
          exact hb.neg
        · rw [show ((⟨0, 1⟩ : GaussianInt) * z).im = z.re by simp [Zsqrtd.im_mul]]
          exact ha
        · rw [show ((⟨0, 1⟩ : GaussianInt) * z).re = -z.im by simp [Zsqrtd.re_mul],
              show ((⟨0, 1⟩ : GaussianInt) * z).im = z.re by simp [Zsqrtd.im_mul]]
          push_cast at hf0 ⊢
          linear_combination hf0
      · refine ⟨(⟨0, -1⟩ : GaussianInt) * z, associated_of_isUnit_mul_left (z := z) isUnit_neg_sqrtd,
          ?_, ?_, ?_⟩
        · rw [show ((⟨0, -1⟩ : GaussianInt) * z).re = z.im by simp [Zsqrtd.re_mul]]
          exact hb
        · rw [show ((⟨0, -1⟩ : GaussianInt) * z).im = -z.re by simp [Zsqrtd.im_mul]]
          exact ha.neg
        · rw [show ((⟨0, -1⟩ : GaussianInt) * z).re = z.im by simp [Zsqrtd.re_mul],
              show ((⟨0, -1⟩ : GaussianInt) * z).im = -z.re by simp [Zsqrtd.im_mul]]
          push_cast at hf2 ⊢
          linear_combination -hf2
  refine ⟨w0, hw0, fun y hy => ?_⟩
  obtain ⟨hyaz, hyre, hye, hyc⟩ := hy
  obtain ⟨hwaz, hwre, hwe, hwc⟩ := hw0
  obtain ⟨u, hu⟩ : ∃ u : GaussianIntˣ, y * ↑u = w0 := hyaz.trans hwaz.symm
  have hu1 : (↑u : GaussianInt) = 1 :=
    unit_eq_one_of_primary hyre hye hyc (by rw [hu]; exact hwre) (by rw [hu]; exact hwc)
  rw [hu1, mul_one] at hu
  exact hu

end Commons.NumberTheory.GaussianInt
