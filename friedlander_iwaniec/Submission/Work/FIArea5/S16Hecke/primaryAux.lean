/-
# `Submission.Work.FIArea5.S16Hecke.primaryAux`

Elementary API for `Work.FIPlan.IsPrimary`, `Work.FIPlan.gnorm` and the box `Work.FIPlan.gBox`.

These are the tools used by the proof of the multiplicativity of the Hecke eigenvalue sum
`Work.FIArea5.S16Hecke.heckeEigenvalue_mul`: the primary Gaussian integers form a submonoid, a
primary element is invertible modulo `(1+i)^3` so it can be cancelled, a primary unit is `1`,
and the box `gBox R` contains every Gaussian integer of norm `≤ R` (`R ≥ 1`).
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Commons.NumberTheory.GaussianInt.units_classification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-! ## Elementary modular arithmetic -/

/-- An odd integer reduces to `1` or `3` modulo `4`. -/
theorem odd_cast_four {n : ℤ} (h : Odd n) : (n : ZMod 4) = 1 ∨ (n : ZMod 4) = 3 := by
  obtain ⟨k, rfl⟩ := h
  have hk : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  push_cast
  rcases hk (k : ZMod 4) with h | h | h | h <;> rw [h] <;> decide

/-! ## The multiplicative structure of `IsPrimary` and `gnorm` -/

/-- `gnorm z = |z|²` is multiplicative. -/
theorem gnorm_mul (z w : GaussianInt) : gnorm (z * w) = gnorm z * gnorm w := by
  simp only [gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `gnorm 1 = 1`. -/
theorem gnorm_one : gnorm (1 : GaussianInt) = 1 := by
  simp only [gnorm, Zsqrtd.norm_def]
  norm_num

/-- `1` is primary. -/
theorem isPrimary_one : IsPrimary (1 : GaussianInt) :=
  ⟨odd_one, ⟨0, by norm_num⟩, by decide⟩

/-- **The primary elements form a submonoid**: `z ≡ w ≡ 1 (mod (1+i)^3)` implies
`zw ≡ 1 (mod (1+i)^3)`.

The arithmetic core: for `z = a+bi`, `w = c+di` with `a, c` odd, `b ≡ a-1`, `d ≡ c-1` (mod 4),
the product coordinates `ac-bd`, `ad+bc` again satisfy the primary conditions. -/
theorem isPrimary_mul {z w : GaussianInt} (hz : IsPrimary z) (hw : IsPrimary w) :
    IsPrimary (z * w) := by
  obtain ⟨hzo, hze, hzc⟩ := hz
  obtain ⟨hwo, hwe, hwc⟩ := hw
  have hre : (z * w).re = z.re * w.re - z.im * w.im := by rw [Zsqrtd.re_mul]; ring
  have him : (z * w).im = z.re * w.im + z.im * w.re := by rw [Zsqrtd.im_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]
    exact (hzo.mul hwo).sub_even (hze.mul_right w.im)
  · rw [him]
    exact (hwe.mul_left z.re).add (hze.mul_right w.re)
  · rw [him, hre]
    have L1 : z.re * w.im ≡ z.re * (w.re - 1) [ZMOD 4] := Int.ModEq.mul_left z.re hwc
    have L2 : z.im * w.re ≡ (z.re - 1) * w.re [ZMOD 4] := Int.ModEq.mul_right w.re hzc
    have hmid : z.re * (w.re - 1) + (z.re - 1) * w.re
        ≡ (z.re * w.re - (z.re - 1) * (w.re - 1)) - 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hzo
      obtain ⟨l, hl⟩ := hwo
      use -2 * k * l
      rw [hk, hl]; ring
    have hR : z.re * w.re - z.im * w.im - 1
        ≡ z.re * w.re - (z.re - 1) * (w.re - 1) - 1 [ZMOD 4] :=
      ((Int.ModEq.refl (z.re * w.re)).sub (Int.ModEq.mul hzc hwc)).sub (Int.ModEq.refl 1)
    exact (L1.add L2).trans (hmid.trans hR.symm)

/-- A primary Gaussian integer has odd norm: `z.re` is odd and `z.im` is even, so
`|z|² = z.re² + z.im²` is odd. -/
theorem isPrimary_odd_gnorm {z : GaussianInt} (hz : IsPrimary z) : Odd (gnorm z) := by
  obtain ⟨ho, he, _⟩ := hz
  have hnorm : (z.norm : ℤ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Zsqrtd.norm_def]; ring
  rw [gnorm, Int.natAbs_odd, hnorm]
  exact (ho.pow).add_even (by rw [pow_two]; exact he.mul_right z.im)

/-! ## Cancelling a primary factor -/

/-- The `ZMod 4` core of the cancellation lemma: if `u` is odd, `v = u - 1`, `e` is odd,
`f` is even and `u * f + v * e = u * e - v * f - 1`, then `f = e - 1`. -/
theorem zmod4_primary_cancel : ∀ u v e f : ZMod 4, (u = 1 ∨ u = 3) → v = u - 1 →
    (e = 1 ∨ e = 3) → (f = 0 ∨ f = 2) → u * f + v * e = u * e - v * f - 1 → f = e - 1 := by
  decide

/-- **A primary element can be cancelled**: if `a` and `a * b` are both primary then so is `b`.
(`a ≡ 1 (mod (1+i)^3)` is a unit of `ℤ[i]/(1+i)^3`, so `b ≡ 1` there as well.) -/
theorem isPrimary_of_isPrimary_mul_right {a b : GaussianInt} (ha : IsPrimary a)
    (hab : IsPrimary (a * b)) : IsPrimary b := by
  obtain ⟨hao, hae, hac⟩ := ha
  obtain ⟨habo, habe, habc⟩ := hab
  have hre : (a * b).re = a.re * b.re - a.im * b.im := by rw [Zsqrtd.re_mul]; ring
  have him : (a * b).im = a.re * b.im + a.im * b.re := by rw [Zsqrtd.im_mul]
  -- parities of `b.re` and `b.im`
  have hbre : Odd b.re := by
    have h1 : Odd (a.re * b.re) := by
      have h := habo.add_even (hae.mul_right b.im)
      rw [hre] at h
      have heq : a.re * b.re - a.im * b.im + a.im * b.im = a.re * b.re := by ring
      rwa [heq] at h
    exact (Int.odd_mul.mp h1).2
  have hbim : Even b.im := by
    have h2 : Even (a.re * b.im) := by
      have h := habe.sub (hae.mul_left b.re)
      rw [him] at h
      have heq : a.re * b.im + a.im * b.re - b.re * a.im = a.re * b.im := by ring
      rwa [heq] at h
    exact (Int.even_mul.mp h2).resolve_left (Int.not_even_iff_odd.mpr hao)
  refine ⟨hbre, hbim, ?_⟩
  have hv : ((a.im : ℤ) : ZMod 4) = ((a.re : ℤ) : ZMod 4) - 1 := by
    have := (ZMod.intCast_eq_intCast_iff a.im (a.re - 1) 4).mpr hac
    push_cast at this ⊢
    exact this
  have hh : ((a.re : ℤ) : ZMod 4) * ((b.im : ℤ) : ZMod 4)
        + ((a.im : ℤ) : ZMod 4) * ((b.re : ℤ) : ZMod 4)
      = ((a.re : ℤ) : ZMod 4) * ((b.re : ℤ) : ZMod 4)
        - ((a.im : ℤ) : ZMod 4) * ((b.im : ℤ) : ZMod 4) - 1 := by
    have h := (ZMod.intCast_eq_intCast_iff (a * b).im ((a * b).re - 1) 4).mpr habc
    rw [him, hre] at h
    push_cast at h ⊢
    exact h
  have hkey := zmod4_primary_cancel ((a.re : ℤ) : ZMod 4) ((a.im : ℤ) : ZMod 4)
    ((b.re : ℤ) : ZMod 4) ((b.im : ℤ) : ZMod 4)
    (odd_cast_four hao) hv (odd_cast_four hbre)
    (Commons.NumberTheory.GaussianInt.even_cast_zmod4 b.im hbim) hh
  refine (ZMod.intCast_eq_intCast_iff b.im (b.re - 1) 4).mp ?_
  push_cast
  exact hkey

/-- `0` is not odd. -/
theorem not_odd_zero : ¬ Odd (0 : ℤ) := by
  rintro ⟨k, hk⟩
  omega

/-- The only primary unit is `1`. -/
theorem isPrimary_unit {u : GaussianInt} (h : IsPrimary u) (hu : IsUnit u) : u = 1 := by
  rcases (Commons.NumberTheory.GaussianInt.units_classification u).mp hu with
    h1 | h1 | h1 | h1
  · exact h1
  · exfalso
    rw [h1] at h
    have hh : ((0 : ℤ) : ZMod 4) = ((-2 : ℤ) : ZMod 4) :=
      (ZMod.intCast_eq_intCast_iff 0 (-2) 4).mpr (by simpa using h.2.2)
    exact absurd hh (by decide)
  · exfalso
    rw [h1] at h
    exact not_odd_zero (by simpa using h.1)
  · exfalso
    rw [h1] at h
    exact not_odd_zero (by simpa using h.1)

/-! ## The box `gBox` -/

/-- Membership in the box `gBox R`, in coordinates. -/
theorem mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    exact hp
  · intro h
    exact ⟨(z.re, z.im), by rw [Finset.product_eq_sprod, Finset.mem_product]; exact h,
      by ext <;> rfl⟩

/-- Every Gaussian integer of norm `≤ R` lies in the box `gBox R`, for `R ≥ 1`. -/
theorem mem_gBox_of_gnorm_le {R : ℤ} {z : GaussianInt} (hR : 0 < R)
    (h : ((gnorm z : ℕ) : ℤ) ≤ R) : z ∈ gBox R := by
  have hnorm : ((gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
    rw [gnorm, Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) z),
      Zsqrtd.norm_def]
    ring
  have hre : z.re ^ 2 ≤ ((gnorm z : ℕ) : ℤ) := by rw [hnorm]; nlinarith [sq_nonneg z.im]
  have him : z.im ^ 2 ≤ ((gnorm z : ℕ) : ℤ) := by rw [hnorm]; nlinarith [sq_nonneg z.re]
  have habs_re : |z.re| ≤ R := by
    by_cases h1 : |z.re| ≤ 1
    · omega
    · have h2 : 1 ≤ |z.re| := by omega
      nlinarith [sq_abs z.re]
  have habs_im : |z.im| ≤ R := by
    by_cases h1 : |z.im| ≤ 1
    · omega
    · have h2 : 1 ≤ |z.im| := by omega
      nlinarith [sq_abs z.im]
  rw [mem_gBox_iff, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨abs_le.mp habs_re, abs_le.mp habs_im⟩

end

end Work.FIArea5.S16Hecke
