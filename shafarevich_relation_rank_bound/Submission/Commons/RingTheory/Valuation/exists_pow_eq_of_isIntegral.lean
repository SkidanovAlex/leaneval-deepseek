import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Extension

namespace Commons.RingTheory.Valuation

open Polynomial

/-- In a valued field, if a finite sum of nonzero elements is zero, then two summands
have the same value. (The maximal value among the summands is attained at least twice.) -/
theorem exists_ne_map_eq_of_sum_eq_zero {K Γ ι : Type*} [Field K] [DecidableEq ι]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {s : Finset ι} {f : ι → K}
    (hs : s.Nonempty) (hsum : ∑ i ∈ s, f i = 0) (hne : ∀ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ v (f i) = v (f j) := by
  by_contra h
  push Not at h
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image s (fun i => v (f i)) hs
  have hkey : v (∑ i ∈ s, f i) = v (f k) := by
    refine Valuation.map_sum_eq_of_lt v hk ?_
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hkmax i hi.1) (h i hi.1 k hk hi.2)
  rw [hsum, map_zero] at hkey
  exact hne k hk ((Valuation.zero_iff v).mp hkey.symm)

theorem exists_pow_eq_of_isIntegral {K L Γ₀ Γ₁ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (v : Valuation K Γ₀) (w : Valuation L Γ₁) [v.HasExtension w] {x : L}
    (hx : IsIntegral K x) (hx0 : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : K, w x ^ n = w (algebraMap K L a) := by
  obtain ⟨p, hpm, hpeval⟩ := hx
  have hwx0 : w x ≠ 0 := (Valuation.zero_iff w).not.mpr hx0
  have hsne : p.support.Nonempty := Polynomial.support_nonempty.mpr hpm.ne_zero
  have hsum : ∑ i ∈ p.support, algebraMap K L (p.coeff i) * x ^ i = 0 := by
    have h' := hpeval
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def] at h'
    exact h'
  have hne : ∀ i ∈ p.support, algebraMap K L (p.coeff i) * x ^ i ≠ 0 := by
    intro i hi
    refine mul_ne_zero ?_ (pow_ne_zero i hx0)
    intro h
    exact (Polynomial.mem_support_iff.mp hi)
      ((algebraMap K L).injective (h.trans (map_zero (algebraMap K L)).symm))
  obtain ⟨i, hi, j, hj, hij, heq⟩ := exists_ne_map_eq_of_sum_eq_zero w hsne hsum hne
  have heq' : w (algebraMap K L (p.coeff i)) * w x ^ i
      = w (algebraMap K L (p.coeff j)) * w x ^ j := by
    simpa only [Valuation.map_mul, Valuation.map_pow] using heq
  have hAi : algebraMap K L (p.coeff i) ≠ 0 := fun h =>
    (Polynomial.mem_support_iff.mp hi)
      ((algebraMap K L).injective (h.trans (map_zero (algebraMap K L)).symm))
  have hAj : algebraMap K L (p.coeff j) ≠ 0 := fun h =>
    (Polynomial.mem_support_iff.mp hj)
      ((algebraMap K L).injective (h.trans (map_zero (algebraMap K L)).symm))
  have hvi : w (algebraMap K L (p.coeff i)) ≠ 0 := (Valuation.zero_iff w).not.mpr hAi
  have hvj : w (algebraMap K L (p.coeff j)) ≠ 0 := (Valuation.zero_iff w).not.mpr hAj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hpw : w x ^ j = w x ^ i * w x ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    have hstep : w (algebraMap K L (p.coeff i)) * w x ^ i
        = w (algebraMap K L (p.coeff j)) * (w x ^ i * w x ^ (j - i)) := by
      rw [heq', hpw]
    have h1 : w (algebraMap K L (p.coeff i))
        = w (algebraMap K L (p.coeff j)) * w x ^ (j - i) :=
      mul_right_cancel₀ (pow_ne_zero i hwx0) (by rw [hstep]; ac_rfl)
    refine ⟨j - i, Nat.sub_pos_of_lt hlt, p.coeff i / p.coeff j, ?_⟩
    rw [map_div₀ (algebraMap K L), Valuation.map_div w, div_eq_mul_inv, mul_comm]
    rw [h1, inv_mul_cancel_left₀ hvj]
  · have hpw : w x ^ i = w x ^ j * w x ^ (i - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    have hstep : w (algebraMap K L (p.coeff j)) * w x ^ j
        = (w (algebraMap K L (p.coeff i)) * w x ^ (i - j)) * w x ^ j := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le, ← heq']
    have h1 : w (algebraMap K L (p.coeff j))
        = w (algebraMap K L (p.coeff i)) * w x ^ (i - j) :=
      mul_right_cancel₀ (pow_ne_zero j hwx0) hstep
    refine ⟨i - j, Nat.sub_pos_of_lt hlt, p.coeff j / p.coeff i, ?_⟩
    rw [map_div₀ (algebraMap K L), Valuation.map_div w, div_eq_mul_inv, mul_comm]
    rw [h1, inv_mul_cancel_left₀ hvi]

end Commons.RingTheory.Valuation