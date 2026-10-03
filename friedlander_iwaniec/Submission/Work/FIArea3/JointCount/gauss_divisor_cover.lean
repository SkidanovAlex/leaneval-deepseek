import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea3.JointCount

/-- `z * star z` is the rational integer `gnorm z`, viewed inside `ℤ[i]`.  This is the bridge
between the norm divisibility `d ∣ gnorm z` and divisibility in the Gaussian integers. -/
lemma mul_star_eq_gnorm (z : GaussianInt) :
    z * star z = ((Work.FIPlan.gnorm z : ℕ) : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_mul_conj z, Work.FIPlan.gnorm]
  simp

/-- **Splitting a rational divisor of a norm.**  For a positive integer `d` and a Gaussian integer
`z`, one has `d ∣ |z|²` if and only if `d` can be split as a product `u · (d/u)` of a Gaussian
integer `u` dividing `z` and a Gaussian integer `d/u` dividing `star z`.

This is the arithmetic input ("the ring `ℤ[i]` is a decomposition monoid") behind the polynomial
`X² + Y⁴` capturing its primes. -/
theorem gauss_divisor_cover (d : ℕ) (hd : 1 ≤ d) (z : GaussianInt) :
    d ∣ Work.FIPlan.gnorm z ↔
      ∃ u : GaussianInt, u ∣ (d : GaussianInt) ∧
        u ∣ z ∧ ((d : GaussianInt) / u) ∣ star z := by
  have hd0 : d ≠ 0 := by omega
  have hdc : (d : GaussianInt) ≠ 0 := by exact_mod_cast hd0
  have hcast : (d : GaussianInt) = ((d : ℤ) : GaussianInt) := by simp
  have hcast2 : ∀ n : ℕ, ((n : ℕ) : GaussianInt) = ((n : ℤ) : GaussianInt) := by
    intro n; simp
  constructor
  · intro h
    -- `d ∣ gnorm z` gives `(d : ℤ[i]) ∣ z * star z`
    have hdvd : (d : GaussianInt) ∣ z * star z := by
      rw [mul_star_eq_gnorm, hcast, hcast2, Zsqrtd.intCast_dvd_intCast, Int.natCast_dvd_natCast]
      exact h
    -- split the divisor `d` of the product `z * star z` (decomposition monoid `ℤ[i]`)
    obtain ⟨u, w, huz, hwz, huw⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
    refine ⟨u, ⟨w, huw⟩, huz, ?_⟩
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [zero_mul] at huw
      exact hdc huw
    -- since `u ∣ d`, the Euclidean quotient `d / u` is exactly the complementary factor `w`
    have hw : w = (d : GaussianInt) / u := EuclideanDomain.eq_div_of_mul_eq_right hu0 huw.symm
    rw [← hw]
    exact hwz
  · rintro ⟨u, hud, huz, hwz⟩
    have hu0 : u ≠ 0 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hud
      rw [zero_mul] at hc
      exact hdc hc
    -- multiply the two divisibilities: `u · (d/u) = d` divides `z * star z`
    have hdvd : (d : GaussianInt) ∣ z * star z := by
      rw [← EuclideanDomain.mul_div_cancel' hu0 hud]
      exact mul_dvd_mul huz hwz
    rw [mul_star_eq_gnorm, hcast, hcast2, Zsqrtd.intCast_dvd_intCast, Int.natCast_dvd_natCast] at hdvd
    exact hdvd

end Work.FIArea3.JointCount
