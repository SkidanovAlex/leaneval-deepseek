import Mathlib
import Submission.Work.FIArea2.area2_r3

namespace Work.FIArea2

/-! ### Auxiliary facts for `isCoprime_star_of_squarefree_odd_gnorm`

The proof below is a coordinate computation in `ℤ[i] = Zsqrtd (-1)`.  Writing `z = a + bi`
(`a = z.re`, `b = z.im`, `|z|² = gnorm z = |a|² + |b|²`):

* squarefreeness of `|z|²` forces `gcd(|a|,|b|) = 1` (a common divisor `g` would satisfy
  `g² ∣ |a|² + |b|²`);
* a common divisor `c` of `z` and `z̄` divides `z + z̄ = 2a` and `z - z̄ = 2bi`, hence `2b`, and
  Bézout for `a, b` combines these into `c ∣ 2`;
* consequently `gnorm c ∣ 4` and `gnorm c ∣ gnorm z`, so `gnorm c` is an odd divisor of `4`;
* hence `gnorm c = 1`, i.e. `c` is a unit.

No common divisor of `z` and `z̄` is a non-unit; since `ℤ[i]` is a PID this is exactly
coprimality. -/

/-- `gnorm (2 : ℤ[i]) = 4`. -/
theorem gnorm_two : Work.FIPlan.gnorm (2 : GaussianInt) = 4 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]
  decide

/-- **An odd Gaussian integer of squarefree norm is primitive** (`(z, z̄) = 1`).  This is the
step by which the support of the coefficient (4.13) — `β_z ≠ 0` forces `|z|²` squarefree, and the
paper's polar box (5.14) is primary hence of odd norm — supplies the primitivity hypothesis that
*FI* (6.1)/(6.2) and Lemma 8.4 assume ("Since β(n) is supported on odd squarefree numbers we have
`(r,s) = 1`"; "the restrictions on the support of `β_z` … imply that `(z₁,z̄₁) = (z₂,z̄₂) = 1`").
It is the missing hypothesis of `Work.FIArea2.Delta_ne_zero_of_coprime`.
Proof: if `π ∣ z` and `π ∣ z̄` then `π ∣ z` and `π̄ ∣ z` (conjugate the second divisibility); for a
non-ramified prime (`π ∤ π̄`) coprimality gives `ππ̄ = N(π) ∣ z`, hence `N(π)² ∣ gnorm z`, against
squarefreeness; the only ramified prime of `ℤ[i]` is `(1+i)`, whose divisibility is equivalent to
`2 ∣ gnorm z`, excluded by oddness. -/
theorem isCoprime_star_of_squarefree_odd_gnorm {z : GaussianInt}
    (h : Squarefree (Work.FIPlan.gnorm z)) (hodd : Odd (Work.FIPlan.gnorm z)) :
    IsCoprime z (star z) := by
  classical
  -- `gnorm z = a² + b²` with `a = z.re`, `b = z.im`.
  have hgn : Work.FIPlan.gnorm z = z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs :=
    GaussianInt.natAbs_norm_eq z
  -- Squarefreeness forces `gcd a b = 1`.
  have hg : z.re.natAbs.gcd z.im.natAbs = 1 := by
    have hdvd : z.re.natAbs.gcd z.im.natAbs * z.re.natAbs.gcd z.im.natAbs ∣
        Work.FIPlan.gnorm z := by
      rw [hgn]
      exact dvd_add (mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
        (mul_dvd_mul (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
    exact Nat.isUnit_iff.mp (h _ hdvd)
  have hgcd : z.re.gcd z.im = 1 := hg
  -- Bézout for the coordinates.
  have hbez : (z.re : ℤ) * (z.re.gcdA z.im) + (z.im : ℤ) * (z.re.gcdB z.im) = 1 := by
    have hh := Int.gcd_eq_gcd_ab z.re z.im
    rw [hgcd] at hh
    simpa using hh.symm
  have hJneg : (⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt) * (-(⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt)) = 1 := by
    decide
  have hI : IsUnit (⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt) :=
    Zsqrtd.norm_eq_one_iff.mp (by decide)
  -- A common divisor of `z` and `z̄` divides `2`.
  have hkey : ∀ c : GaussianInt, c ∣ z → c ∣ star z → c ∣ (2 : GaussianInt) := by
    intro c hc hcs
    have e1 : z + star z = 2 * (z.re : GaussianInt) := by ext <;> simp <;> ring
    have e2 : z - star z = 2 * (z.im : GaussianInt) * ⟨(0:ℤ), (1:ℤ)⟩ := by
      ext <;> simp <;> ring
    have h2a : c ∣ 2 * (z.re : GaussianInt) := by
      have hh : c ∣ z + star z := dvd_add hc hcs
      rwa [e1] at hh
    have h2b : c ∣ 2 * (z.im : GaussianInt) := by
      have hh : c ∣ z - star z := dvd_sub hc hcs
      rw [e2] at hh
      exact (IsUnit.dvd_mul_right hI).mp hh
    have hbezG : (z.re : GaussianInt) * (z.re.gcdA z.im : GaussianInt)
        + (z.im : GaussianInt) * (z.re.gcdB z.im : GaussianInt) = 1 := by
      exact_mod_cast hbez
    have hsum : (2 : GaussianInt) = (z + star z) * (z.re.gcdA z.im : GaussianInt)
        + (z - star z) * (-(⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt))
          * (z.re.gcdB z.im : GaussianInt) := by
      have hh : (z - star z) * (-(⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt))
            * (z.re.gcdB z.im : GaussianInt)
          = 2 * (z.im : GaussianInt) * (z.re.gcdB z.im : GaussianInt) := by
        rw [e2, show (2 * (z.im : GaussianInt) * (⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt))
            * (-(⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt)) = 2 * (z.im : GaussianInt) by
          rw [mul_assoc, hJneg, mul_one]]
      calc (2 : GaussianInt)
          = 2 * ((z.re : GaussianInt) * (z.re.gcdA z.im : GaussianInt)
              + (z.im : GaussianInt) * (z.re.gcdB z.im : GaussianInt)) := by
            rw [hbezG, mul_one]
        _ = 2 * (z.re : GaussianInt) * (z.re.gcdA z.im : GaussianInt)
              + 2 * (z.im : GaussianInt) * (z.re.gcdB z.im : GaussianInt) := by ring
        _ = (z + star z) * (z.re.gcdA z.im : GaussianInt)
              + (z - star z) * (-(⟨(0:ℤ), (1:ℤ)⟩ : GaussianInt))
                * (z.re.gcdB z.im : GaussianInt) := by rw [e1, hh]
    rw [hsum]
    refine dvd_add ?_ ?_
    · rw [e1]; exact dvd_mul_of_dvd_left h2a _
    · rw [e2]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2b _) _) _
  -- Every common divisor is a unit.
  refine IsRelPrime.isCoprime (fun c hc hcs => ?_)
  have hd2 : c ∣ (2 : GaussianInt) := hkey c hc hcs
  have h4 : Work.FIPlan.gnorm c ∣ 4 := by
    obtain ⟨k, hk⟩ := hd2
    refine ⟨Work.FIPlan.gnorm k, ?_⟩
    calc (4 : ℕ) = Work.FIPlan.gnorm (2 : GaussianInt) := gnorm_two.symm
      _ = Work.FIPlan.gnorm (c * k) := by rw [hk]
      _ = Work.FIPlan.gnorm c * Work.FIPlan.gnorm k := gnorm_mul c k
  have hN : Work.FIPlan.gnorm c ∣ Work.FIPlan.gnorm z := by
    obtain ⟨k, hk⟩ := hc
    exact ⟨Work.FIPlan.gnorm k, by rw [hk, gnorm_mul]⟩
  have hodd' : Odd (Work.FIPlan.gnorm c) := by
    refine Nat.not_even_iff_odd.mp fun he => ?_
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp he).trans hN))
  have hcop : Nat.Coprime (Work.FIPlan.gnorm c) 4 := by
    have hh := (Nat.coprime_two_right.mpr hodd').pow_right 2
    simpa using hh
  have hone : Work.FIPlan.gnorm c ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd dvd_rfl h4
  exact Zsqrtd.norm_eq_one_iff.mp (Nat.dvd_one.mp hone)

end Work.FIArea2
