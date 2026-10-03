import Mathlib
import Submission.Work.FIArea7.prop232Defs

namespace Work.FIArea7

/-- `|z|²` as a Gaussian integer is `z z̄`.  (Local restatement of
`Commons.NumberTheory.GaussianInt.norm_natAbs_cast_eq`, kept here so that this module needs no
extra import.) -/
private lemma cast_gnorm_eq_mul_star (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : GaussianInt) = z * star z := by
  have hx : 0 ≤ Zsqrtd.norm z := Zsqrtd.norm_nonneg (show (-1 : ℤ) ≤ 0 by norm_num) z
  have h := congrArg (fun t : ℤ => (t : GaussianInt)) (Int.natAbs_of_nonneg hx)
  simpa [Work.FIPlan.gnorm] using h.trans (Zsqrtd.norm_eq_mul_conj z)

/-- **The vanishing that lets the condition `(|z|², m) = 1` be dropped in `L∗(N)`.**  If `w, z` are
primary, `IsCoprime z w`, and a natural number `q > 1` divides both `|z|²` and `|w|²`, then the
Jacobi–Kubota symbol of the product vanishes: `[w·z] = 0`.

This is what makes *FI*'s identity `L∗(N) = Σ∧_{ww̄=m} ψ(w) Σ_{z : |z|² ≤ N, (z,w)=1} ψ(z)[wz]`
correct: with `w w̄ = m` the terms with `(|z|², m) > 1` that appear in the disc sum on the right
have `q := gcd(|z|²,|w|²) > 1` and are exactly zero.

Proof route: since `(gnorm z : ℤ[i]) = z * star z` and likewise for `w`
(`Commons.NumberTheory.GaussianInt.norm_natAbs_cast_eq`), `q` divides both `z * star z` and
`w * star w` in `ℤ[i]`.  Bezout for the coprime pair (`IsCoprime z w` is coprimality of the ideals
`(z), (w)`, so there are `a b` with `a*z + b*w = 1`) multiplied by `star z * star w` gives
`a·(z star z)·star w + b·(w star w)·star z = star z * star w`, so `q ∣ star (w*z)`, hence `q ∣ w*z`
(`q` is a rational integer: conjugate divisibility), hence `q` divides both coordinates of `w*z`.
As `w*z` is primary (use `Work.FITop3.Witness.isPrimary_mul`) it has odd real part, hence nonzero
real part, and `jacobiSym (w*z).im (w*z).re.natAbs = 0` by `jacobiSym.eq_zero_iff` (`b ≠ 0` and
`gcd (w*z).im (w*z).re ≠ 1` since `q > 1` divides both coordinates); finally
`JKSym = I^((re-1)/2) · JKCoeff` with `JKCoeff = jacobiSym im re.natAbs`. -/
theorem JKSym_mul_eq_zero {w z : GaussianInt} {q : ℕ}
    (hq : 1 < q) (hw : Work.FIPlan.IsPrimary w) (hz : Work.FIPlan.IsPrimary z)
    (hcop : IsCoprime z w) (hqz : q ∣ Work.FIPlan.gnorm z) (hqw : q ∣ Work.FIPlan.gnorm w) :
    Work.FIArea7.JKSym (w * z) = 0 := by
  -- Bezout for the coprime pair `z, w`.
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨c, hc⟩ := hqz
  obtain ⟨d, hd⟩ := hqw
  -- `q` divides `z z̄` and `w w̄` in `ℤ[i]`.
  have hqvdz : (q : GaussianInt) ∣ z * star z := by
    refine ⟨(c : GaussianInt), ?_⟩
    rw [← cast_gnorm_eq_mul_star z, hc]
    push_cast
    ring
  have hqvdw : (q : GaussianInt) ∣ w * star w := by
    refine ⟨(d : GaussianInt), ?_⟩
    rw [← cast_gnorm_eq_mul_star w, hd]
    push_cast
    ring
  -- Multiplying `a z + b w = 1` by `z̄ w̄` exhibits `w̄ z̄ = star (w z)` as a combination of
  -- `z z̄` and `w w̄`, so `q ∣ star (w z)`.
  have hkey : star (w * z) = a * (z * star z) * star w + b * (w * star w) * star z := by
    have h1 : a * (z * star z) * star w + b * (w * star w) * star z
        = (a * z + b * w) * (star z * star w) := by ring
    rw [h1, hab, one_mul]
    simp [star_mul]
  have hqvdstar : (q : GaussianInt) ∣ star (w * z) := by
    rw [hkey]
    apply dvd_add
    · simpa [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_right hqvdz (a * star w)
    · simpa [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_right hqvdw (b * star z)
  -- `q` is a rational integer, so it survives conjugation: `q ∣ w z`.
  have hqstar : star (q : GaussianInt) = (q : GaussianInt) := by simp
  have hqvdwz : (q : GaussianInt) ∣ w * z := by
    obtain ⟨u, hu⟩ := hqvdstar
    refine ⟨star u, ?_⟩
    have h2 := congrArg star hu
    simp only [star_mul, star_star] at h2
    rw [h2, hqstar, mul_comm]
  -- Hence `q` divides both coordinates of `w z`.
  obtain ⟨u, hu⟩ := hqvdwz
  have hdvd_re : (q : ℤ) ∣ (w * z).re := by
    refine ⟨u.re, ?_⟩
    rw [hu, Zsqrtd.re_mul]
    simp
  have hdvd_im : (q : ℤ) ∣ (w * z).im := by
    refine ⟨u.im, ?_⟩
    rw [hu, Zsqrtd.im_mul]
    simp
  -- `w z` is primary, hence has odd (in particular nonzero) real part.
  obtain ⟨hrw, hsw, _⟩ := hw
  obtain ⟨hrz, hsz, _⟩ := hz
  have hodd : Odd (w * z).re := by
    rw [Work.FIArea7.re_mul]
    exact (hrw.mul hrz).sub_even (hsw.mul_right z.im)
  have hre0 : (w * z).re ≠ 0 := fun h => Int.not_odd_zero (h ▸ hodd)
  -- and `gcd ((w z).im, |(w z).re|) ≥ q > 1`.
  have hdvd_im_nat : q ∣ (w * z).im.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    exact hdvd_im
  have hdvd_re_nat : q ∣ (w * z).re.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    exact hdvd_re
  have hgcd : Int.gcd (w * z).im ((w * z).re.natAbs) ≠ 1 := by
    intro h
    have h1 : q ∣ (1 : ℕ) := by
      rw [← h, Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact Nat.dvd_gcd hdvd_im_nat hdvd_re_nat
    exact absurd (Nat.eq_one_of_dvd_one h1) (by omega)
  have hzero : jacobiSym (w * z).im (w * z).re.natAbs = 0 := by
    rw [jacobiSym.eq_zero_iff]
    exact ⟨Int.natAbs_ne_zero.mpr hre0, hgcd⟩
  rw [JKSym, JKCoeff, hzero]
  simp

end Work.FIArea7
