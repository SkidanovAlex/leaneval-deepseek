import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.jksym_mul_rule

namespace Work.FIArea7

attribute [local instance] Classical.propDecidable

open Finset

noncomputable section

/-- A primary Gaussian integer is nonzero, hence its real part is nonzero. -/
lemma primary_re_ne_zero {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) : z.re ≠ 0 := by
  obtain ⟨hzodd, _, _⟩ := hz
  obtain ⟨k, hk⟩ := hzodd
  omega

/-- **Vanishing of the Jacobi–Kubota symbol at a non-primitive argument**: if `z` is primary but
`(z.re, z.im) ≠ 1`, then `[z] = 0`.  Indeed `[z]` is `i^{(r-1)/2}` times the Jacobi symbol
`(s | |r|)`, and `gcd(s, |r|) = gcd(r,s) > 1` with `|r| ≠ 0`. -/
lemma JKSym_eq_zero_of_not_isCoprime_primary {z : GaussianInt}
    (hz : Work.FIPlan.IsPrimary z) (hnc : ¬ IsCoprime z.re z.im) : JKSym z = 0 := by
  have hzre0 : z.re ≠ 0 := primary_re_ne_zero hz
  have hzd : Int.gcd z.re z.im ≠ 1 := fun h => hnc (Int.isCoprime_iff_gcd_eq_one.mpr h)
  have hb : z.re.natAbs ≠ 0 := fun h => hzre0 (Int.natAbs_eq_zero.mp h)
  have hgcd : z.im.gcd (↑(z.re.natAbs) : ℤ) ≠ 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.gcd_comm]
    rwa [Int.gcd_eq_natAbs] at hzd
  have hjs : jacobiSym z.im z.re.natAbs = 0 := by
    rw [jacobiSym.eq_zero_iff]
    exact ⟨hb, hgcd⟩
  rw [JKSym, JKCoeff, hjs]
  simp

/-- **Vanishing of the Jacobi–Kubota symbol at a non-primitive multiple**: if `z` is primary with
`(z.re, z.im) ≠ 1` and `w` is primary, then `[wz] = 0`.

Indeed `d = gcd(z.re, z.im) ≥ 2` divides `z.re` and `z.im`, hence divides both coordinates of
`wz`; since `(wz).re = w.re·z.re − w.im·z.im` is odd (hence nonzero), `d` divides
`gcd((wz).im, |(wz).re|) > 1`, so the Jacobi symbol `((wz).im | |(wz).re|)` vanishes. -/
lemma JKSym_mul_eq_zero_of_not_isCoprime_primary {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hz : Work.FIPlan.IsPrimary z)
    (hnc : ¬ IsCoprime z.re z.im) : JKSym (w * z) = 0 := by
  obtain ⟨hzodd, hzeven, hz4⟩ := hz
  obtain ⟨hwodd, hweven, _⟩ := hw
  have hzre0 : z.re ≠ 0 := primary_re_ne_zero ⟨hzodd, hzeven, hz4⟩
  have hzd : Int.gcd z.re z.im ≠ 1 := fun h => hnc (Int.isCoprime_iff_gcd_eq_one.mpr h)
  have hd0 : Int.gcd z.re z.im ≠ 0 := by
    intro h
    have hh := Int.gcd_dvd_left z.re z.im
    rw [h] at hh
    obtain ⟨k, hk⟩ := hh
    exact hzre0 (by simpa using hk)
  have hd2 : 2 ≤ Int.gcd z.re z.im := by omega
  have hd_zre : (↑(Int.gcd z.re z.im) : ℤ) ∣ z.re := Int.gcd_dvd_left z.re z.im
  have hd_zim : (↑(Int.gcd z.re z.im) : ℤ) ∣ z.im := Int.gcd_dvd_right z.re z.im
  have hodd : Odd ((w * z).re) := by
    rw [re_mul]
    exact (hwodd.mul hzodd).sub_even (hweven.mul_right z.im)
  have hreb : (w * z).re.natAbs ≠ 0 := by
    intro h
    have h0 : (w * z).re = 0 := Int.natAbs_eq_zero.mp h
    rw [h0] at hodd
    exact (Int.not_even_iff_odd.mpr hodd) ⟨0, by norm_num⟩
  have hd_re : (↑(Int.gcd z.re z.im) : ℤ) ∣ (w * z).re := by
    rw [re_mul]
    exact dvd_sub (dvd_mul_of_dvd_right hd_zre w.re) (dvd_mul_of_dvd_right hd_zim w.im)
  have hd_im : (↑(Int.gcd z.re z.im) : ℤ) ∣ (w * z).im := by
    rw [im_mul]
    exact dvd_add (dvd_mul_of_dvd_right hd_zim w.re) (dvd_mul_of_dvd_right hd_zre w.im)
  have h2 : (↑(Int.gcd z.re z.im) : ℤ) ∣ ↑((w * z).re.natAbs) :=
    (Int.dvd_natAbs (a := (↑(Int.gcd z.re z.im) : ℤ)) (b := (w * z).re)).mpr hd_re
  have hddvd : Int.gcd z.re z.im ∣ Int.gcd (w * z).im (↑((w * z).re.natAbs) : ℤ) :=
    Int.dvd_gcd hd_im h2
  have hgd : Int.gcd (w * z).im (↑((w * z).re.natAbs) : ℤ) ≠ 1 := by
    intro h
    have h1 : Int.gcd z.re z.im ∣ 1 := h ▸ hddvd
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hjs : jacobiSym (w * z).im (w * z).re.natAbs = 0 := by
    rw [jacobiSym.eq_zero_iff]
    exact ⟨hreb, hgd⟩
  rw [JKSym, JKCoeff, hjs]
  simp

/-- **Lemma 20.1 (*FI* (20.3)/(20.4)) for an arbitrary primary `z`** — the multiplier rule

  `[wz] = ε(w,z)·[w]·[z]·(z/w)`,

stated without the primitivity hypothesis on `z` (which `Work.FIArea7.jksym_mul_rule` assumes and
which *FI* §22 needs to drop, since its sum `Σ∧_{z ∈ B} ψ(z)[wz]` runs over all primary `z`).
In the non-primitive case `z` (i.e. `¬ IsCoprime z.re z.im`) both sides vanish: the left because
`JKSym (w*z) = 0` whenever `z` is non-primitive, the right because
`[z] = i^((r-1)/2)·(s | |r|)` vanishes as well.  So the claim follows from
`Work.FIArea7.jksym_mul_rule` by a case split (and each side is `0` in the second case). -/
theorem jksym_mul_rule_primary {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hcop : IsCoprime w.re w.im)
    (hz : Work.FIPlan.IsPrimary z) :
    Work.FIArea7.JKSym (w * z)
      = (Work.FIArea7.MultEps w z : ℂ) * Work.FIArea7.JKSym w * Work.FIArea7.JKSym z
        * (Work.FIArea7.DirichletSym w z : ℂ) := by
  by_cases hzc : IsCoprime z.re z.im
  · obtain ⟨ho, he, _⟩ := hz
    exact jksym_mul_rule hw ⟨ho, he⟩ hcop hzc
  · rw [JKSym_mul_eq_zero_of_not_isCoprime_primary hw hz hzc,
      JKSym_eq_zero_of_not_isCoprime_primary hz hzc]
    ring

end

end Work.FIArea7
