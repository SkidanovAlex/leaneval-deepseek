import Mathlib
import Submission.Work.FIArea3.BoxDefs

namespace Work.FIArea3.JointCount

/-- The **content** `gcd(|Im(z̄w)|, |Re(z̄w)|)` of `z̄w` divides `|w|²`, provided `z` has
content one (`gcd(|Re z|, |Im z|) = 1`).

Writing `z = a + bi`, `w = c + di` one has `Re(z̄w) = ac + bd` and `Im(z̄w) = ad - bc`; if
`g = gcd(|ad-bc|, |ac+bd|)` then `g ∣ a(c²+d²)` and `g ∣ b(c²+d²)` (the identities
`a(c²+d²) = d·Im(z̄w) + c·Re(z̄w)` and `b(c²+d²) = d·Re(z̄w) - c·Im(z̄w)`), and Bézout for
`gcd(a,b) = 1` finishes. -/
lemma content_dvd_gnorm (z w : GaussianInt) (hcop : Nat.Coprime z.re.natAbs z.im.natAbs) :
    Nat.gcd (star z * w).im.natAbs (star z * w).re.natAbs ∣ Work.FIPlan.gnorm w := by
  -- Bézout data for the coprimality of the two components of `z`
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * z.re + v * z.im = 1 := by
    have h2 : IsCoprime (z.re.natAbs : ℤ) (z.im.natAbs : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr hcop
    rw [Int.natCast_natAbs, Int.natCast_natAbs] at h2
    exact (IsCoprime.abs_abs_iff _ _).mp h2
  have him : (star z * w).im = z.re * w.im - z.im * w.re := by
    rw [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring
  have hre : (star z * w).re = z.re * w.re + z.im * w.im := by
    rw [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring
  have hnorm : w.norm = w.re * w.re + w.im * w.im := by
    rw [Zsqrtd.norm_def]; ring
  set S := w.re * w.re + w.im * w.im with hS
  set g := Nat.gcd (star z * w).im.natAbs (star z * w).re.natAbs with hg
  have hgX : (g : ℤ) ∣ (star z * w).im := by
    have h1 : (g : ℤ) ∣ ((star z * w).im.natAbs : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
    exact h1.trans (Int.natAbs_dvd.mpr dvd_rfl)
  have hgY : (g : ℤ) ∣ (star z * w).re := by
    have h1 : (g : ℤ) ∣ ((star z * w).re.natAbs : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
    exact h1.trans (Int.natAbs_dvd.mpr dvd_rfl)
  have hkey1 : (g : ℤ) ∣ z.re * S := by
    have heq : w.im * (star z * w).im + w.re * (star z * w).re = z.re * S := by
      rw [him, hre, hS]; ring
    exact heq ▸ dvd_add (hgX.mul_left w.im) (hgY.mul_left w.re)
  have hkey2 : (g : ℤ) ∣ z.im * S := by
    have heq : w.im * (star z * w).re - w.re * (star z * w).im = z.im * S := by
      rw [him, hre, hS]; ring
    exact heq ▸ dvd_sub (hgY.mul_left w.im) (hgX.mul_left w.re)
  have hfin : (g : ℤ) ∣ w.norm := by
    rw [hnorm]
    have hcomb : u * (z.re * S) + v * (z.im * S) = S := by
      linear_combination S * huv
    rw [← hcomb]
    exact dvd_add (hkey1.mul_left u) (hkey2.mul_left v)
  rw [Work.FIPlan.gnorm]
  have h2 : (g : ℤ) ∣ (w.norm.natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    exact (dvd_abs (g : ℤ) w.norm).mpr hfin
  exact Int.natCast_dvd_natCast.mp h2

end Work.FIArea3.JointCount
