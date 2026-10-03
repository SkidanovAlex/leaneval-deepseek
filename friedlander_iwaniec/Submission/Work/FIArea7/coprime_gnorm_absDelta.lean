import Mathlib
import Submission.Work.FIArea7.jacobiSym_reflection_mod4

namespace Work.FIArea7

open Work.FIPlan

/-!
# `N(z₁)` and `Δ(z₁,z₂)` are coprime for primary, squarefree-norm, coprime `z₁, z₂`

This is the elementary coprimality that makes the Jacobi symbols of the paper's §17 (`χ_d(z₂/z₁)`,
`(·/d)` with `4d ∣ Δ`) well defined: for `z₁, z₂` primary, of squarefree norm and Gaussian-coprime,
the norm `|z₁|²` and `|Δ(z₁,z₂)| = |Im(z̄₁z₂)|` share no prime factor.

The argument is Bézout plus the multiplicativity of the norm, with no unique factorisation input:

* if a prime `p` divides both `|z₁|²` and `Δ(z₁,z₂)`, then writing `q = z̄₁z₂` we have
  `p ∣ q.re` and `p ∣ q.im` (from `(|z₁|²|z₂|² : ℤ) = q.re² + q.im²`), hence `p ∣ q` in `ℤ[i]`,
  and `p ∣ |z₁|² = gnorm z₁` gives `p ∣ z₁z̄₁`;
* `IsCoprime z₁ z₂` gives `a z₁ + b z₂ = 1`, and multiplying by `z̄₁` gives
  `z̄₁ = a(z₁z̄₁) + b q`, both terms divisible by `p`, so `p ∣ z̄₁`;
* then `p² ∣ gnorm z̄₁ = gnorm z₁`, contradicting squarefreeness of `gnorm z₁`.
-/

/-- Conjugation preserves the norm. -/
private lemma gnorm_star_eq (z : GaussianInt) : gnorm (star z) = gnorm z := by
  simp only [gnorm, Zsqrtd.norm_conj]

/-- `z * z̄ = |z|²` as a Gaussian integer. -/
private lemma mul_star_eq_gnorm (z : GaussianInt) : z * star z = (gnorm z : GaussianInt) := by
  have hnn : 0 ≤ Zsqrtd.norm z := Zsqrtd.norm_nonneg (by norm_num) z
  have hcast : (gnorm z : ℤ) = Zsqrtd.norm z := by
    rw [gnorm, Int.natAbs_of_nonneg hnn]
  have h2 : (gnorm z : GaussianInt) = ((gnorm z : ℤ) : GaussianInt) := by push_cast; ring
  rw [h2, hcast]
  exact (Zsqrtd.norm_eq_mul_conj z).symm

/-- The norm of the integer `p` viewed in `ℤ[i]` is `p²`. -/
private lemma gnorm_natCast (p : ℕ) : gnorm ((p : GaussianInt)) = p ^ 2 := by
  have h : (p : GaussianInt) = ((p : ℤ) : GaussianInt) := by push_cast; ring
  rw [h, gnorm_intCast']; simp

private lemma natCast_re (p : ℕ) : ((p : GaussianInt)).re = (p : ℤ) := by
  have h : (p : GaussianInt) = ((p : ℤ) : GaussianInt) := by push_cast; ring
  rw [h]; exact Zsqrtd.re_intCast _

private lemma natCast_im (p : ℕ) : ((p : GaussianInt)).im = 0 := by
  have h : (p : GaussianInt) = ((p : ℤ) : GaussianInt) := by push_cast; ring
  rw [h]; exact Zsqrtd.im_intCast _

/-- An integer prime `p` divides the product `z z̄` as a Gaussian integer as soon as it divides the
norm `gnorm z`. -/
private lemma intCast_dvd_of_dvd_gnorm {p : ℕ} {z : GaussianInt} (h : p ∣ gnorm z) :
    (p : GaussianInt) ∣ z * star z := by
  rw [mul_star_eq_gnorm]
  exact Nat.cast_dvd_cast h

/-- If `p` divides both coordinates of `q : ℤ[i]`, then `p ∣ q` in `ℤ[i]`. -/
private lemma intCast_dvd_of_coords {p : ℕ} {q : GaussianInt}
    (hre : p ∣ q.re.natAbs) (him : p ∣ q.im.natAbs) : (p : GaussianInt) ∣ q := by
  obtain ⟨r, hr⟩ := (Int.natCast_dvd).mpr hre
  obtain ⟨s, hs⟩ := (Int.natCast_dvd).mpr him
  refine ⟨⟨r, s⟩, ?_⟩
  apply Zsqrtd.ext
  · simp only [Zsqrtd.re_mul, natCast_re, natCast_im]
    rw [hr]; ring
  · simp only [Zsqrtd.im_mul, natCast_re, natCast_im]
    rw [hs]; ring

theorem coprime_gnorm_absDelta {z1 z2 : GaussianInt}
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2) (hD : 0 < Work.FIPlan.absDelta z1 z2) :
    Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) := by
  have _ := hP1
  have _ := hP2
  have _ := hs2
  have _ := hD
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hp1 : p ∣ gnorm z1 := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpD : p ∣ absDelta z1 z2 := hpd.trans (Nat.gcd_dvd_right _ _)
  set q : GaussianInt := star z1 * z2 with hq
  have hqim : Work.FIPlan.absDelta z1 z2 = q.im.natAbs := by
    rw [Work.FIPlan.absDelta, Work.FIPlan.Delta, hq]
  have hpim : p ∣ q.im.natAbs := by rw [← hqim]; exact hpD
  have hgnq : gnorm q = gnorm z1 * gnorm z2 := by rw [hq, gnorm_mul', gnorm_star_eq]
  have hpq : p ∣ gnorm q := by rw [hgnq]; exact dvd_mul_of_dvd_left hp1 _
  have hcoords : gnorm q = q.re.natAbs ^ 2 + q.im.natAbs ^ 2 := gnorm_coords' q
  have hsum : p ∣ q.re.natAbs ^ 2 + q.im.natAbs ^ 2 := by rw [← hcoords]; exact hpq
  have him2 : p ∣ q.im.natAbs ^ 2 := by rw [pow_two]; exact dvd_mul_of_dvd_left hpim _
  have hpre2 : p ∣ q.re.natAbs ^ 2 := (Nat.dvd_add_iff_left him2).mpr hsum
  have hpre : p ∣ q.re.natAbs := hp.dvd_of_dvd_pow hpre2
  have hpq2 : (p : GaussianInt) ∣ q := intCast_dvd_of_coords hpre hpim
  obtain ⟨a, b, hab⟩ := hc
  have hbez : star z1 = a * (z1 * star z1) + b * q := by
    calc star z1 = star z1 * 1 := (mul_one _).symm
      _ = star z1 * (a * z1 + b * z2) := by rw [← hab]
      _ = a * (z1 * star z1) + b * (star z1 * z2) := by ring
      _ = a * (z1 * star z1) + b * q := by rw [hq]
  have hpz1 : (p : GaussianInt) ∣ z1 * star z1 := intCast_dvd_of_dvd_gnorm hp1
  have hpstar : (p : GaussianInt) ∣ star z1 := by
    rw [hbez]
    exact dvd_add (dvd_mul_of_dvd_right hpz1 a) (dvd_mul_of_dvd_right hpq2 b)
  have hsq : p * p ∣ gnorm z1 := by
    obtain ⟨w, hw⟩ := hpstar
    refine ⟨gnorm w, ?_⟩
    have e : gnorm z1 = gnorm (star z1) := (gnorm_star_eq z1).symm
    rw [e, hw, gnorm_mul', gnorm_natCast]
    ring
  exact (Nat.squarefree_iff_prime_squarefree.mp hs1 p hp) hsq

end Work.FIArea7
