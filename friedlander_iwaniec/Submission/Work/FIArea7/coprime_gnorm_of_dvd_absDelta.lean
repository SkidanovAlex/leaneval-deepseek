import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.coprime_gnorm_absDelta

namespace Work.FIArea7

open Work.FIPlan

/-!
# `|z₂|²` is coprime to every divisor `q` of `|Δ(z₁,z₂)|`

This is the `z₂`-analogue of `Work.FIArea7.coprime_gnorm_absDelta` (same file's sibling), needed to
justify the integrality of the Jacobi symbols `χ_d(z₂/z₁)` of the paper's §17 when `4d ∣ Δ`.

The paper's argument is elementary: Bézout plus multiplicativity of the norm, no unique
factorisation in `ℤ[i]`.

* if a prime `p` divides both `|z₂|²` and `|Δ(z₁,z₂)|`, then with `Q = z̄₂z₁ = conj(z̄₁z₂)` we have
  `p ∣ Q.im` (`Q.im = -Δ`), while `p ∣ |z₂|²` gives `p ∣ |Q|² = |z̄₂z₁|²`, hence `p ∣ Q.re²` and
  `p ∣ Q.re`, so `p ∣ Q` in `ℤ[i]`;
* `IsCoprime z₁ z₂` gives `a z₁ + b z₂ = 1`, and multiplying by `z̄₂` gives
  `z̄₂ = a(z₁z̄₂) + b(z₂z̄₂)`: both terms are divisible by `p`, so `p ∣ z̄₂`;
* then `p² ∣ |z̄₂|² = |z₂|²`, contradicting squarefreeness of `|z₂|²`.

The primary hypotheses are not needed for this coprimality, and neither is `Δ ≠ 0`: the argument
goes through verbatim when `Δ = 0` (then `p ∣ 0` is automatic and still yields `p² ∣ |z₂|²`).
-/

/-! ## Local norm bookkeeping

Copies (with fresh names) of the private helpers of `coprime_gnorm_absDelta`, so that this module is
self-contained. -/

/-- Conjugation preserves the norm. -/
private lemma gnorm_star_eqB (z : GaussianInt) : gnorm (star z) = gnorm z := by
  simp only [gnorm, Zsqrtd.norm_conj]

/-- `z * z̄ = |z|²` as a Gaussian integer. -/
private lemma mul_star_eq_gnormB (z : GaussianInt) : z * star z = (gnorm z : GaussianInt) := by
  have hnn : 0 ≤ Zsqrtd.norm z := Zsqrtd.norm_nonneg (by norm_num) z
  have hcast : (gnorm z : ℤ) = Zsqrtd.norm z := by
    rw [gnorm, Int.natAbs_of_nonneg hnn]
  have h2 : (gnorm z : GaussianInt) = ((gnorm z : ℤ) : GaussianInt) := by push_cast; ring
  rw [h2, hcast]
  exact (Zsqrtd.norm_eq_mul_conj z).symm

/-- The norm of the integer `p` viewed in `ℤ[i]` is `p²`. -/
private lemma gnorm_natCastB (p : ℕ) : gnorm ((p : GaussianInt)) = p ^ 2 := by
  have h : (p : GaussianInt) = ((p : ℤ) : GaussianInt) := by push_cast; ring
  rw [h, gnorm_intCast']; simp

private lemma natCast_reB (p : ℕ) : ((p : GaussianInt)).re = (p : ℤ) := by
  have h : (p : GaussianInt) = ((p : ℤ) : GaussianInt) := by push_cast; ring
  rw [h]; exact Zsqrtd.re_intCast _

private lemma natCast_imB (p : ℕ) : ((p : GaussianInt)).im = 0 := by
  have h : (p : GaussianInt) = ((p : ℤ) : GaussianInt) := by push_cast; ring
  rw [h]; exact Zsqrtd.im_intCast _

/-- An integer prime `p` divides `z z̄` in `ℤ[i]` as soon as it divides the norm `gnorm z`. -/
private lemma intCast_dvd_of_dvd_gnormB {p : ℕ} {z : GaussianInt} (h : p ∣ gnorm z) :
    (p : GaussianInt) ∣ z * star z := by
  rw [mul_star_eq_gnormB]
  exact Nat.cast_dvd_cast h

/-- If `p` divides both coordinates of `Q : ℤ[i]`, then `p ∣ Q` in `ℤ[i]`. -/
private lemma intCast_dvd_of_coordsB {p : ℕ} {Q : GaussianInt}
    (hre : p ∣ Q.re.natAbs) (him : p ∣ Q.im.natAbs) : (p : GaussianInt) ∣ Q := by
  obtain ⟨r, hr⟩ := (Int.natCast_dvd).mpr hre
  obtain ⟨s, hs⟩ := (Int.natCast_dvd).mpr him
  refine ⟨⟨r, s⟩, ?_⟩
  apply Zsqrtd.ext
  · simp only [Zsqrtd.re_mul, natCast_reB, natCast_imB]
    rw [hr]; ring
  · simp only [Zsqrtd.im_mul, natCast_reB, natCast_imB]
    rw [hs]; ring

theorem coprime_gnorm_of_dvd_absDelta {z1 z2 : GaussianInt} {q : ℕ} (hq0 : 0 < q)
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2) (hq : q ∣ Work.FIPlan.absDelta z1 z2) :
    Nat.Coprime (Work.FIPlan.gnorm z2) q := by
  have _ := hP1
  have _ := hP2
  have _ := hs1
  have _ := hq0
  -- It suffices to prove coprimality of `gnorm z2` with the whole of `|Δ(z₁,z₂)|`.
  have hmain : Nat.Coprime (gnorm z2) (absDelta z1 z2) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p ∣ gnorm z2 := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpD : p ∣ absDelta z1 z2 := hpd.trans (Nat.gcd_dvd_right _ _)
    -- `Q = z̄₂z₁ = conj(z̄₁z₂)`, so `Q.im = -Δ(z₁,z₂)`.
    set Q : GaussianInt := star z2 * z1 with hQ
    have hQstar : star (star z1 * z2) = Q := by
      rw [hQ, star_mul, star_star]
    have hQim : absDelta z1 z2 = Q.im.natAbs := by
      rw [absDelta, Delta, ← hQstar, Zsqrtd.im_star, Int.natAbs_neg]
    have hpim : p ∣ Q.im.natAbs := by rw [← hQim]; exact hpD
    have hgnQ : gnorm Q = gnorm z1 * gnorm z2 := by
      rw [hQ, gnorm_mul', gnorm_star_eqB]; ring
    have hpnQ : p ∣ gnorm Q := by rw [hgnQ]; exact dvd_mul_of_dvd_right hp2 _
    have hcoords : gnorm Q = Q.re.natAbs ^ 2 + Q.im.natAbs ^ 2 := gnorm_coords' Q
    have hsum : p ∣ Q.re.natAbs ^ 2 + Q.im.natAbs ^ 2 := by rw [← hcoords]; exact hpnQ
    have him2 : p ∣ Q.im.natAbs ^ 2 := by rw [pow_two]; exact dvd_mul_of_dvd_left hpim _
    have hre2 : p ∣ Q.re.natAbs ^ 2 := (Nat.dvd_add_iff_left him2).mpr hsum
    have hre : p ∣ Q.re.natAbs := hp.dvd_of_dvd_pow hre2
    have hpQ : (p : GaussianInt) ∣ Q := intCast_dvd_of_coordsB hre hpim
    -- Bézout, multiplied by `z̄₂`.
    obtain ⟨a, b, hab⟩ := hc
    have hbez : star z2 = a * (z1 * star z2) + b * (z2 * star z2) := by
      calc star z2 = star z2 * 1 := (mul_one _).symm
        _ = star z2 * (a * z1 + b * z2) := by rw [← hab]
        _ = a * (z1 * star z2) + b * (z2 * star z2) := by ring
    have hpz2 : (p : GaussianInt) ∣ z2 * star z2 := intCast_dvd_of_dvd_gnormB hp2
    have hpQ' : (p : GaussianInt) ∣ z1 * star z2 := by
      rw [mul_comm z1 (star z2)]; exact hpQ
    have hpstar : (p : GaussianInt) ∣ star z2 := by
      rw [hbez]
      exact dvd_add (dvd_mul_of_dvd_right hpQ' a) (dvd_mul_of_dvd_right hpz2 b)
    -- Hence `p² ∣ |z₂|²`, contradicting squarefreeness.
    have hsq : p * p ∣ gnorm z2 := by
      obtain ⟨w, hw⟩ := hpstar
      refine ⟨gnorm w, ?_⟩
      have e : gnorm z2 = gnorm (star z2) := (gnorm_star_eqB z2).symm
      rw [e, hw, gnorm_mul', gnorm_natCastB]
      ring
    exact (Nat.squarefree_iff_prime_squarefree.mp hs2 p hp) hsq
  exact hmain.coprime_dvd_right hq

end Work.FIArea7
