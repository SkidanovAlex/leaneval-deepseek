import Mathlib
import Submission.Work.FIArea7.coprime_gnorm_absDelta

set_option autoImplicit false

namespace Work.FIArea7

/-!
# `Re(z₁z̄₂)` and `Δ(z₁,z₂)` are coprime for primary, squarefree-norm, Gaussian-coprime `z₁, z₂`

The paper's §17 needs, besides `(N(z₁), |Δ|) = 1` (proved in `Work.FIArea7.coprime_gnorm_absDelta`),
the coprimality of the *real* part `Re(z₁z̄₂) = r₁r₂ + s₁s₂` with `|Δ(z₁,z₂)| = |Im(z̄₁z₂)|`; this is
what makes the Jacobi symbols `(Re(z̄₁z₂)‖Δ|)` of (17.5) well defined.

Write `W = z₁·z̄₂`, so that `W.re = r₁r₂ + s₁s₂` and `Im(z̄₁z₂) = -W.im`, and suppose a rational prime
`p` divides both coordinates of `W`, i.e. `(p : ℤ[i]) ∣ W`.

* `W = p·c` gives `p² ∣ N(W) = gnorm z₁ · gnorm z₂`; with both norms squarefree this forces
  `p ∣ gnorm z₁` and `p ∣ gnorm z₂`.
* Bézout `a z₁ + b z₂ = 1` from `IsCoprime z₁ z₂`, multiplied by `z̄₂`, reads
  `z̄₂ = a·W + b·(gnorm z₂ : ℤ[i])`; both summands are divisible by `p`, hence `p ∣ z̄₂`, hence
  `p ∣ z₂`.
* But then `p² ∣ gnorm z₂`, contradicting squarefreeness of `gnorm z₂`.

So no rational prime divides `W`, which by `Zsqrtd.intCast_dvd` is exactly the coprimality of the
two coordinates of `W`.  (`IsPrimary` and `0 < absDelta` are not needed for this step; they are part
of the requested interface.)
-/

open Work.FIPlan

/-- `Re(z₁z̄₂) = r₁r₂ + s₁s₂`. -/
lemma re_mul_conj (z1 z2 : GaussianInt) :
    (z1 * star z2).re = z1.re * z2.re + z1.im * z2.im := by
  rw [Zsqrtd.re_mul]
  simp only [Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- `Δ(z₁,z₂) = Im(z̄₁z₂) = -Im(z₁z̄₂)`. -/
lemma delta_eq_neg_im (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = -(z1 * star z2).im := by
  rw [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.im_mul]
  simp only [Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- `|Δ(z₁,z₂)| = |Im(z₁z̄₂)|`. -/
lemma absDelta_eq_im_natAbs (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z1 z2 = (z1 * star z2).im.natAbs := by
  rw [Work.FIPlan.absDelta, delta_eq_neg_im, Int.natAbs_neg]

/-- Conjugation preserves the norm. -/
lemma gnorm_star (z : GaussianInt) : Work.FIPlan.gnorm (star z) = Work.FIPlan.gnorm z := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_conj]

/-- The norm of the rational integer `p` inside `ℤ[i]` is `p²`. -/
lemma gnorm_natCast_gauss (p : ℕ) : Work.FIPlan.gnorm (p : GaussianInt) = p ^ 2 := by
  rw [show (p : GaussianInt) = ((p : ℤ) : GaussianInt) by push_cast; ring, gnorm_intCast']
  simp

/-- `z z̄ = |z|²` as Gaussian integers. -/
lemma mul_star_eq_gnorm_cast (z : GaussianInt) :
    z * star z = ((Work.FIPlan.gnorm z : ℤ) : GaussianInt) := by
  have h : ((Work.FIPlan.gnorm z : ℤ) : GaussianInt) = ((z.norm : ℤ) : GaussianInt) := by
    congr 1
    rw [gnorm_int', Zsqrtd.norm_def]; ring
  rw [h]; exact (Zsqrtd.norm_eq_mul_conj z).symm

/-- The conjugate of a rational integer is itself. -/
lemma star_natCast_gauss (p : ℕ) : star (p : GaussianInt) = (p : GaussianInt) := by
  simp [Zsqrtd.star_mk, Zsqrtd.natCast_val]

/-- **The core arithmetic fact.**  No rational prime divides `z₁z̄₂` when `z₁, z₂` have squarefree
norm and are coprime in `ℤ[i]`. -/
theorem rat_prime_not_dvd_mul_star {z1 z2 : GaussianInt}
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2) (p : ℕ) (hp : Nat.Prime p) :
    ¬ ((p : GaussianInt) ∣ z1 * star z2) := by
  intro hdvd
  -- the norm of `z₁z̄₂` is `|z₁|²|z₂|²`
  have hWg : Work.FIPlan.gnorm (z1 * star z2)
      = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := by
    rw [gnorm_mul', gnorm_star]
  obtain ⟨c, hc_eq⟩ := hdvd
  have hdvdW : (p : GaussianInt) ∣ z1 * star z2 := ⟨c, hc_eq⟩
  -- `p² ∣ |z₁|²|z₂|²`
  have hsqW : p ^ 2 ∣ Work.FIPlan.gnorm (z1 * star z2) := by
    rw [hc_eq, gnorm_mul', gnorm_natCast_gauss]
    exact dvd_mul_right _ _
  have hprod : p ^ 2 ∣ Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := hWg ▸ hsqW
  -- squarefreeness forces `p ∣ |z₂|²`
  have hpgn : p ∣ Work.FIPlan.gnorm z2 :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hs1 (by rwa [pow_two] at hprod)
  -- Bézout, multiplied by `z̄₂`
  obtain ⟨a, b, hab⟩ := hc
  have hbez : a * (z1 * star z2) + b * ((Work.FIPlan.gnorm z2 : ℤ) : GaussianInt) = star z2 := by
    have h1 : (a * z1 + b * z2) * star z2 = star z2 := by rw [hab, one_mul]
    have h2 : (a * z1 + b * z2) * star z2
        = a * (z1 * star z2) + b * ((Work.FIPlan.gnorm z2 : ℤ) : GaussianInt) := by
      rw [add_mul, ← mul_star_eq_gnorm_cast]
      ring
    rw [← h2, h1]
  -- hence `p ∣ z̄₂`
  have hpN : (p : GaussianInt) ∣ ((Work.FIPlan.gnorm z2 : ℤ) : GaussianInt) := by
    obtain ⟨m, hm⟩ := hpgn
    exact ⟨(m : GaussianInt), by rw [hm]; push_cast; ring⟩
  have hdvd_star : (p : GaussianInt) ∣ star z2 := by
    rw [← hbez]
    exact dvd_add (dvd_mul_of_dvd_right hdvdW a) (dvd_mul_of_dvd_right hpN b)
  have hdvd_z2 : (p : GaussianInt) ∣ z2 := by
    obtain ⟨e, he⟩ := hdvd_star
    refine ⟨star e, ?_⟩
    rw [← star_star z2, he, star_mul]
    simp [mul_comm]
  -- and then `p² ∣ |z₂|²`, contradicting squarefreeness
  obtain ⟨d, hd⟩ := hdvd_z2
  have hsq2 : p ^ 2 ∣ Work.FIPlan.gnorm z2 := by
    rw [hd, gnorm_mul', gnorm_natCast_gauss]
    exact dvd_mul_right _ _
  exact (Nat.squarefree_iff_prime_squarefree.mp hs2 p hp) (by rwa [pow_two] at hsq2)

theorem coprime_re_absDelta {z1 z2 : GaussianInt}
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2) (hD : 0 < Work.FIPlan.absDelta z1 z2) :
    Nat.Coprime (Int.natAbs (z1.re * z2.re + z1.im * z2.im))
      (Work.FIPlan.absDelta z1 z2) := by
  have _ := hP1
  have _ := hP2
  have _ := hD
  have hkey : ∀ p : ℕ, Nat.Prime p →
      ¬ (p ∣ (z1 * star z2).re.natAbs ∧ p ∣ (z1 * star z2).im.natAbs) := by
    intro p hp hcon
    have hds : (p : GaussianInt) ∣ z1 * star z2 := by
      refine (Zsqrtd.intCast_dvd (p : ℤ) (z1 * star z2)).mpr ⟨?_, ?_⟩
      · exact Int.dvd_natAbs.mp (by exact_mod_cast hcon.1)
      · exact Int.dvd_natAbs.mp (by exact_mod_cast hcon.2)
    exact rat_prime_not_dvd_mul_star hs1 hs2 hc p hp hds
  rw [← re_mul_conj z1 z2, absDelta_eq_im_natAbs z1 z2]
  exact Nat.coprime_of_dvd' (fun p hp h1 h2 => absurd ⟨h1, h2⟩ (hkey p hp))

end Work.FIArea7
