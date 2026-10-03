/-
# `Work.FIArea7.Pub213.dirichletSym_reciprocity_pp` — *FI* (19.12) for primary primitive `w, z`

The Dirichlet symbol `ξ_w(z) = (Re(wz) | |w|²)` (`Work.FIArea7.DirichletSym`) is symmetric on
primary primitive Gaussian integers:

  `ξ_w(z) = ξ_z(w)`  whenever  `IsPP w` and `IsPP z`.

This is *FI* (19.12), proved as `Work.FIArea7.dirichletSym_reciprocity` under the extra hypothesis
that the **product** `wz` is primitive (the form in which (19.8) consumes it).  That hypothesis is
*not* automatic: `w = -1 + 2i` and `z = -1 - 2i` are both primary and primitive while
`w z = 5` is not primitive.  In that degenerate case both symbols vanish, so reciprocity still
holds; the present file supplies the missing case and thereby removes the hypothesis.

Why both symbols vanish.  `ξ_w(z) = (Re(wz) | |w|²)` and `ξ_z(w) = (Re(wz) | |z|²)`; a Jacobi
symbol vanishes exactly when its two arguments are not coprime (`jacobiSym.eq_zero_iff`).  So it
suffices that, `w` and `z` being primitive, every rational prime `p` dividing both coordinates of
`wz` divides `|w|²` and `|z|²` as well.  That is a matrix/determinant statement: modulo `p`,
multiplication by `w` sends `(z.re, z.im)` to `((wz).re, (wz).im) = (0,0)`, and the determinant of
that map is `|w|² = w.re² + w.im²`; if `p ∤ |w|²` the map is invertible modulo `p`, forcing
`z ≡ 0 (mod p)` and contradicting primitivity of `z`.  Formally the whole content is the four
algebraic identities
`|w|²·z.re = Re(wz)·w.re + Im(wz)·w.im`, `|w|²·z.im = Im(wz)·w.re − Re(wz)·w.im`,
`|z|²·w.re = Re(wz)·z.re + Im(wz)·z.im`, `|z|²·w.im = Im(wz)·z.re − Re(wz)·z.im`
of §1 below.
-/
import Mathlib
import Submission.Work.FIArea7.Prop213Aux.Defs
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.DirichletReciprocity

set_option autoImplicit false

namespace Work.FIArea7.Pub213

/-! ## 1. The arithmetic core

Multiplying `w · conj w = |w|²` by `z` (and `z · conj z = |z|²` by `w`) exhibits
`|w|² z.re`, `|w|² z.im`, `|z|² w.re`, `|z|² w.im` as integer combinations of `Re(wz)` and
`Im(wz)`:
`|w|² z.re = Re(wz)·w.re + Im(wz)·w.im`,  `|w|² z.im = Im(wz)·w.re − Re(wz)·w.im`,
`|z|² w.re = Re(wz)·z.re + Im(wz)·z.im`,  `|z|² w.im = Im(wz)·z.re − Re(wz)·z.im`.
Hence any `p` dividing both `Re(wz)` and `Im(wz)` divides all four. -/
lemma dvd_mul_coords_aux {w z : GaussianInt} {p : ℕ}
    (hre : (p : ℤ) ∣ (w * z).re) (him : (p : ℤ) ∣ (w * z).im) :
    ((p : ℤ) ∣ (w.re ^ 2 + w.im ^ 2) * z.re) ∧
      ((p : ℤ) ∣ (w.re ^ 2 + w.im ^ 2) * z.im) ∧
      ((p : ℤ) ∣ (z.re ^ 2 + z.im ^ 2) * w.re) ∧
      ((p : ℤ) ∣ (z.re ^ 2 + z.im ^ 2) * w.im) := by
  rw [Work.FIArea7.re_mul] at hre
  rw [Work.FIArea7.im_mul] at him
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert Int.dvd_add (dvd_mul_of_dvd_right hre w.re) (dvd_mul_of_dvd_right him w.im) using 1
    ring
  · convert Int.dvd_add (dvd_mul_of_dvd_right hre (-w.im)) (dvd_mul_of_dvd_right him w.re) using 1
    ring
  · convert Int.dvd_add (dvd_mul_of_dvd_right hre z.re) (dvd_mul_of_dvd_right him z.im) using 1
    ring
  · convert Int.dvd_add (dvd_mul_of_dvd_right hre (-z.im)) (dvd_mul_of_dvd_right him z.re) using 1
    ring

/-- **A rational prime dividing both coordinates of `wz` divides `|w|²`**, provided `z` is
primitive.  Indeed `p ∣ |w|² · z.re` and `p ∣ |w|² · z.im`; if `p ∤ |w|²` then `p ∣ z.re` and
`p ∣ z.im`, contradicting `IsCoprime z.re z.im`. -/
lemma prime_dvd_gnorm_of_dvd_mul_coords {w z : GaussianInt} (hc : IsCoprime z.re z.im) {p : ℕ}
    (hp : p.Prime) (hre : (p : ℤ) ∣ (w * z).re) (him : (p : ℤ) ∣ (w * z).im) :
    (p : ℤ) ∣ (Work.FIPlan.gnorm w : ℤ) := by
  rw [Work.FIArea7.norm_eq]
  obtain ⟨hA, hB, _, _⟩ := dvd_mul_coords_aux hre him
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_contra hcon
  have hpa : (p : ℤ) ∣ z.re := (hpz.dvd_mul.mp hA).resolve_left hcon
  have hpb : (p : ℤ) ∣ z.im := (hpz.dvd_mul.mp hB).resolve_left hcon
  have hg : p ∣ Int.gcd z.re z.im := Int.dvd_gcd hpa hpb
  have hc1 : Int.gcd z.re z.im = 1 := Int.isCoprime_iff_gcd_eq_one.mp hc
  rw [hc1] at hg
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hg
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- **The symbol vanishes when the product is not primitive.**  For `w` with `|w|² ≠ 0` and `z`
primitive, if `¬ IsCoprime (wz).re (wz).im` then `ξ_w(z) = (Re(wz) | |w|²) = 0`.

Indeed the shared gcd `Int.gcd (wz).re (wz).im` is `≠ 1`, so it has a prime divisor `p` (the
ambiguity at `gcd = 0` is harmless: `p = 2` divides `0`); then `p ∣ (wz).re`, `p ∣ (wz).im` and,
by the previous lemma, `p ∣ |w|²`, so `p` is a common divisor `> 1` of the two arguments of the
Jacobi symbol. -/
lemma dirichletSym_eq_zero_of_not_isCoprime_mul {w z : GaussianInt} (hw0 : Work.FIPlan.gnorm w ≠ 0)
    (hz : IsCoprime z.re z.im) (h : ¬ IsCoprime (w * z).re (w * z).im) :
    DirichletSym w z = 0 := by
  rw [DirichletSym, jacobiSym.eq_zero_iff]
  refine ⟨hw0, ?_⟩
  intro hg
  have hd : Int.gcd (w * z).re (w * z).im ≠ 1 :=
    fun h1 => h (Int.isCoprime_iff_gcd_eq_one.mpr h1)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hd
  have hpre : (p : ℤ) ∣ (w * z).re :=
    dvd_trans (by exact_mod_cast hpdvd) (Int.gcd_dvd_left _ _)
  have hpim : (p : ℤ) ∣ (w * z).im :=
    dvd_trans (by exact_mod_cast hpdvd) (Int.gcd_dvd_right _ _)
  have hgn : (p : ℤ) ∣ (Work.FIPlan.gnorm w : ℤ) := prime_dvd_gnorm_of_dvd_mul_coords hz hp hpre hpim
  have hgd : p ∣ Int.gcd (w * z).re ((Work.FIPlan.gnorm w : ℕ) : ℤ) := Int.dvd_gcd hpre hgn
  rw [hg] at hgd
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hgd
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-! ## 2. Reciprocity for primary primitive `w, z` -/

theorem dirichletSym_reciprocity_pp {w z : GaussianInt} (hw : Prop213Aux.IsPP w)
    (hz : Prop213Aux.IsPP z) : DirichletSym w z = DirichletSym z w := by
  by_cases hcop : IsCoprime (w * z).re (w * z).im
  · -- the primitive case: this is *FI* (19.12) as already proved
    exact dirichletSym_reciprocity hw.primary hz.primary hcop hw.gnorm_pos.ne' hz.gnorm_pos.ne'
  · -- otherwise both symbols vanish
    have h1 : DirichletSym w z = 0 :=
      dirichletSym_eq_zero_of_not_isCoprime_mul hw.gnorm_pos.ne' hz.coprime hcop
    have h2 : DirichletSym z w = 0 := by
      refine dirichletSym_eq_zero_of_not_isCoprime_mul hz.gnorm_pos.ne' hw.coprime ?_
      rwa [mul_comm z w]
    rw [h1, h2]

end Work.FIArea7.Pub213
