/-
# `Submission.Work.FIArea7.KStarAP.dvd_and_primary_iff_modEq`

The arithmetic core of the Möbius reduction of *FI* §22 for the co-primality restricted form
`K*(N)`: for a **primary** Gaussian integer `e` with primitive coordinates
(`IsCoprime e.re e.im`) and an **odd** rational integer `r`, the Gaussian integers `r + is` that
are both divisible by `e` and primary form exactly one residue class of `s` modulo
`4 · |e|² = 4 · gnorm e`.

Mathematically: writing `e = u + iv` (`u = e.re`, `v = e.im`, `N = u² + v² = gnorm e`),

* `e ∣ r + is` ⟺ `N ∣ (u s - v r)` (the ideal `(e)` is a lattice of covolume `N`, whose
  intersection with the vertical line `Re = r` is a single class of `s` mod `N`; this uses
  `IsCoprime u v` so that `gcd(u, N) = 1`),
* `r + is` is primary ⟺ `s ≡ r - 1 [ZMOD 4]` (the primary condition `z ≡ 1 mod 2(1+i)` in
  coordinates is `s` even and `s ≡ r - 1 (mod 4)`; the parity of `s` is forced by the congruence
  because `r` is odd),
* since `e` primary forces `N` odd, `gcd(N, 4) = 1`, so the conjunction of a class mod `N` and a
  class mod `4` is a single class modulo `4 N` (Chinese remainder).

The final statement is exactly the interface required by the requester.
-/
import Mathlib
import Submission.Work.FIArea7.KStarDefs

set_option autoImplicit false

namespace Work.FIArea7.KStarAP

open Work.FIPlan

/-! ## Coordinates of a product of Gaussian integers -/

private lemma gmul_re (w z : GaussianInt) : (w * z).re = w.re * z.re - w.im * z.im :=
  Work.FIArea7.re_mul w z

private lemma gmul_im (w z : GaussianInt) : (w * z).im = w.re * z.im + w.im * z.re :=
  Work.FIArea7.im_mul w z

/-! ## `gcd(e.re, |e|²) = 1` for primitive `e` -/

private lemma isCoprime_re_gnorm (e : GaussianInt) (he : IsCoprime e.re e.im) :
    IsCoprime e.re ((Work.FIPlan.gnorm e : ℕ) : ℤ) := by
  obtain ⟨a, b, hab⟩ := he
  refine ⟨a ^ 2 * e.re + 2 * a * b * e.im - b ^ 2 * e.re, b ^ 2, ?_⟩
  have hNz : ((Work.FIPlan.gnorm e : ℕ) : ℤ) = e.re ^ 2 + e.im ^ 2 := Work.FIArea7.norm_eq e
  rw [hNz]
  nlinarith [hab]

private lemma isPrimary_odd_gnorm {z : GaussianInt} (hz : IsPrimary z) : Odd (gnorm z) := by
  obtain ⟨ho, he, _⟩ := hz
  have hnorm : ((gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
  have hZ : Odd ((gnorm z : ℕ) : ℤ) := by
    rw [hnorm]
    exact (ho.pow).add_even (by rw [pow_two]; exact he.mul_right z.im)
  exact_mod_cast hZ

/-! ## Divisibility by `e` is a single congruence on `Im` -/

private lemma dvd_char_fwd (e : GaussianInt) (r s : ℤ) :
    e ∣ (⟨r, s⟩ : GaussianInt) → ((gnorm e : ℕ) : ℤ) ∣ (e.re * s - e.im * r) := by
  intro h
  obtain ⟨w, hw⟩ := h
  have hr : r = e.re * w.re - e.im * w.im := by
    have := congrArg Zsqrtd.re hw; rwa [gmul_re] at this
  have hs : s = e.re * w.im + e.im * w.re := by
    have := congrArg Zsqrtd.im hw; rwa [gmul_im] at this
  exact ⟨w.im, by rw [hr, hs, Work.FIArea7.norm_eq]; ring⟩

private lemma dvd_char_bwd (e : GaussianInt) (r s : ℤ) (he : IsCoprime e.re e.im) (he0 : e ≠ 0) :
    ((gnorm e : ℕ) : ℤ) ∣ (e.re * s - e.im * r) → e ∣ (⟨r, s⟩ : GaussianInt) := by
  intro hdvd
  set Nz : ℤ := ((gnorm e : ℕ) : ℤ) with hNzdef
  have hN : Nz = e.re ^ 2 + e.im ^ 2 := by rw [hNzdef, Work.FIArea7.norm_eq]
  have hcop : IsCoprime e.re Nz := by rw [hNzdef]; exact isCoprime_re_gnorm e he
  have hNz_ne : Nz ≠ 0 := by
    rw [hNzdef]; exact_mod_cast (Work.FIArea7.gnorm_eq_zero_iff.not.mpr he0)
  obtain ⟨k, hk⟩ := hdvd
  have hkN : (e.re ^ 2 + e.im ^ 2) * k = e.re * s - e.im * r := by rw [← hN]; exact hk.symm
  have h1 : Nz ∣ e.re * (e.re * r + e.im * s) := by
    refine ⟨r + k * e.im, ?_⟩
    rw [hN]
    linear_combination -e.im * hkN
  obtain ⟨m, hm⟩ := hcop.symm.dvd_of_dvd_mul_left h1
  have hmk : e.re * m - e.im * k = r := by
    apply mul_left_cancel₀ hNz_ne
    rw [show Nz * (e.re * m - e.im * k) = e.re * (Nz * m) - e.im * (Nz * k) by ring,
        show Nz * m = e.re * r + e.im * s from hm.symm,
        show Nz * k = e.re * s - e.im * r from hk.symm, hN]
    ring
  have hsk : e.re * k + e.im * m = s := by
    apply mul_left_cancel₀ hNz_ne
    rw [show Nz * (e.re * k + e.im * m) = e.re * (Nz * k) + e.im * (Nz * m) by ring,
        show Nz * m = e.re * r + e.im * s from hm.symm,
        show Nz * k = e.re * s - e.im * r from hk.symm, hN]
    ring
  refine ⟨⟨m, k⟩, ?_⟩
  rw [Zsqrtd.ext_iff]
  exact ⟨by rw [gmul_re]; simpa using hmk.symm, by rw [gmul_im]; simpa using hsk.symm⟩

private lemma dvd_iff (e : GaussianInt) (r s : ℤ) (he : IsCoprime e.re e.im) (he0 : e ≠ 0) :
    e ∣ (⟨r, s⟩ : GaussianInt) ↔ ((gnorm e : ℕ) : ℤ) ∣ (e.re * s - e.im * r) :=
  ⟨dvd_char_fwd e r s, dvd_char_bwd e r s he he0⟩

/-! ## The primary condition on the line `Re = r` -/

private lemma isPrimary_mk_iff (r s : ℤ) (hr : Odd r) :
    IsPrimary (⟨r, s⟩ : GaussianInt) ↔ s ≡ r - 1 [ZMOD 4] := by
  unfold Work.FIPlan.IsPrimary
  simp only
  constructor
  · intro h; exact h.2.2
  · intro h
    refine ⟨hr, ?_, h⟩
    have h4 : (4 : ℤ) ∣ (r - 1) - s := Int.modEq_iff_dvd.mp h
    have h2 : (2 : ℤ) ∣ (r - 1) - s := dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h4
    have hro : (2 : ℤ) ∣ r - 1 := by obtain ⟨t, ht⟩ := hr; exact ⟨t, by omega⟩
    have hs : (2 : ℤ) ∣ s := by have := Int.dvd_sub hro h2; simpa using this
    exact even_iff_two_dvd.mpr hs

/-! ## Main theorem -/

theorem dvd_and_primary_iff_modEq (e : GaussianInt) (r : ℤ)
    (he : IsCoprime e.re e.im) (heprim : Work.FIPlan.IsPrimary e) (hr : Odd r) :
    ∃ c : ℤ, ∀ s : ℤ,
      (e ∣ (⟨r, s⟩ : GaussianInt) ∧ Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt)) ↔
        s ≡ c [ZMOD (4 * (((Work.FIPlan.gnorm e : ℕ) : ℤ)))] := by
  have he0 : e ≠ 0 := by
    rintro rfl
    exact (by rintro ⟨k, hk⟩; omega : ¬ Odd (0 : ℤ)) (by simpa using heprim.1)
  set Nz : ℤ := ((Work.FIPlan.gnorm e : ℕ) : ℤ) with hNzdef
  have hcop_re : IsCoprime e.re Nz := by rw [hNzdef]; exact isCoprime_re_gnorm e he
  have hcop4 : Nat.Coprime 4 (Work.FIPlan.gnorm e) := by
    have hodd : Odd (Work.FIPlan.gnorm e) := isPrimary_odd_gnorm heprim
    have h2 : Nat.Coprime 2 (Work.FIPlan.gnorm e) := Nat.coprime_two_left.mpr hodd
    simpa using h2.pow_left 2
  have h4Nz : (4 : ℤ).natAbs.Coprime Nz.natAbs := by simpa [hNzdef] using hcop4
  have hcop_re_sym : IsCoprime Nz e.re := IsCoprime.symm hcop_re
  obtain ⟨a, b, hab⟩ := hcop_re
  have ha : e.re * a ≡ 1 [ZMOD Nz] := by
    rw [Int.modEq_iff_dvd]; exact ⟨b, by linear_combination -hab⟩
  obtain ⟨z, hz⟩ := Int.mod_coprime hcop4
  have hz' : (4 : ℤ) * z ≡ 1 [ZMOD Nz] := by rw [hNzdef]; exact hz
  set d : ℤ := e.im * r * a with hd
  set t : ℤ := z * (d - (r - 1)) with ht
  set c : ℤ := (r - 1) + 4 * t with hc
  have hd_eq : e.re * d ≡ e.im * r [ZMOD Nz] := by
    rw [hd, show e.re * (e.im * r * a) = (e.re * a) * (e.im * r) by ring]
    calc (e.re * a) * (e.im * r) ≡ 1 * (e.im * r) [ZMOD Nz] := ha.mul_right _
      _ = e.im * r := by ring
  have h4t : (4 : ℤ) * t ≡ d - (r - 1) [ZMOD Nz] := by
    rw [ht, show (4 : ℤ) * (z * (d - (r - 1))) = ((4 : ℤ) * z) * (d - (r - 1)) by ring]
    calc ((4 : ℤ) * z) * (d - (r - 1)) ≡ 1 * (d - (r - 1)) [ZMOD Nz] := hz'.mul_right _
      _ = d - (r - 1) := by ring
  have hc4 : c ≡ r - 1 [ZMOD 4] := by
    rw [hc, Int.modEq_iff_dvd]; exact ⟨-t, by ring⟩
  have hcN : e.re * c ≡ e.im * r [ZMOD Nz] := by
    have h2' : e.re * ((4 : ℤ) * t) ≡ e.re * (d - (r - 1)) [ZMOD Nz] := h4t.mul_left e.re
    have hsum : e.re * (r - 1) + e.re * ((4 : ℤ) * t) ≡ e.re * d [ZMOD Nz] := by
      have h2'' := (Int.ModEq.refl (e.re * (r - 1))).add h2'
      convert h2'' using 1; ring
    have key1 : e.re * c = e.re * (r - 1) + e.re * ((4 : ℤ) * t) := by rw [hc]; ring
    rw [key1]
    exact hsum.trans hd_eq
  refine ⟨c, ?_⟩
  intro s
  rw [dvd_iff e r s he he0, isPrimary_mk_iff r s hr]
  constructor
  · rintro ⟨hBs, hAs⟩
    have hsc4 : s ≡ c [ZMOD 4] := hAs.trans hc4.symm
    have h2 : Nz ∣ e.im * r - e.re * c := Int.modEq_iff_dvd.mp hcN
    have hsum : Nz ∣ e.re * (s - c) := by
      have := Int.dvd_add hBs h2
      convert this using 1; ring
    have hscc : Nz ∣ s - c := IsCoprime.dvd_of_dvd_mul_left hcop_re_sym hsum
    have hscN : s ≡ c [ZMOD Nz] := (Int.modEq_iff_dvd.mpr hscc).symm
    exact (Int.modEq_and_modEq_iff_modEq_mul h4Nz).mp ⟨hsc4, hscN⟩
  · intro h
    have hsc4 : s ≡ c [ZMOD 4] := Int.ModEq.of_dvd (dvd_mul_right 4 Nz) h
    have hscN : s ≡ c [ZMOD Nz] := Int.ModEq.of_dvd (dvd_mul_left Nz 4) h
    have hAs : s ≡ r - 1 [ZMOD 4] := hsc4.trans hc4
    have hBs : Nz ∣ e.re * s - e.im * r :=
      Int.modEq_iff_dvd.mp ((hscN.mul_left e.re).trans hcN).symm
    exact ⟨hBs, hAs⟩

end Work.FIArea7.KStarAP
