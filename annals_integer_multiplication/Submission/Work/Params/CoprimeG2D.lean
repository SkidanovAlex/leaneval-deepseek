import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.uparfacts
import Submission.Work.Params.nt1
import Submission.Work.Params.basic

/-!
# `G₂`-coprimality of §5.1 in the form used by `ssPar`

`ssPar` pairs the exponent `r` with the numbers `s = 2u₀ - 1 + 2F·j` for `1 ≤ j ≤ D - d'`, so the
index `b` occurring there can be as large as `D` (not only `< D`, which is the hypothesis of
`Work.Params.CoprimeG2`).  Since the other index is `a ≥ 1`, we still have `b - a ≤ b - 1 ≤ D - 1`,
hence `(b - a) ∣ F = (D-1)!`, and the generic coprime-shift argument applies verbatim:

`2u₀ - 1` is odd (as `u₀ ≥ 1`) and coprime to `F` (as `u₀ ≡ 1 (mod F)`).  A common divisor `g` of
`2u₀-1+2Fa` and `2u₀-1+2Fb` divides their difference `2F(b-a)`; it is coprime to `2` (it divides
the odd number `2u₀-1+2Fa`) and to `F` (that number is `x + F·(2a)` with `x = 2u₀-1` coprime to
`F`), hence coprime to `2F`; so `g ∣ b - a ∣ F`, and being coprime to `F` it is `1`.

The proof is kept self-contained here (only `defs`/`uparfacts`/`nt1`/`basic` are imported) so that
it does not depend on the exact auxiliary names published by the other `Params` files.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

namespace CoprimeG2Daux

/-- `u₀ ≥ 1`: from `uparfacts`, `u₀ = Q·(1 + mF)` with `Q ≥ 1` and `1 + mF ≥ 1`. -/
theorem one_le_upar (n : ℕ) : 1 ≤ upar n := by
  have h := (uparfacts n).2.2.2.2
  have hQ : 1 ≤ Qall := Qall_pos
  have hsecond : 1 ≤ 1 + ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * Ffac := by omega
  rw [h]
  exact Nat.le_trans (by norm_num : 1 ≤ 1 * 1) (Nat.mul_le_mul hQ hsecond)

/-- `2u₀ - 1` is odd and coprime to `F = (D-1)!`.

Odd because `u₀ ≥ 1`; coprime to `F` because `u₀ ≡ 1 (mod F)`, so `2u₀ - 1 ≡ 1 (mod F)`, and a
number congruent to `1` modulo `F` is coprime to `F`. -/
theorem upar_two_mul_sub_one (n : ℕ) :
    Odd (2 * upar n - 1) ∧ Nat.Coprime (2 * upar n - 1) Ffac := by
  have hu1 : 1 ≤ upar n := one_le_upar n
  refine ⟨⟨upar n - 1, by omega⟩, ?_⟩
  refine Nat.coprime_of_mul_modEq_one 1 ?_
  have h1 : 2 * upar n ≡ 2 * 1 [MOD Ffac] :=
    Nat.ModEq.mul (Nat.ModEq.refl 2) ((uparfacts n).2.2.2.1)
  have h2 := Nat.ModEq.sub (show 1 ≤ 2 * upar n by omega) (show 1 ≤ 2 * 1 by norm_num) h1
    (Nat.ModEq.refl 1)
  have h3 : 2 * upar n - 1 ≡ 1 [MOD Ffac] := by simpa using h2
  simpa using h3

/-- Generic coprimality of two shifted values: if `x` is odd and coprime to `F`, then `x + 2Fa`
and `x + 2Fb` are coprime as soon as `b - a` divides `F`. -/
theorem coprime_shift_two_mul (x F a b : ℕ) (hx : Odd x) (hxF : Nat.Coprime x F)
    (hdvd : (b - a) ∣ F) :
    Nat.Coprime (x + 2 * F * a) (x + 2 * F * b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set g : ℕ := Nat.gcd (x + 2 * F * a) (x + 2 * F * b) with hg
  have hgA : g ∣ x + 2 * F * a := by rw [hg]; exact Nat.gcd_dvd_left _ _
  have hgB : g ∣ x + 2 * F * b := by rw [hg]; exact Nat.gcd_dvd_right _ _
  have hPQ : 2 * F * b - 2 * F * a = 2 * F * (b - a) :=
    (Nat.mul_sub_left_distrib (2 * F) b a).symm
  have hsub1 : (x + 2 * F * b) - (x + 2 * F * a) = 2 * F * b - 2 * F * a := by omega
  have hsub : (x + 2 * F * b) - (x + 2 * F * a) = 2 * F * (b - a) := by rw [hsub1, hPQ]
  have hgdiff : g ∣ 2 * F * (b - a) := by rw [← hsub]; exact Nat.dvd_sub hgB hgA
  have hAodd : Odd (x + 2 * F * a) := by
    apply hx.add_even
    rw [show 2 * F * a = 2 * (F * a) from by ring]
    exact even_two_mul (F * a)
  have hAF : Nat.Coprime (x + 2 * F * a) F := by
    rw [show x + 2 * F * a = x + F * (2 * a) from by ring]
    exact (Nat.coprime_add_mul_left_left x F (2 * a)).mpr hxF
  have hg2 : Nat.Coprime g 2 :=
    Nat.Coprime.coprime_dvd_left hgA (Nat.coprime_two_right.mpr hAodd)
  have hgF : Nat.Coprime g F := Nat.Coprime.coprime_dvd_left hgA hAF
  have hg2F : Nat.Coprime g (2 * F) := hg2.mul_right hgF
  have hgdvd : g ∣ b - a := Nat.Coprime.dvd_of_dvd_mul_left hg2F hgdiff
  exact Nat.eq_one_of_dvd_coprimes hgF (dvd_refl g) (hgdvd.trans hdvd)

/-- `(b-a) ∣ Ffac` whenever `1 ≤ a < b ≤ D`: then `0 < b - a ≤ b - 1 ≤ D - 1`, and every
`m` with `0 < m ≤ D - 1` divides `F = (D-1)!`. -/
theorem sub_dvd_Ffac_of_le_D {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ D) :
    (b - a) ∣ Ffac := by
  have hpos : 0 < b - a := by omega
  have hle : b - a ≤ D - 1 := by omega
  exact Nat.dvd_factorial hpos hle

end CoprimeG2Daux

theorem CoprimeG2D (n : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ D) :
    Nat.Coprime (2 * upar n - 1 + 2 * Ffac * a) (2 * upar n - 1 + 2 * Ffac * b) :=
  CoprimeG2Daux.coprime_shift_two_mul (2 * upar n - 1) Ffac a b
    (CoprimeG2Daux.upar_two_mul_sub_one n).1 (CoprimeG2Daux.upar_two_mul_sub_one n).2
    (CoprimeG2Daux.sub_dvd_Ffac_of_le_D ha hab hb)

end Work.Params
