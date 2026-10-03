/-
# Area 4 (round 6, `A6psi`): the §15 ratio symbol vanishes off the coprimality locus

The round-6 §15 per-modulus sum `S15pDng6` (and hence `pDng6_le_EvarG`) runs over pairs
`zᵢ = scalePt e wᵢ` of the `e`-stratum with `X < d` and `4d ∣ |Δ(z₁,z₂)|`.  Its summand carries
*FI*'s ratio symbol `(z₂/z₁|d) = Work.FIArea7.ratioSym z₁ z₂ d` of modulus `d = e·d'` — the Jacobi
symbol of the rational residue of the Gaussian ratio `z₂/z₁` modulo `d` (`ReSymbolTwist.ratioSym`).
This file records the vanishing statement the stratification needs: **if `|z₁|²` is not coprime to
`d = e·d'`, then `(z₂/z₁|d) = 0`**, so the corresponding terms contribute nothing.

## The mathematics

Let `z = r + is` and write `Δ(z₁,z₂) = Im(z̄₁z₂)` (*FI* (6.1)).

1. **Splitting off the norm.**  `ratioSym z₁ z₂ d` is the Jacobi symbol of the canonical
   representative of `Re(z̄₁z₂)·|z₁|²⁻¹ (mod d)`.  Since `jacobiSym` is multiplicative in its
   numerator (`jacobiSym.mul_left`) and depends on it only through its residue class
   (`jacobiSym.mod_left'`), the inverse factor splits off and

     `ratioSym z₁ z₂ d = (Re(z̄₁z₂)|d) · T`   (†)

   with `T` the Jacobi symbol of the canonical representative of `|z₁|²⁻¹ (mod d)`.  This is
   `aux_ratioSym_factor` below; no coprimality is needed (only `d ≥ 1`, so that `ZMod d ≠ ℤ`).
   So it suffices that the *first* factor — the numerator — is not coprime to `d`.

2. **A prime of `(|z₁|², d)` divides `Δ(z₁,z₂)`.**  `4d' ∣ |Δ(w₁,w₂)|` gives
   `Δ(z₁,z₂) = e·Δ(w₁,w₂) = 4dk`, hence `4d ∣ Δ(z₁,z₂)`; in particular any `p ∣ d` divides
   `Δ(z₁,z₂)`.  (This is where `h4` enters, and the reason the lemma is stated at the *scaled*
   pair: the modulus `d = e·d'` is exactly the scale factor of `Δ`.)

3. **`p ∣ |z₁|²` and `p ∣ Δ(z₁,z₂)` force `p ∣ Re(z̄₁z₂)`.**  The real and imaginary parts of
   `z̄₁z₂` are `Re(z̄₁z₂)` and `Δ(z₁,z₂)`, the coordinates of the product `z₁z₂`, so

     `Re(z̄₁z₂)² + Δ(z₁,z₂)² = |z₁|²·|z₂|²`    (‡)

   (both sides are `(r₁r₂+s₁s₂)² + (r₁s₂-s₁r₂)² = (r₁²+s₁²)(r₂²+s₂²)`).  Hence `p ∣ Re(z̄₁z₂)²`,
   and `p` prime gives `p ∣ Re(z̄₁z₂)`.  This is `aux_prime_dvd_re_star` below; only `p ∣ Δ(z₁,z₂)`
   and `p ∣ |z₁|²` are used — not the shape of the hypothesis that produced them.

4. **Conclusion.**  `p ∣ Re(z̄₁z₂)` and `p ∣ d` show that `(Re(z̄₁z₂), d) ≠ 1`, so
   `(Re(z̄₁z₂)|d) = 0` (`jacobiSym.eq_zero_iff_not_coprime`), and (†) gives `ratioSym = 0`.

The hypotheses `hc1` (coprimality of `Re w₁` with `d'`) and `hprim` (primitivity of `w₁`) belong to
the §15 set-up but are *not* used here: the claim holds for arbitrary `w₁, w₂` as soon as
`4d' ∣ |Δ(w₁,w₂)|`.  No hypothesis of the statement is weakened — the statement is simply slightly
stronger than the flabby form in which the §15 chain needs it.  The two ingredients are also
available as the standalone lemmas `Work.FIArea4.A6psi.prime_dvd_re_star_of_dvd_norm_and_Delta`
(the Gaussian core, step 3) and `Work.FIArea7.ratioSym_eq_jacobiSym_mul_inv` (step 1); they are
reproved privately here so that this file is self-contained.
-/
import Mathlib
import Submission.Work.FIArea4.S15red.stratumSumE_le_EvarG
import Submission.Work.FIArea4.S15delta
import Submission.Work.FIArea7.ReSymbolTwist
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.A6psi

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Step 3 of the module doc.**  For a prime `p`, if `p ∣ |z₁|²` and `p ∣ Δ(z₁,z₂)`, then `p`
divides `Re(z̄₁z₂)`: by (‡), `p` divides `Re(z̄₁z₂)² = |z₁|²|z₂|² - Δ(z₁,z₂)²`, and `p` is prime. -/
private theorem aux_prime_dvd_re_star {p : ℕ} (hp : p.Prime) {z1 z2 : GaussianInt}
    (hg : (p : ℤ) ∣ (Work.FIPlan.gnorm z1 : ℤ))
    (hD : (p : ℤ) ∣ Work.FIPlan.Delta z1 z2) :
    (p : ℤ) ∣ (star z1 * z2).re := by
  have hpz : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  -- (‡): `|z₁|²|z₂|² = Re(z̄₁z₂)² + Δ(z₁,z₂)²`
  have hid : (Work.FIPlan.gnorm z1 : ℤ) * (Work.FIPlan.gnorm z2 : ℤ)
      = ((star z1 * z2).re) ^ 2 + (Work.FIPlan.Delta z1 z2) ^ 2 := by
    rw [Work.FIArea4.re_star_mul_eq, Work.FIArea4.Delta_eq,
      Work.FIArea7.norm_eq z1, Work.FIArea7.norm_eq z2]
    ring
  have h2 : (p : ℤ) ∣ ((star z1 * z2).re) ^ 2 + (Work.FIPlan.Delta z1 z2) ^ 2 := by
    rw [← hid]; exact dvd_mul_of_dvd_left hg _
  have h3 : (p : ℤ) ∣ (Work.FIPlan.Delta z1 z2) ^ 2 := by
    rw [pow_two]; exact dvd_mul_of_dvd_left hD _
  have h4 : (p : ℤ) ∣ ((star z1 * z2).re) ^ 2 := by
    have h5 := dvd_sub h2 h3
    simpa using h5
  exact hpz.dvd_of_dvd_pow h4

/-- **Step 1 of the module doc (†).**  The ratio symbol factors as the product of the Jacobi
symbol of its numerator `Re(z̄₁z₂)` and that of the canonical representative of `|z₁|²⁻¹ (mod d)`.

No coprimality is needed: both the construction of `ratioSym` and the multiplicativity
`jacobiSym.mul_left` are available for every modulus, and `jacobiSym.mod_left'` identifies the
symbol of the canonical representative of `Re(z̄₁z₂)·|z₁|²⁻¹` with that of the product
`Re(z̄₁z₂) · (|z₁|²⁻¹ as an integer)`. -/
private theorem aux_ratioSym_factor (z1 z2 : GaussianInt) (d : ℕ) [NeZero d] :
    Work.FIArea7.ratioSym z1 z2 d
      = jacobiSym ((star z1 * z2).re) d
        * jacobiSym ((((Work.FIPlan.gnorm z1 : ZMod d)⁻¹).val : ℕ) : ℤ) d := by
  unfold Work.FIArea7.ratioSym
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  rw [← ZMod.intCast_eq_intCast_iff']
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- **The §15 ratio symbol vanishes off the coprimality locus.**

For `e, d' ≥ 1` and a pair `zᵢ = scalePt e wᵢ` of the `e`-stratum of modulus `d = e·d'` with
`4d' ∣ |Δ(w₁,w₂)|` (so that `4d ∣ |Δ(z₁,z₂)|` and the Gaussian ratio `z₂/z₁` is rational mod `d`),
if `|z₁|² = gnorm (scalePt e w₁)` is **not** coprime to `d = e·d'` then *FI*'s ratio symbol
`(z₂/z₁|d) = Work.FIArea7.ratioSym z₁ z₂ d` is `0`.

`hc1` and `hprim` are unused (see the module doc): the only arithmetic input is `h4`. -/
theorem ratioSym_scalePt_eq_zero_of_not_coprime (e d' : ℕ) (he : 1 ≤ e) (hd' : 1 ≤ d')
    (w1 w2 : GaussianInt)
    (hc1 : Nat.Coprime w1.re.natAbs d')
    (hprim : Nat.Coprime ((e : ℤ) * w1.re).natAbs (2 * w1.im.natAbs))
    (h4 : 4 * d' ∣ Work.FIPlan.absDelta w1 w2)
    (hcop : ¬ Nat.Coprime (Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1)) (e * d')) :
    Work.FIArea7.ratioSym (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) (e * d') = 0 := by
  have hpos : 0 < e * d' := Nat.mul_pos (by omega) (by omega)
  haveI : NeZero (e * d') := NeZero.of_pos hpos
  -- a prime dividing both `|z₁|²` and the modulus `d = e·d'`
  obtain ⟨p, hp, hpg, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  -- **2.** `4d' ∣ |Δ(w₁,w₂)|` puts `Δ(w₁,w₂)` in `(4d')ℤ`
  have hDw : ((4 * d' : ℕ) : ℤ) ∣ Work.FIPlan.Delta w1 w2 := by
    have h1 : ((4 * d' : ℕ) : ℤ) ∣ ((Work.FIPlan.absDelta w1 w2 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr h4
    exact Int.dvd_natAbs.mp h1
  -- hence `p ∣ Δ(scalePt e w₁, scalePt e w₂) = e·Δ(w₁,w₂)`
  have hDz : (p : ℤ) ∣
      Work.FIPlan.Delta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) := by
    have hDd : (((e * d' : ℕ)) : ℤ) ∣
        Work.FIPlan.Delta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) := by
      rw [Work.FIArea4.S15red.SSE.Delta_scalePt]
      obtain ⟨k, hk⟩ := hDw
      rw [hk]
      refine ⟨4 * k, ?_⟩
      push_cast
      ring
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hpd) hDd
  -- and `p ∣ |z₁|²`
  have hgz : (p : ℤ) ∣ (Work.FIPlan.gnorm (Work.FIArea4.scalePt e w1) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpg
  -- **3.** so `p ∣ Re(z̄₁z₂)`
  have hre : (p : ℤ) ∣
      (star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re :=
    aux_prime_dvd_re_star hp hgz hDz
  have hpa : p ∣
      ((star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hre)
  -- **4.** the numerator of the ratio symbol is not coprime to `d`
  have hnum : jacobiSym ((star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re)
      (e * d') = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime]
    intro hg
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast] at hg
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpa, hpd⟩)
      (Nat.coprime_iff_gcd_eq_one.mpr hg)
  -- **1.** and the inverse factor splits off multiplicatively
  rw [aux_ratioSym_factor, hnum, zero_mul]

end

end Work.FIArea4.A6psi
