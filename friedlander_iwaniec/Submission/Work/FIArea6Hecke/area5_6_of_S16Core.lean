/-
# `Submission.Work.FIArea6Hecke.area5_6_of_S16Core`

The reduction of the §16 bridge from its *strict* form (`Work.FITop4.Bridge.S16Core`, *FI* Lemma
16.2 for the characters of `(ℤ[i]/4d)^*` extended by zero off the units) to the frozen
`Work.FITop4.Area5_6`, which quantifies over **all** characters of modulus `4d` in the sense of
`Work.FITop3.IsCharMod4d` (multiplicative, bounded by `1`, periodic modulo `4d`, vanishing on
multiples of `4d` — but *not* required to vanish off the units).

## The reduction

`IsBetaCoeff6.noSmallPrimes` puts every point of the support of `β` in the region (5.8)
(`NoSmallPrimes`), i.e. free of rational primes `≤ Pz`.  Since `d ≤ Pz` (see
`Work.FIArea6Hecke.le_Pz_of_log_bound`, the threshold bookkeeping of `(log N)^ν` versus
`hPlo : (log log x)² ≤ log Pz`), every prime divisor of `4d` is `≤ Pz`, and then no prime ideal
above `4d` can divide a support point: the character criterion

  `IsUnitMod4d d z ↔ IsUnit ((gnorm z : ℕ) : ZMod (4*d)) ↔ Nat.Coprime (gnorm z) (4*d)`

(proved below from the residue-ring model `(ZMod (4d))²` with the Gaussian multiplication `gmul` of
`Submission.Work.FIArea5.S16Hecke.GaussBasic`) identifies the units modulo `4d` with the classes
of norm coprime to `4d`.

Hence `β_z·χ(z) = β_z·χ̃(z)` on the support, where

  `χ̃ z = if IsUnitMod4d d z then χ z else 0`

is *strict* (vanishes off the units by construction), and `S16Core` applies to `χ̃` and to `β`.
The two statements carry the same `cε` (in both exponentials and as the prefactor) and the same
`(4d)N(log N)^6`, so only the threshold `max x₀ X₀` remains.

## Contents

* §1 the residue-ring characterisation of `IsUnitMod4d` (`gsq`, `gmul`, `ZMod`);
* §2 the elementary API of `IsUnitMod4d` (multiplicativity, congruence, non-units);
* §3 the strict part `χ̃` of a character and `IsCharMod4dStrict d χ̃`;
* §4 support points are units (`isUnitMod4d_of_noSmallPrimes`);
* §5 the assembly.
-/

import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.GaussBasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Work.FIArea6Hecke

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The residue ring `ℤ[i]/(4d)` and the norm criterion for units -/

namespace GaussUnit

open Work.FIArea5.S16Hecke (gmul gone gconj gsq gOfZI zOfG IsUnitR IsUnitMod4d)
open Work.FIArea5.S16Hecke.GaussBasic

variable {d : ℕ} [NeZero (4 * d)]

/-- Multiplication of the two classes `(a,0)`, `(a',0)` (i.e. of the "real" classes). -/
lemma gmul_pair_eq (a a' : ZMod (4 * d)) : gmul d (a, 0) (a', 0) = (a * a', 0) := by
  ext <;> simp [gmul]

/-- `(x x̄)(y ȳ) = (xy)(x̄ȳ)` in the Gaussian residue ring. -/
lemma gmul_gsq_eq (x y : ZMod (4 * d) × ZMod (4 * d)) :
    gmul d (gmul d x (gconj d x)) (gmul d y (gconj d y))
      = gmul d (gmul d x y) (gmul d (gconj d x) (gconj d y)) := by
  ext <;> simp [gmul, gconj] <;> ring

/-- The norm form `x x̄` of a unit of the Gaussian residue ring is a unit of `ZMod (4d)`. -/
lemma isUnit_gsq_of_isUnitR {x : ZMod (4 * d) × ZMod (4 * d)} (h : IsUnitR d x) :
    IsUnit (gsq d x) := by
  obtain ⟨y, hy⟩ := h
  have hc : gmul d (gconj d x) (gconj d y) = gone d := by
    have := congrArg (gconj d) hy
    simpa [gconj_gmul, gconj_gone] using this
  have hxy : gmul d (gmul d x (gconj d x)) (gmul d y (gconj d y)) = gone d := by
    rw [gmul_gsq_eq, hy, hc, gmul_gone_left]
  have h2 : gmul d (gsq d x, 0) (gsq d y, 0) = gone d := by
    rw [← gmul_gconj x, ← gmul_gconj y]
    exact hxy
  have h3 := congrArg Prod.fst h2
  have h4 : gsq d x * gsq d y = 1 := by simpa [gmul_pair_eq, gone] using h3
  exact IsUnit.of_mul_eq_one (gsq d y) h4

/-- Conversely, a class whose norm form is a unit of `ZMod (4d)` is a unit of the Gaussian
residue ring. -/
lemma isUnitR_of_isUnit_gsq {x : ZMod (4 * d) × ZMod (4 * d)} (h : IsUnit (gsq d x)) :
    IsUnitR d x := by
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp h
  refine ⟨gmul d (c, 0) (gconj d x), ?_⟩
  have hcx : c * gsq d x = 1 := by rw [mul_comm c (gsq d x)]; exact hc
  calc gmul d x (gmul d (c, 0) (gconj d x))
      = gmul d (gmul d x (c, 0)) (gconj d x) := by rw [gmul_assoc]
    _ = gmul d (gmul d (c, 0) x) (gconj d x) := by rw [gmul_comm x (c, 0)]
    _ = gmul d (c, 0) (gmul d x (gconj d x)) := by rw [gmul_assoc]
    _ = gmul d (c, 0) (gsq d x, 0) := by rw [gmul_gconj]
    _ = gone d := by
        rw [gmul_pair_eq, hcx]
        ext <;> simp [gone]

lemma isUnit_gsq_iff_isUnitR (x : ZMod (4 * d) × ZMod (4 * d)) :
    IsUnit (gsq d x) ↔ IsUnitR d x :=
  ⟨isUnitR_of_isUnit_gsq, isUnit_gsq_of_isUnitR⟩

/-- The norm form of the class of `z` is the class of `|z|²`. -/
lemma gsq_gOfZI (z : GaussianInt) :
    gsq d (gOfZI d z) = ((Work.FIPlan.gnorm z : ℕ) : ZMod (4 * d)) := by
  have hm : (0 : ℤ) ≤ z.re * z.re - -1 * z.im * z.im := by
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hcast : ((Int.natAbs (z.re * z.re - -1 * z.im * z.im) : ℕ) : ZMod (4 * d))
      = ((z.re * z.re - -1 * z.im * z.im : ℤ) : ZMod (4 * d)) := by
    have := congrArg (fun k : ℤ => (k : ZMod (4 * d))) (Int.natAbs_of_nonneg hm)
    simpa using this
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm]
  rw [hcast]
  simp [gsq, gOfZI]
  ring

/-- **`IsUnitMod4d` is "the norm is a unit in `ℤ/(4d)`"**, one of the two directions. -/
lemma isUnitMod4d_of_isUnit_norm (z : GaussianInt)
    (h : IsUnit (((Work.FIPlan.gnorm z : ℕ)) : ZMod (4 * d))) : IsUnitMod4d d z := by
  have h1 : IsUnit (gsq d (gOfZI d z)) := by rwa [gsq_gOfZI]
  obtain ⟨y, hy⟩ := (isUnit_gsq_iff_isUnitR (d := d) (gOfZI d z)).mp h1
  refine ⟨zOfG d y, ?_⟩
  have h2 : gOfZI d (z * zOfG d y) = gOfZI d (1 : GaussianInt) := by
    rw [gOfZI_mul, gOfZI_zOfG, hy, gOfZI_one]
  exact dvd_of_gOfZI_eq h2

/-- **`IsUnitMod4d` is "the norm is a unit in `ℤ/(4d)`"**, the other direction. -/
lemma isUnit_norm_of_isUnitMod4d (z : GaussianInt) (h : IsUnitMod4d d z) :
    IsUnit (((Work.FIPlan.gnorm z : ℕ)) : ZMod (4 * d)) := by
  obtain ⟨w, hw⟩ := h
  have h1 : gmul d (gOfZI d z) (gOfZI d w) = gone d := by
    rw [← gOfZI_mul, gOfZI_eq_of_dvd hw, gOfZI_one]
  have h2 : IsUnitR d (gOfZI d z) := ⟨gOfZI d w, h1⟩
  have h3 : IsUnit (gsq d (gOfZI d z)) := isUnit_gsq_of_isUnitR h2
  rwa [gsq_gOfZI] at h3

/-- **The unit criterion of the residue ring**: `z` is invertible modulo `4d` exactly when its
norm is invertible modulo `4d`. -/
lemma isUnitMod4d_iff_isUnit_norm (z : GaussianInt) :
    IsUnitMod4d d z ↔ IsUnit (((Work.FIPlan.gnorm z : ℕ)) : ZMod (4 * d)) :=
  ⟨isUnit_norm_of_isUnitMod4d z, isUnitMod4d_of_isUnit_norm z⟩

/-- **The unit criterion, in coprimality form**: `z` is invertible modulo `4d` exactly when
`(|z|², 4d) = 1`. -/
lemma isUnitMod4d_iff_coprime (z : GaussianInt) :
    IsUnitMod4d d z ↔ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) := by
  rw [isUnitMod4d_iff_isUnit_norm]
  exact ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z) (4 * d)

end GaussUnit

/-! ## 2. The elementary API of `IsUnitMod4d` -/

namespace GaussUnit

open Work.FIArea5.S16Hecke (gmul gone gconj gsq gOfZI zOfG IsUnitR IsUnitMod4d)
open Work.FIArea5.S16Hecke.GaussBasic

variable {d : ℕ} [NeZero (4 * d)]

/-- `gnorm` is multiplicative. -/
lemma gnorm_mul' (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  show (z * w).norm.natAbs = z.norm.natAbs * w.norm.natAbs
  have h : (z * w).norm = z.norm * w.norm := by
    simp only [Zsqrtd.norm, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  rw [h, Int.natAbs_mul]

lemma gnorm_one' : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
  show (1 : GaussianInt).norm.natAbs = 1
  norm_num [Zsqrtd.norm]

lemma isUnitMod4d_one : IsUnitMod4d d 1 := by
  rw [isUnitMod4d_iff_isUnit_norm, gnorm_one']
  simpa using (isUnit_one : IsUnit (1 : ZMod (4 * d)))

lemma isUnitMod4d_mul {z w : GaussianInt} (hz : IsUnitMod4d d z) (hw : IsUnitMod4d d w) :
    IsUnitMod4d d (z * w) := by
  rw [isUnitMod4d_iff_isUnit_norm] at hz hw ⊢
  rw [gnorm_mul']
  push_cast
  exact hz.mul hw

lemma isUnitMod4d_of_mul_left {z w : GaussianInt} (h : IsUnitMod4d d (z * w)) :
    IsUnitMod4d d z := by
  rw [isUnitMod4d_iff_isUnit_norm] at h ⊢
  rw [gnorm_mul'] at h
  push_cast at h
  exact (IsUnit.mul_iff.mp h).1

lemma isUnitMod4d_of_mul_right {z w : GaussianInt} (h : IsUnitMod4d d (z * w)) :
    IsUnitMod4d d w := by
  rw [isUnitMod4d_iff_isUnit_norm] at h ⊢
  rw [gnorm_mul'] at h
  push_cast at h
  exact (IsUnit.mul_iff.mp h).2

/-- `4d` as an element of `ℤ[i]`. -/
abbrev fourD (d : ℕ) : GaussianInt := (((4 * d : ℕ) : ℤ) : GaussianInt)

/-- `IsUnitMod4d` only depends on the class modulo `4d`. -/
lemma isUnitMod4d_congr {z w : GaussianInt} (h : fourD d ∣ (z - w)) :
    IsUnitMod4d d z ↔ IsUnitMod4d d w := by
  have h2 : ((Work.FIPlan.gnorm z : ℕ) : ZMod (4 * d))
      = ((Work.FIPlan.gnorm w : ℕ) : ZMod (4 * d)) := by
    have h1 : gOfZI d z = gOfZI d w := gOfZI_eq_of_dvd h
    have h3 : gsq d (gOfZI d z) = gsq d (gOfZI d w) := by rw [h1]
    rwa [gsq_gOfZI, gsq_gOfZI] at h3
  rw [isUnitMod4d_iff_isUnit_norm, isUnitMod4d_iff_isUnit_norm, h2]

/-- A multiple of `4d` is not invertible modulo `4d` (`d ≥ 1`). -/
lemma not_isUnitMod4d_of_dvd {z : GaussianInt} (hd : 1 ≤ d) (h : fourD d ∣ z) :
    ¬ IsUnitMod4d d z := by
  intro hz
  rw [isUnitMod4d_iff_isUnit_norm] at hz
  rw [← gsq_gOfZI] at hz
  have hz0 : fourD d ∣ (z - 0) := by simpa using h
  have h0 : gsq d (gOfZI d z) = 0 := by
    rw [gOfZI_eq_of_dvd hz0]
    simp [gsq, gOfZI]
  rw [h0] at hz
  have h4 : Nat.Coprime 0 (4 * d) := (ZMod.isUnit_iff_coprime 0 (4 * d)).mp (by simpa using hz)
  rw [Nat.coprime_zero_left] at h4
  omega

end GaussUnit

/-! ## 3. The strict part of a character modulo `4d` -/

namespace GaussUnit

open Work.FIArea5.S16Hecke (IsUnitMod4d)

variable {d : ℕ}

/-- **The strict part of `χ`**: keep the values of `χ` on the units modulo `4d`, put `0` on all
other classes.  This is *the* canonical strict character agreeing with `χ` on the units, and (by
§4) agreeing with `χ` on the support of any coefficient of (4.13)+(5.13). -/
def strictPart (d : ℕ) (chi : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun z => if IsUnitMod4d d z then chi z else 0

lemma strictPart_of_unit {chi : GaussianInt → ℂ} {z : GaussianInt} (h : IsUnitMod4d d z) :
    strictPart d chi z = chi z := if_pos h

lemma strictPart_of_not_unit {chi : GaussianInt → ℂ} {z : GaussianInt}
    (h : ¬ IsUnitMod4d d z) : strictPart d chi z = 0 := if_neg h

/-- **The strict part of a character is a strict character.** -/
theorem strictPart_isCharMod4dStrict {d : ℕ} {chi : GaussianInt → ℂ}
    (hd : 1 ≤ d) (hchi : Work.FITop3.IsCharMod4d d chi) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d (strictPart d chi) := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [strictPart_of_unit isUnitMod4d_one, hchi.1]
  · intro z w
    by_cases hz : IsUnitMod4d d z
    · by_cases hw : IsUnitMod4d d w
      · rw [strictPart_of_unit (isUnitMod4d_mul hz hw), hchi.2.1 z w,
          strictPart_of_unit hz, strictPart_of_unit hw]
      · rw [strictPart_of_not_unit hw, mul_zero,
          strictPart_of_not_unit (fun h => hw (isUnitMod4d_of_mul_right h))]
    · rw [strictPart_of_not_unit hz, zero_mul,
          strictPart_of_not_unit (fun h => hz (isUnitMod4d_of_mul_left h))]
  · intro z
    by_cases hz : IsUnitMod4d d z
    · rw [strictPart_of_unit hz]; exact hchi.2.2.1 z
    · rw [strictPart_of_not_unit hz]; simp
  · intro z w h
    by_cases hz : IsUnitMod4d d z
    · rw [strictPart_of_unit hz, strictPart_of_unit ((isUnitMod4d_congr h).mp hz),
        hchi.2.2.2.1 z w h]
    · rw [strictPart_of_not_unit hz,
        strictPart_of_not_unit (fun h' => hz ((isUnitMod4d_congr h).mpr h'))]
  · intro z hz
    rw [strictPart_of_not_unit (not_isUnitMod4d_of_dvd hd hz)]
  · intro z hz
    exact strictPart_of_not_unit hz

end GaussUnit

/-! ## 4. Support points of a coefficient are units modulo `4d` -/

namespace GaussUnit

open Work.FIArea5.S16Hecke (IsUnitMod4d)

/-- **The arithmetic core of the reduction.**  If every prime divisor of `d` is `≤ Pz` — here in
the form `d ≤ Pz` together with `2 ≤ Pz` — then a Gaussian integer whose norm is free of primes
`≤ Pz` (the condition (5.8) of the paper, `Work.FITop3.NoSmallPrimes`) is a unit modulo `4d`:
any common prime of `z` and `4d` would produce a rational prime `≤ Pz` dividing `|z|²`. -/
theorem isUnitMod4d_of_noSmallPrimes {Pa : Work.FITop.Params} {d : ℕ} {z : GaussianInt}
    (hd1 : 1 ≤ d) (hdPz : d ≤ Pa.Pz) (hz : Work.FITop3.NoSmallPrimes Pa z) :
    IsUnitMod4d d z := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  rw [isUnitMod4d_iff_coprime]
  refine Nat.coprime_of_dvd fun q hq hqz hq4d => ?_
  have hqPz : q ≤ Pa.Pz := by
    rcases hq.dvd_mul.mp hq4d with h4 | hdd
    · have h4' : q ∣ 2 * 2 := h4
      have h2 : q ∣ 2 := by
        rcases hq.dvd_mul.mp h4' with h | h <;> exact h
      have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have h2le : 2 ≤ q := hq.two_le
      rw [le_antisymm hle h2le]
      exact Pa.hP2
    · exact le_trans (Nat.le_of_dvd (by omega) hdd) hdPz
  exact hz q hq hqPz hqz

end GaussUnit

/-! ## 5. The assembly of `Area5_6` from `S16Core` -/

open GaussUnit

/-- **The threshold bookkeeping of the reduction**, isolated so that the assembly below depends
only on its statement: for every `ε > 0` there is `X₀` such that for every datum with `x ≥ X₀`,
every `ν < 1/(2ε)` and every `d ≥ 1` with `d ≤ (log N)^ν`, every prime divisor of `4d` is `≤ Pz`
(in the form `d ≤ Pz`).  It is proved below as `d_le_Pz_of_log_bound`. -/
abbrev ThresholdBookkeeping : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X0 : ℝ,
    ∀ (Pa : Work.FITop.Params) (ν : ℝ) (d : ℕ),
      X0 ≤ (Pa.x : ℝ) → 0 < ν → ν < 1 / (2 * ε) → 1 ≤ d →
      (d : ℝ) ≤ (Real.log Pa.N) ^ ν → d ≤ Pa.Pz

/-- **The threshold bookkeeping: `d ≤ Pz`.**  *FI* §16 compares the conductor range
`d ≤ (log N)^ν` (`ν < 1/(2ε)`) with the small-prime cutoff (4.4) `(log log x)² ≤ log P ≤
log x (log log x)^{-2}`: the obstruction is (5.8), which only excludes primes `≤ P` from the
support of `β`, so the arithmetic core `isUnitMod4d_of_noSmallPrimes` needs the prime divisors of
`4d` — hence `d` itself — to be `≤ Pz`.

Chaining the range hypotheses,

  `log d ≤ ν log log N ≤ ν log log x ≤ (log log x)² ≤ log Pz`,

where the middle step uses `N < x^{1/2}(log x)^{-B} ≤ x` (`hNhi`, `hB`, `hx`) and the last
inequality uses `ν < 1/(2ε) ≤ log log x`.  The hypothesis `1/(2ε) ≤ log log x` is met as soon as
`x ≥ exp (exp (1/(2ε)))`, which is the threshold `X₀` below; the remaining case
`log N ≤ 1` is immediate from `1 ≤ d` and `(log N)^ν ≤ 1 ≤ Pz`.

(An independent proof of the same statement is `Work.FIArea6Hecke.le_Pz_of_log_bound`.) -/
theorem d_le_Pz_of_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ X0 : ℝ, ∀ (Pa : Work.FITop.Params) (ν : ℝ) (d : ℕ),
      X0 ≤ (Pa.x : ℝ) → 0 < ν → ν < 1 / (2 * ε) → 1 ≤ d →
      (d : ℝ) ≤ (Real.log Pa.N) ^ ν → d ≤ Pa.Pz := by
  refine ⟨Real.exp (Real.exp (1 / (2 * ε))), ?_⟩
  intro Pa ν d hX hν0 hνlt hd1 hdl
  have hXpos : 0 < Real.exp (Real.exp (1 / (2 * ε))) := Real.exp_pos _
  have hxpos : 0 < (Pa.x : ℝ) := lt_of_lt_of_le hXpos hX
  have hlogx : Real.exp (1 / (2 * ε)) ≤ Real.log (Pa.x : ℝ) := by
    have := Real.log_le_log hXpos hX
    rwa [Real.log_exp] at this
  have hllx : 1 / (2 * ε) ≤ Real.log (Real.log (Pa.x : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos (1 / (2 * ε))) hlogx
    rwa [Real.log_exp] at this
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlogx1 : 1 ≤ Real.log (Pa.x : ℝ) := by
    have := (Real.log_le_log_iff (Real.exp_pos 1) hxpos).mpr
      (le_trans (le_of_lt Real.exp_one_lt_three) hx3)
    rwa [Real.log_exp] at this
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hNpos : 0 < (Pa.N : ℝ) := by linarith
  have hlogN0 : 0 ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg hN1
  have hlogNx : Real.log (Pa.N : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have hpow : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlogx1 (by linarith [Pa.hB])
    have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) := by
      have h3 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) ≤ (Pa.x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      rw [Real.rpow_one] at h3
      nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (Pa.x : ℝ)) ((1 : ℝ) / 2)]
    exact Real.log_le_log hNpos (le_trans (le_of_lt Pa.hNhi) h2)
  have hPz2 : (2 : ℝ) ≤ (Pa.Pz : ℝ) := by exact_mod_cast Pa.hP2
  have hPzpos : 0 < (Pa.Pz : ℝ) := by linarith
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd1
  by_cases hcase : Real.log (Pa.N : ℝ) ≤ 1
  · have h1 : (Real.log (Pa.N : ℝ)) ^ ν ≤ 1 := Real.rpow_le_one hlogN0 hcase (le_of_lt hν0)
    exact_mod_cast le_trans (le_trans hdl h1) (by linarith : (1 : ℝ) ≤ (Pa.Pz : ℝ))
  · have hLpos : 0 < Real.log (Pa.N : ℝ) := lt_trans zero_lt_one (not_le.mp hcase)
    have hlogd : Real.log (d : ℝ) ≤ ν * Real.log (Real.log (Pa.N : ℝ)) := by
      have h1 : Real.log (d : ℝ) ≤ Real.log ((Real.log (Pa.N : ℝ)) ^ ν) :=
        Real.log_le_log hdpos hdl
      rwa [Real.log_rpow hLpos ν] at h1
    have hloglog_le : Real.log (Real.log (Pa.N : ℝ)) ≤ Real.log (Real.log (Pa.x : ℝ)) :=
      Real.log_le_log hLpos hlogNx
    have hν_le : ν ≤ Real.log (Real.log (Pa.x : ℝ)) :=
      le_of_lt (lt_of_lt_of_le hνlt hllx)
    have hs0 : 0 ≤ Real.log (Real.log (Pa.x : ℝ)) :=
      le_trans (le_of_lt (by positivity : 0 < 1 / (2 * ε))) hllx
    have hstep1 : ν * Real.log (Real.log (Pa.N : ℝ))
        ≤ ν * Real.log (Real.log (Pa.x : ℝ)) :=
      mul_le_mul_of_nonneg_left hloglog_le (le_of_lt hν0)
    have hstep2 : ν * Real.log (Real.log (Pa.x : ℝ))
        ≤ (Real.log (Real.log (Pa.x : ℝ))) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hν_le hs0
      simpa [pow_two] using this
    have hfinal : Real.log (d : ℝ) ≤ Real.log (Pa.Pz : ℝ) :=
      le_trans hlogd (le_trans hstep1 (le_trans hstep2 Pa.hPlo))
    exact_mod_cast (Real.log_le_log_iff hdpos hPzpos).mp hfinal

/-- **The reduction `S16Core → Area5_6`**, assembled from the strict-character form of *FI*
Lemma 16.2 and the threshold bookkeeping.

The two statements differ in exactly one place: `S16Core` asks for `IsCharMod4dStrict d χ`, while
`Area5_6` asks for `IsCharMod4d d χ`.  That difference is removed by replacing `χ` by its strict
part `χ̃ z = if z ∈ (ℤ[i]/4d)^* then χ z else 0`: for a support point `z` of `β`, `z` is free of
primes `≤ Pz` while every prime divisor of `4d` is `≤ Pz`, so `(|z|², 4d) = 1` and `z` *is* a unit
modulo `4d` (`isUnitMod4d_of_noSmallPrimes`); hence `β_z χ(z) = β_z χ̃(z)` for every `z`, the two
sums coincide, and `χ̃` is a strict character (`strictPart_isCharMod4dStrict`).

Since `S16Core` and `Area5_6` carry the same constants (`cε` in both exponentials and as the
prefactor, and the same `(4d)N(log N)^6`), the remaining bookkeeping is the threshold
`max x₀ X₀`. -/
theorem area5_6_of_threshold (h : Work.FITop4.Bridge.S16Core)
    (hthr : ThresholdBookkeeping) : Work.FITop4.Area5_6 := by
  intro ε hε0 hε4
  obtain ⟨cε, x0, hcε, hS16⟩ := h ε hε0 hε4
  obtain ⟨X0, hX0⟩ := hthr ε hε0
  refine ⟨cε, max x0 X0, hcε, ?_⟩
  intro Pa hx φ ν z0 d k chi hν0 hνlt hd1 hdl hk hchi β hβ
  have hx0 : x0 ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hX : X0 ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have hdPz : d ≤ Pa.Pz := hX0 Pa ν d hX hν0 hνlt hd1 hdl
  have hψ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d (strictPart d chi) :=
    strictPart_isCharMod4dStrict hd1 hchi
  have key := hS16 Pa hx0 φ ν z0 d k (strictPart d chi) hν0 hνlt hd1 hdl hk hψ β hβ
  have heq : (∑ z ∈ Work.FITop.boxN Pa,
        β z * strictPart d chi z *
          (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k)
      = ∑ z ∈ Work.FITop.boxN Pa,
        β z * chi z * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hb : β z = 0
    · simp [hb]
    · have hunit : Work.FIArea5.S16Hecke.IsUnitMod4d d z :=
        isUnitMod4d_of_noSmallPrimes hd1 hdPz (hβ.noSmallPrimes hb)
      rw [strictPart_of_unit hunit]
  rw [heq] at key
  exact key

/-- **`Area5_6` from `S16Core`** (*FI* Lemma 16.2 at the round-6 hypotheses, for *all*
characters of modulus `4d`): the strict character case `S16Core` plus the threshold bookkeeping
`d_le_Pz_of_log_bound`. -/
theorem area5_6_of_S16Core (h : Work.FITop4.Bridge.S16Core) : Work.FITop4.Area5_6 := by
  apply area5_6_of_threshold h
  intro ε hε
  exact d_le_Pz_of_log_bound ε hε

end

end Work.FIArea6Hecke
