import Mathlib
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15red.ClassFactorCS
import Submission.Work.FIArea4.S15red.gcd_re_eq_of_delta
import Submission.Work.FIArea4.S15pDngAux
import Submission.Work.FIArea4.S15theta_phase_factor
import Submission.Work.FIArea4.S15box

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.S15red

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace SSE

/-! ## 0. Divisor bookkeeping -/

lemma one_le_of_mem_divisors {d e : ℕ} (he : e ∈ d.divisors) : 1 ≤ e :=
  Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (Nat.pos_of_ne_zero (Nat.mem_divisors.mp he).2)

lemma dvd_of_mem_divisors {d e : ℕ} (he : e ∈ d.divisors) : e ∣ d := (Nat.mem_divisors.mp he).1

/-! ## 1. Arithmetic of the change of variables `z = e·Re w + i·Im w` -/

lemma Delta_scalePt (e : ℕ) (w1 w2 : GaussianInt) :
    Work.FIPlan.Delta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
      = (e : ℤ) * Work.FIPlan.Delta w1 w2 := by
  simp only [Work.FIArea4.scalePt, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star,
    Work.FIPlan.Delta]
  ring

lemma absDelta_scalePt (e : ℕ) (w1 w2 : GaussianInt) :
    Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
      = e * Work.FIPlan.absDelta w1 w2 := by
  unfold Work.FIPlan.absDelta
  rw [Delta_scalePt, Int.natAbs_mul]
  simp

lemma re_star_scalePt (e : ℕ) (w1 w2 : GaussianInt) :
    (star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re
      = (e : ℤ) ^ 2 * w1.re * w2.re + w1.im * w2.im := by
  simp only [Work.FIArea4.scalePt, Zsqrtd.star_mk, Zsqrtd.re_mul]
  ring

lemma gcd_scalePt_re {d e : ℕ} (hed : e ∣ d) (ρ : ℤ) :
    Nat.gcd d ((e : ℤ) * ρ).natAbs = e * Nat.gcd (d / e) ρ.natAbs := by
  have hd : d = e * (d / e) := by rw [mul_comm]; exact (Nat.div_mul_cancel hed).symm
  have h1 : ((e : ℤ) * ρ).natAbs = e * ρ.natAbs := by rw [Int.natAbs_mul]; simp
  rw [h1]
  conv_lhs => rw [hd]
  rw [Nat.gcd_mul_left]

lemma coprime_of_gcd_scalePt {d e : ℕ} (he : 1 ≤ e) (hed : e ∣ d) {ρ : ℤ}
    (h : Nat.gcd d ((e : ℤ) * ρ).natAbs = e) : Nat.Coprime ρ.natAbs (d / e) := by
  rw [gcd_scalePt_re hed ρ] at h
  have h2 : e * Nat.gcd (d / e) ρ.natAbs = e * 1 := by rw [mul_one]; exact h
  have h3 : Nat.gcd (d / e) ρ.natAbs = 1 := Nat.eq_of_mul_eq_mul_left (by omega) h2
  rw [Nat.Coprime, Nat.gcd_comm]
  exact h3

lemma gcd_scalePt_of_coprime {d e : ℕ} (hed : e ∣ d) {ρ : ℤ}
    (h : Nat.Coprime ρ.natAbs (d / e)) : Nat.gcd d ((e : ℤ) * ρ).natAbs = e := by
  rw [gcd_scalePt_re hed ρ]
  have h3 : Nat.gcd (d / e) ρ.natAbs = 1 := by rw [Nat.gcd_comm]; exact h
  rw [h3, mul_one]

lemma four_mul_dvd_iff {d e A : ℕ} (he : 1 ≤ e) (hed : e ∣ d) :
    4 * d ∣ e * A ↔ 4 * (d / e) ∣ A := by
  have hd : 4 * d = e * (4 * (d / e)) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hed]
    ring
  rw [hd, Nat.mul_dvd_mul_iff_left (by omega : 0 < e)]

/-! ## 2. Membership in the box -/

lemma abs_le_of_mem_Icc' {R : ℤ} {z : ℤ} (hz : z ∈ Finset.Icc (-R) R) : |z| ≤ R := by
  rw [Finset.mem_Icc] at hz
  exact abs_le.mpr ⟨hz.1, hz.2⟩

lemma unscalePt_mem_boxN (Pa : Work.FITop.Params) {e : ℕ} {z : GaussianInt}
    (hz : z ∈ Work.FITop.boxN Pa) : Work.FIArea4.unscalePt e z ∈ Work.FITop.boxN Pa := by
  rw [Work.FIArea4.mem_boxN] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [Work.FIArea4.unscalePt_re, Finset.mem_Icc]
    have h : |z.re / (e : ℤ)| ≤ |z.re| := Int.abs_ediv_le_abs z.re (e : ℤ)
    have h2 : |z.re| ≤ Work.FITop.radN Pa := abs_le_of_mem_Icc' hz.1
    exact abs_le.mp (le_trans h h2)
  · rw [Work.FIArea4.unscalePt_im]; exact hz.2

lemma re_sq_le_gnorm (z : GaussianInt) : z.re.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
  rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq]
  exact Nat.le_add_right _ _

lemma im_sq_le_gnorm (z : GaussianInt) : z.im.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
  rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq]
  exact Nat.le_add_left _ _

/-- A point of the polar box (5.14) lies in the box `boxN`. -/
lemma mem_boxN_of_polar (Pa : Work.FITop.Params) {φ : ℝ} {z : GaussianInt}
    (hz : Work.FITop3.InPolarBox Pa φ z) : z ∈ Work.FITop.boxN Pa := by
  have hθ : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hz.2.2.1
  have hgn2 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N :=
    le_trans hgn (mul_le_mul_of_nonneg_right (by linarith [hθ]) hN0)
  set R : ℕ := ⌈Real.sqrt (4 * Pa.N)⌉₊ with hRdef
  have hRZ : Work.FITop.radN Pa = (R : ℤ) := by rw [Work.FITop.radN, hRdef]
  have hsq_le : ((z.re.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
    exact_mod_cast re_sq_le_gnorm z
  have hsq_le_im : ((z.im.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
    exact_mod_cast im_sq_le_gnorm z
  have hsqrt : Real.sqrt (Work.FIPlan.gnorm z : ℝ) ≤ (R : ℝ) := by
    have h1 : Real.sqrt (Work.FIPlan.gnorm z : ℝ) ≤ Real.sqrt (2 * Pa.N) := Real.sqrt_le_sqrt hgn2
    have h2 : Real.sqrt (2 * Pa.N) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.sqrt (4 * Pa.N) ≤ (R : ℝ) := by rw [hRdef]; exact Nat.le_ceil _
    linarith
  have hb (c : ℤ) (hc : ((c.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ)) :
      c ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa) := by
    rw [hRZ, Finset.mem_Icc]
    have h1 : (c.natAbs : ℝ) ≤ (R : ℝ) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
      exact le_trans (Real.sqrt_le_sqrt hc) hsqrt
    have h2 : c.natAbs ≤ R := by exact_mod_cast h1
    have habs : |c| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
    exact abs_le.mp habs
  rw [Work.FIArea4.mem_boxN]
  exact ⟨hb z.re hsq_le, hb z.im hsq_le_im⟩

/-- On the support of an `IsBoxCoeff`, `β` vanishes outside the box `boxN`. -/
lemma eq_zero_of_not_mem_boxN (Pa : Work.FITop.Params) {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBoxCoeff Pa φ β) {z : GaussianInt} (hz : z ∉ Work.FITop.boxN Pa) :
    β z = 0 := by
  by_contra h
  exact hz (mem_boxN_of_polar Pa (hβ.2 z h).1)

/-! ## 3. Primitivity of the stratum points -/

lemma odd_re_of_prim {e : ℕ} {β : GaussianInt → ℂ}
    (hβ : ∀ z : GaussianInt, β z ≠ 0 → Nat.Coprime z.re.natAbs (2 * z.im.natAbs))
    {w : GaussianInt} (hb : β (Work.FIArea4.scalePt e w) ≠ 0) : Odd w.re := by
  have h := hβ (Work.FIArea4.scalePt e w) hb
  rw [Work.FIArea4.scalePt_re, Work.FIArea4.scalePt_im, Int.natAbs_mul] at h
  have h3 : Nat.Coprime (((e : ℤ).natAbs) * w.re.natAbs) 2 :=
    h.coprime_dvd_right (dvd_mul_right 2 (w.im.natAbs))
  have h2 : Nat.Coprime w.re.natAbs 2 :=
    h3.coprime_dvd_left (dvd_mul_left w.re.natAbs ((e : ℤ).natAbs))
  exact Int.natAbs_odd.mp (Nat.coprime_two_right.mp h2)

lemma coprime_four_mul_of_guard {e d : ℕ} {β : GaussianInt → ℂ}
    (hβ : ∀ z : GaussianInt, β z ≠ 0 → Nat.Coprime z.re.natAbs (2 * z.im.natAbs))
    {w : GaussianInt} (hb : β (Work.FIArea4.scalePt e w) ≠ 0)
    (hg : Nat.Coprime w.re.natAbs (d / e)) :
    Nat.Coprime w.re.natAbs (4 * (d / e)) := by
  have hodd := odd_re_of_prim hβ hb
  have h2 : Nat.Coprime w.re.natAbs 2 := Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hodd)
  have h4 : Nat.Coprime w.re.natAbs (2 * 2) := h2.mul_right h2
  simpa using h4.mul_right hg

/-! ## 4. Jacobi symbol of the odd part -/

lemma jacobiSym_two_eq_one_of_odd_int (a : ℤ) (ha : Odd a) : jacobiSym a 2 = 1 := by
  have h2 : (a : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (2 : ZMod 2) = 0 := by decide
    rw [hz, zero_mul, zero_add]
  rw [(jacobiSym.legendreSym.to_jacobiSym 2 a).symm, legendreSym]
  simp [h2]

lemma jacobiSym_two_pow_eq_one_of_odd_int (a : ℤ) (e : ℕ) (ha : Odd a) :
    jacobiSym a (2 ^ e) = 1 := by
  rw [jacobiSym.pow_right, jacobiSym_two_eq_one_of_odd_int a ha, one_pow]

lemma jacobiSym_odd_eq_oddPart (a : ℤ) (d : ℕ) (ha : Odd a) :
    jacobiSym a d = jacobiSym a (Work.FIPlan.oddPart d) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp [Work.FIPlan.oddPart]
  · rw [Work.FIPlan.oddPart]
    have hdvd : 2 ^ d.factorization 2 ∣ d := Nat.ordProj_dvd d 2
    have hsplit : 2 ^ d.factorization 2 * (d / 2 ^ d.factorization 2) = d :=
      Nat.mul_div_cancel' hdvd
    have hpos : 0 < d / 2 ^ d.factorization 2 :=
      Nat.div_pos (Nat.le_of_dvd h hdvd) (by positivity)
    haveI : NeZero (d / 2 ^ d.factorization 2) := ⟨by omega⟩
    haveI : NeZero (2 ^ d.factorization 2) := ⟨by positivity⟩
    calc jacobiSym a d
        = jacobiSym a (2 ^ d.factorization 2 * (d / 2 ^ d.factorization 2)) := by rw [hsplit]
      _ = jacobiSym a (2 ^ d.factorization 2) * jacobiSym a (d / 2 ^ d.factorization 2) :=
          jacobiSym.mul_right a _ _
      _ = jacobiSym a (d / 2 ^ d.factorization 2) := by
          rw [jacobiSym_two_pow_eq_one_of_odd_int a _ ha, one_mul]

lemma jwG_four_mul (d' : ℕ) (ρ : ℤ) (hρ : Odd ρ) :
    Work.FIArea4.jwG (4 * d') ρ = (((jacobiSym ρ d' : ℤ)) : ℂ) := by
  unfold Work.FIArea4.jwG
  have h1 : jacobiSym ρ (4 * d') = jacobiSym ρ d' := by
    by_cases hd' : d' = 0
    · subst hd'; simp
    · rw [show (4 * d' : ℕ) = 2 ^ 2 * d' by norm_num,
        jacobiSym.mul_right' ρ (by norm_num) hd',
        jacobiSym_two_pow_eq_one_of_odd_int ρ 2 hρ, one_mul]
  have h2 : jacobiSym ρ (Work.FIPlan.oddPart (4 * d')) = jacobiSym ρ (4 * d') :=
    (jacobiSym_odd_eq_oddPart ρ (4 * d') hρ).symm
  rw [h2, h1]

/-! ## 5. The `e`-factorisation of the Jacobi symbol -/

lemma jacobiSym_congr {a b : ℤ} {c : ℕ} (h : (c : ℤ) ∣ a - b) : jacobiSym a c = jacobiSym b c := by
  apply jacobiSym.mod_left'
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact (Int.dvd_iff_emod_eq_zero).mp h

lemma jacobiSym_factor (e d' a : ℕ) (r1 s1 r2 s2 : ℤ) (he : e ≠ 0) (hd' : d' ≠ 0)
    (h1 : (4 * d' : ℤ) ∣ (s1 - (a : ℤ) * r1)) (h2 : (4 * d' : ℤ) ∣ (s2 - (a : ℤ) * r2)) :
    jacobiSym ((e : ℤ) ^ 2 * r1 * r2 + s1 * s2) (e * d')
      = jacobiSym ((e : ℤ) ^ 2 + (a : ℤ) ^ 2) d' * jacobiSym s1 e * jacobiSym s2 e
        * jacobiSym r1 d' * jacobiSym r2 d' := by
  have h1e : (e : ℤ) ∣ ((e : ℤ) ^ 2 * r1 * r2 + s1 * s2) - s1 * s2 := ⟨(e : ℤ) * r1 * r2, by ring⟩
  have hd1 : (d' : ℤ) ∣ (s1 - (a : ℤ) * r1) :=
    dvd_trans (show (d' : ℤ) ∣ 4 * (d' : ℤ) from ⟨4, by ring⟩) h1
  have hd2 : (d' : ℤ) ∣ (s2 - (a : ℤ) * r2) :=
    dvd_trans (show (d' : ℤ) ∣ 4 * (d' : ℤ) from ⟨4, by ring⟩) h2
  have h1d : (d' : ℤ) ∣ ((e : ℤ) ^ 2 * r1 * r2 + s1 * s2) - ((e : ℤ) ^ 2 + (a : ℤ) ^ 2) * r1 * r2 := by
    have hh : (d' : ℤ) ∣ (s1 - (a : ℤ) * r1) * s2 + ((a : ℤ) * r1) * (s2 - (a : ℤ) * r2) :=
      dvd_add (hd1.mul_right s2) (hd2.mul_left ((a : ℤ) * r1))
    rwa [show (s1 - (a : ℤ) * r1) * s2 + ((a : ℤ) * r1) * (s2 - (a : ℤ) * r2)
        = ((e : ℤ) ^ 2 * r1 * r2 + s1 * s2) - ((e : ℤ) ^ 2 + (a : ℤ) ^ 2) * r1 * r2 by ring] at hh
  rw [jacobiSym.mul_right' _ he hd', jacobiSym_congr h1e, jacobiSym_congr h1d,
      jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left]
  ac_rfl

/-! ## 6. Congruences modulo the class modulus -/

lemma delta_zmod_eq_zero_of_dvd_absDelta {m : ℕ} {w1 w2 : GaussianInt}
    (h : m ∣ Work.FIPlan.absDelta w1 w2) : (Work.FIPlan.Delta w1 w2 : ZMod m) = 0 := by
  have h2 : ((m : ℕ) : ℤ) ∣ (((Work.FIPlan.Delta w1 w2).natAbs : ℕ) : ℤ) := by
    rw [← Work.FIPlan.absDelta]
    exact_mod_cast h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Work.FIPlan.Delta w1 w2) m).mpr
    (Int.dvd_natAbs.mp h2)

lemma cls_res_eq_of_delta {m : ℕ} {w1 w2 : GaussianInt}
    (h1 : Nat.Coprime w1.re.natAbs m) (h2 : Nat.Coprime w2.re.natAbs m)
    (hΔ : (Work.FIPlan.Delta w1 w2 : ZMod m) = 0) :
    (w2.im : ZMod m) * ((w2.re : ZMod m))⁻¹
      = (w1.im : ZMod m) * ((w1.re : ZMod m))⁻¹ := by
  have hu1 := Work.FIArea4.isUnit_intCast_zmod' m w1.re h1
  have hu2 := Work.FIArea4.isUnit_intCast_zmod' m w2.re h2
  have e1 : ((w1.re : ZMod m))⁻¹ * (w1.re : ZMod m) = 1 := ZMod.inv_mul_of_unit _ hu1
  have e2 : ((w2.re : ZMod m))⁻¹ * (w2.re : ZMod m) = 1 := ZMod.inv_mul_of_unit _ hu2
  have e2' : (w2.re : ZMod m) * ((w2.re : ZMod m))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu2
  have hD : ((Work.FIPlan.Delta w1 w2 : ℤ) : ZMod m)
      = (w1.re : ZMod m) * (w2.im : ZMod m) - (w2.re : ZMod m) * (w1.im : ZMod m) := by
    rw [Work.FIArea4.Delta_eq]; push_cast; ring
  have hrel : (w1.re : ZMod m) * (w2.im : ZMod m) = (w2.re : ZMod m) * (w1.im : ZMod m) := by
    have h := hΔ
    rw [hD, sub_eq_zero] at h
    exact h
  calc (w2.im : ZMod m) * ((w2.re : ZMod m))⁻¹
      = ((w1.re : ZMod m))⁻¹
          * ((w1.re : ZMod m) * ((w2.im : ZMod m) * ((w2.re : ZMod m))⁻¹)) := by
        rw [← mul_assoc, e1, one_mul]
    _ = ((w1.re : ZMod m))⁻¹ * (((w1.re : ZMod m) * (w2.im : ZMod m)) * ((w2.re : ZMod m))⁻¹) := by
        ring
    _ = ((w1.re : ZMod m))⁻¹ * (((w2.re : ZMod m) * (w1.im : ZMod m)) * ((w2.re : ZMod m))⁻¹) := by
        rw [hrel]
    _ = ((w1.re : ZMod m))⁻¹ * ((w1.im : ZMod m) * ((w2.re : ZMod m) * ((w2.re : ZMod m))⁻¹)) := by
        ring
    _ = (w1.im : ZMod m) * ((w1.re : ZMod m))⁻¹ := by
        rw [e2', mul_one]
        ring

/-! ## 7. The separated summand and its factorisation -/

/-- The single summand of the `§15` pair sum, separated into the `d`-factor, the Jacobi symbol
and the angular/phase factor. -/
def ssTerm (X j d : ℕ) (u t : ℝ) (ℓ : ℤ) (z1 z2 : GaussianInt) : ℂ :=
  ((((Nat.totient d : ℝ) / (d : ℝ) : ℝ)) : ℂ)
    * (((jacobiSym ((star z1 * z2).re) d : ℤ)) : ℂ)
    * (Work.FIArea4.S15theta ℓ z1 z2 * Work.FIArea4.S15phase X j u t ((z1, z2), d))

lemma summand_eq (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) (z1 z2 : GaussianInt) :
    Work.FIArea4.S15coef β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
      * Work.FIArea4.S15phase X j u t ((z1, z2), d)
    = 2 * (β z1 * star (β z2)) * ssTerm X j d u t ℓ z1 z2 := by
  unfold Work.FIArea4.S15coef Work.FIArea4.S15w ssTerm
  ring

/-- The `d`-only factor `(4X2^jd)^{-it}` of the phase. -/
def ssD (X j d : ℕ) (t : ℝ) : ℂ :=
  (((((4 : ℝ) * (X : ℝ) * (2 : ℝ) ^ j * (d : ℝ)) : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))

/-- The pair-independent constant `(φ(d)/d)·(4X2^jd)^{-it}`. -/
def ssConst (X j d : ℕ) (t : ℝ) : ℂ :=
  ((((Nat.totient d : ℝ) / (d : ℝ) : ℝ)) : ℂ) * ssD X j d t

/-- The class factor `(e²+a² | d')`. -/
def ssFac (e d' : ℕ) (a : ZMod (4 * d')) : ℂ :=
  (((jacobiSym ((e : ℤ) ^ 2 + ((a.val : ℤ)) ^ 2) d' : ℤ)) : ℂ)

/-- The `z₁`-array of the `(d,e)`-stratum. -/
def ssArrA (e d' : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (w : GaussianInt) : ℂ :=
  β (Work.FIArea4.scalePt e w) * Work.FIArea4.S15zf u t ℓ (Work.FIArea4.scalePt e w)
    * ((jacobiSym w.im e : ℤ) : ℂ) * ((jacobiSym w.re d' : ℤ) : ℂ)

/-- The `z₂`-array of the `(d,e)`-stratum (with the `star` absorbed). -/
def ssArrB (e d' : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (w : GaussianInt) : ℂ :=
  star (β (Work.FIArea4.scalePt e w) * Work.FIArea4.S15zfV u t ℓ (Work.FIArea4.scalePt e w))
    * ((jacobiSym w.im e : ℤ) : ℂ) * ((jacobiSym w.re d' : ℤ) : ℂ)

/-- The `z₁`-array of the stratum, read against the variance `EvarG` (i.e. truncated to the points
whose real part is coprime to the class modulus `4d'`). -/
def ssU (Pa : Work.FITop.Params) (e d' : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ)
    (w : GaussianInt) : ℂ :=
  if Nat.Coprime w.re.natAbs (4 * d') then
    Work.FIArea4.S15strU β u t ℓ e w * Work.FIArea4.jwG (4 * d') w.re else 0

/-- The `z₂`-array of the stratum, read against the variance `EvarG`. -/
def ssV (Pa : Work.FITop.Params) (e d' : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ)
    (w : GaussianInt) : ℂ :=
  if Nat.Coprime w.re.natAbs (4 * d') then
    Work.FIArea4.S15strV β u t ℓ e w * Work.FIArea4.jwG (4 * d') w.re else 0

lemma ssU_eq_ssArrA {Pa : Work.FITop.Params} {e d' : ℕ} {β : GaussianInt → ℂ} {u t : ℝ} {ℓ : ℤ}
    {w : GaussianInt} (hodd : Odd w.re) (hc : Nat.Coprime w.re.natAbs d') :
    ssU Pa e d' β u t ℓ w = ssArrA e d' β u t ℓ w := by
  have h2 : Nat.Coprime w.re.natAbs 2 := Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hodd)
  have hc4 : Nat.Coprime w.re.natAbs (4 * d') := by
    have h4 : Nat.Coprime w.re.natAbs (2 * 2) := h2.mul_right h2
    simpa using h4.mul_right hc
  rw [ssU, if_pos hc4, ssArrA, jwG_four_mul d' w.re hodd]
  simp only [Work.FIArea4.S15strU, Work.FIArea4.scalePt]
  ring

lemma ssV_eq_ssArrB {Pa : Work.FITop.Params} {e d' : ℕ} {β : GaussianInt → ℂ} {u t : ℝ} {ℓ : ℤ}
    {w : GaussianInt} (hodd : Odd w.re) (hc : Nat.Coprime w.re.natAbs d') :
    star (ssV Pa e d' β u t ℓ w) = ssArrB e d' β u t ℓ w := by
  have h2 : Nat.Coprime w.re.natAbs 2 := Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hodd)
  have hc4 : Nat.Coprime w.re.natAbs (4 * d') := by
    have h4 : Nat.Coprime w.re.natAbs (2 * 2) := h2.mul_right h2
    simpa using h4.mul_right hc
  rw [ssV, if_pos hc4, ssArrB]
  rw [star_mul, star_mul, jwG_four_mul d' w.re hodd]
  simp only [Work.FIArea4.S15strV, Work.FIArea4.scalePt, star_mul, star_intCast]
  ring

/-- `csEvG` only depends on the values of the array at the points with `(Re z, m) = 1`. -/
lemma csEvG_congr {R : ℤ} {m : ℕ} {u u' : GaussianInt → ℂ}
    (h : ∀ z : GaussianInt, Nat.Coprime z.re.natAbs m → u z = u' z) :
    StrCS.csEvG R m u = StrCS.csEvG R m u' := by
  unfold StrCS.csEvG StrCS.csClsSum2
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun z hz => ?_)
  exact h z (StrCS.mem_csClsF.mp hz).2.1

/-- **The pointwise factorisation of the `(d,e)`-stratum summand.** -/
lemma ssFactor (X j d e : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) (hed : e ∣ d)
    (u t : ℝ) (ℓ : ℤ) (β : GaussianInt → ℂ)
    (hβ : ∀ z : GaussianInt, β z ≠ 0 → Nat.Coprime z.re.natAbs (2 * z.im.natAbs))
    {w1 w2 : GaussianInt} (hb1 : β (Work.FIArea4.scalePt e w1) ≠ 0)
    (hb2 : β (Work.FIArea4.scalePt e w2) ≠ 0)
    (hc1 : Nat.Coprime w1.re.natAbs (d / e)) (hc2 : Nat.Coprime w2.re.natAbs (d / e))
    (h4 : 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2) :
    β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2))
        * ssTerm X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
      = ssConst X j d t
          * ssFac e (d / e)
              ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)
          * (ssArrA e (d / e) β u t ℓ w1 * ssArrB e (d / e) β u t ℓ w2) := by
  classical
  have he0 : e ≠ 0 := by omega
  have hd_eq : d = e * (d / e) := by rw [mul_comm]; exact (Nat.div_mul_cancel hed).symm
  have hd'0 : d / e ≠ 0 := by
    intro h
    have h1 : d = 0 := by rw [hd_eq, h, mul_zero]
    omega
  have hc1' : Nat.Coprime w1.re.natAbs (4 * (d / e)) := coprime_four_mul_of_guard hβ hb1 hc1
  have hc2' : Nat.Coprime w2.re.natAbs (4 * (d / e)) := coprime_four_mul_of_guard hβ hb2 hc2
  haveI : NeZero (4 * (d / e)) := ⟨by omega⟩
  have hΔ0 : (Work.FIPlan.Delta w1 w2 : ZMod (4 * (d / e))) = 0 :=
    delta_zmod_eq_zero_of_dvd_absDelta h4
  have hcls := cls_res_eq_of_delta hc1' hc2' hΔ0
  set c : ZMod (4 * (d / e)) :=
    (w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹ with hcdef
  set a : ℕ := c.val with hadef
  have hac : (a : ZMod (4 * (d / e))) = c := ZMod.natCast_zmod_val c
  have hunit1 : IsUnit ((w1.re : ZMod (4 * (d / e)))) :=
    Work.FIArea4.isUnit_intCast_zmod' _ w1.re hc1'
  have hinv1 : ((w1.re : ZMod (4 * (d / e))))⁻¹ * (w1.re : ZMod (4 * (d / e))) = 1 :=
    ZMod.inv_mul_of_unit _ hunit1
  have hunit2 : IsUnit ((w2.re : ZMod (4 * (d / e)))) :=
    Work.FIArea4.isUnit_intCast_zmod' _ w2.re hc2'
  have hinv2 : ((w2.re : ZMod (4 * (d / e))))⁻¹ * (w2.re : ZMod (4 * (d / e))) = 1 :=
    ZMod.inv_mul_of_unit _ hunit2
  have ha1 : (w1.im : ZMod (4 * (d / e)))
      = (a : ZMod (4 * (d / e))) * (w1.re : ZMod (4 * (d / e))) := by
    rw [hac, hcdef, mul_assoc, hinv1, mul_one]
  have ha2 : (w2.im : ZMod (4 * (d / e)))
      = (a : ZMod (4 * (d / e))) * (w2.re : ZMod (4 * (d / e))) := by
    rw [hac, ← hcls, mul_assoc, hinv2, mul_one]
  have hdvd1 : (4 * (d / e) : ℤ) ∣ (w1.im - (a : ℤ) * w1.re) := by
    have h1' : ((w1.im : ℤ) : ZMod (4 * (d / e)))
        = (((a : ℤ) * w1.re : ℤ) : ZMod (4 * (d / e))) := by
      rw [show (((a : ℤ) * w1.re : ℤ) : ZMod (4 * (d / e)))
          = (a : ZMod (4 * (d / e))) * (w1.re : ZMod (4 * (d / e))) by push_cast; ring]
      exact ha1
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (w1.im : ℤ) ((a : ℤ) * w1.re)
      (4 * (d / e))).mp h1'
    have h3 : (4 * (d / e) : ℤ) ∣ -(((a : ℤ) * w1.re) - w1.im) := dvd_neg.mpr h2
    rwa [neg_sub] at h3
  have hdvd2 : (4 * (d / e) : ℤ) ∣ (w2.im - (a : ℤ) * w2.re) := by
    have h1' : ((w2.im : ℤ) : ZMod (4 * (d / e)))
        = (((a : ℤ) * w2.re : ℤ) : ZMod (4 * (d / e))) := by
      rw [show (((a : ℤ) * w2.re : ℤ) : ZMod (4 * (d / e)))
          = (a : ZMod (4 * (d / e))) * (w2.re : ZMod (4 * (d / e))) by push_cast; ring]
      exact ha2
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (w2.im : ℤ) ((a : ℤ) * w2.re)
      (4 * (d / e))).mp h1'
    have h3 : (4 * (d / e) : ℤ) ∣ -(((a : ℤ) * w2.re) - w2.im) := dvd_neg.mpr h2
    rwa [neg_sub] at h3
  have hJz : jacobiSym ((star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re) d
      = jacobiSym ((e : ℤ) ^ 2 + (a : ℤ) ^ 2) (d / e)
        * jacobiSym w1.im e * jacobiSym w2.im e
        * jacobiSym w1.re (d / e) * jacobiSym w2.re (d / e) := by
    conv_lhs => rw [re_star_scalePt e w1 w2, hd_eq]
    rw [jacobiSym_factor e (d / e) a w1.re w1.im w2.re w2.im he0 hd'0 hdvd1 hdvd2]
  have hJ : ((jacobiSym ((star (Work.FIArea4.scalePt e w1) * Work.FIArea4.scalePt e w2).re) d : ℤ) : ℂ)
      = ((jacobiSym ((e : ℤ) ^ 2 + (a : ℤ) ^ 2) (d / e) : ℤ) : ℂ)
        * ((jacobiSym w1.im e : ℤ) : ℂ) * ((jacobiSym w2.im e : ℤ) : ℂ)
        * ((jacobiSym w1.re (d / e) : ℤ) : ℂ) * ((jacobiSym w2.re (d / e) : ℤ) : ℂ) := by
    rw [hJz]; push_cast; ring
  have hS15 := Work.FIArea4.S15theta_phase_factor X j d u t ℓ
    (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
  simp only [ssTerm, ssConst, ssFac, ssArrA, ssArrB, ssD]
  rw [← hadef, hJ, hS15, star_mul]
  ring

/-- The class factor has modulus at most one. -/
lemma norm_ssFac_le_one (e d' : ℕ) (a : ZMod (4 * d')) : ‖ssFac e d' a‖ ≤ 1 := by
  unfold ssFac
  rcases jacobiSym.trichotomy ((e : ℤ) ^ 2 + (a.val : ℤ) ^ 2) d' with h | h | h <;> rw [h] <;> norm_num

/-- The `d`-only phase factor has modulus at most one. -/
lemma norm_ssD_le_one (X j d : ℕ) (t : ℝ) : ‖ssD X j d t‖ ≤ 1 := by
  unfold ssD
  set r : ℝ := (4 : ℝ) * (X : ℝ) * (2 : ℝ) ^ j * (d : ℝ) with hr
  have h0 : 0 ≤ r := by rw [hr]; positivity
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]
    simp only [Complex.ofReal_zero]
    by_cases hh : -(Complex.I * (t : ℂ)) = 0
    · rw [hh, Complex.cpow_zero]; norm_num
    · rw [Complex.zero_cpow hh]; norm_num
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h]
    simp

lemma norm_ssConst_le_one (X j d : ℕ) (hd : 1 ≤ d) (t : ℝ) : ‖ssConst X j d t‖ ≤ 1 := by
  unfold ssConst
  rw [norm_mul]
  have htot : ‖((((Nat.totient d : ℝ) / (d : ℝ) : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    rw [div_le_one (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd))]
    exact_mod_cast Nat.totient_le d
  calc ‖((((Nat.totient d : ℝ) / (d : ℝ) : ℝ)) : ℂ)‖ * ‖ssD X j d t‖
      ≤ 1 * 1 := mul_le_mul htot (norm_ssD_le_one X j d t) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring


lemma dvd_re_of_gcd_eq {d e : ℕ} {z : GaussianInt} (h : Nat.gcd d z.re.natAbs = e) :
    (e : ℤ) ∣ z.re := by
  have h1 : e ∣ z.re.natAbs := h ▸ Nat.gcd_dvd_right d z.re.natAbs
  have h2 : (e : ℤ) ∣ ((z.re.natAbs : ℕ) : ℤ) := by exact_mod_cast h1
  exact (Int.dvd_natAbs).mp h2

lemma S15strU_eq' (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (w : GaussianInt) :
    Work.FIArea4.S15strU β u t ℓ e w
      = β (Work.FIArea4.scalePt e w) * ((jacobiSym w.im e : ℤ) : ℂ)
          * Work.FIArea4.S15zf u t ℓ (Work.FIArea4.scalePt e w) := rfl

lemma S15strV_eq' (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (w : GaussianInt) :
    Work.FIArea4.S15strV β u t ℓ e w
      = β (Work.FIArea4.scalePt e w) * ((jacobiSym w.im e : ℤ) : ℂ)
          * Work.FIArea4.S15zfV u t ℓ (Work.FIArea4.scalePt e w) := rfl

/-- The `z`-side stratum summand. -/
def ssZ (X j d e : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (z1 z2 : GaussianInt) : ℂ :=
  if Nat.gcd d z1.re.natAbs = e ∧ X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
    (β z1 * star (β z2)) * ssTerm X j d u t ℓ z1 z2 else 0

/-- The `w`-side stratum summand (before the class factorisation). -/
def ssW (X j d e : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (w1 w2 : GaussianInt) : ℂ :=
  if Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e ∧ X < d
      ∧ 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) then
    (β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2)))
      * ssTerm X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) else 0

/-- The class-Cauchy–Schwarz form of the stratum summand. -/
def ssT (Pa : Work.FITop.Params) (X j d e : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ)
    (w1 w2 : GaussianInt) : ℂ :=
  if (Work.FIPlan.Delta w1 w2 : ZMod (4 * (d / e))) = 0 then
    (ssConst X j d t * ssFac e (d / e)
        ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹))
      * (ssU Pa e (d / e) β u t ℓ w1 * star (ssV Pa e (d / e) β u t ℓ w2))
  else 0

/-- **The pointwise identity of the stratum summand with its class factorisation.** -/
lemma ssPoint (Pa : Work.FITop.Params) (X j d e : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β)
    (he : 1 ≤ e) (hd : 1 ≤ d) (hed : e ∣ d) (w1 w2 : GaussianInt) :
    (if Nat.Coprime w1.re.natAbs (d / e) ∧ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2 then
        (β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2)))
          * ssTerm X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) else 0)
      = (if (Work.FIPlan.Delta w1 w2 : ZMod (4 * (d / e))) = 0 then
          (ssConst X j d t * ssFac e (d / e)
              ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹))
            * (ssU Pa e (d / e) β u t ℓ w1 * star (ssV Pa e (d / e) β u t ℓ w2)) else 0) := by
  classical
  by_cases hcond : Nat.Coprime w1.re.natAbs (d / e) ∧ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2
  · rw [if_pos hcond, if_pos (delta_zmod_eq_zero_of_dvd_absDelta hcond.2)]
    by_cases hb1 : β (Work.FIArea4.scalePt e w1) = 0
    · have hz : ssU Pa e (d / e) β u t ℓ w1 = 0 := by
        rw [ssU]
        split_ifs with hc4
        · rw [S15strU_eq', hb1]; simp
        · rfl
      simp only [hb1, zero_mul, mul_zero, hz]
    by_cases hb2 : β (Work.FIArea4.scalePt e w2) = 0
    · have hz : ssV Pa e (d / e) β u t ℓ w2 = 0 := by
        rw [ssV]
        split_ifs with hc4
        · rw [S15strV_eq', hb2]; simp
        · rfl
      simp only [hb2, star_zero, zero_mul, mul_zero, hz]
    · have hodd1 := odd_re_of_prim (e := e)
        (fun z hz => Work.FIArea4.IsPrimBoxCoeff.coprime hβ hz) hb1
      have hodd2 := odd_re_of_prim (e := e)
        (fun z hz => Work.FIArea4.IsPrimBoxCoeff.coprime hβ hz) hb2
      have hc2 : Nat.Coprime w2.re.natAbs (d / e) := by
        have hD : (d : ℤ) ∣ Work.FIPlan.Delta (Work.FIArea4.scalePt e w1)
            (Work.FIArea4.scalePt e w2) := by
          have h4d : 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
              (Work.FIArea4.scalePt e w2) := by
            rw [absDelta_scalePt]
            exact (four_mul_dvd_iff he hed).mpr hcond.2
          have hd1 : d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
              (Work.FIArea4.scalePt e w2) := dvd_trans (dvd_mul_left d 4) h4d
          have h2 : (d : ℤ) ∣ ((Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
              (Work.FIArea4.scalePt e w2) : ℕ) : ℤ) := by exact_mod_cast hd1
          rw [Work.FIPlan.absDelta] at h2
          exact (Int.dvd_natAbs).mp h2
        have hg := gcd_re_eq_of_delta
          (Work.FIArea4.IsPrimBoxCoeff.coprime hβ hb1)
          (Work.FIArea4.IsPrimBoxCoeff.coprime hβ hb2) hD
        have hg2 : Nat.gcd d (Work.FIArea4.scalePt e w2).re.natAbs = e := by
          rw [← hg, Work.FIArea4.scalePt_re]
          exact gcd_scalePt_of_coprime hed hcond.1
        have hgw : Nat.gcd d ((e : ℤ) * w2.re).natAbs = e := by
          have h1 : Nat.gcd d ((e : ℤ) * w2.re).natAbs
              = Nat.gcd d (Work.FIArea4.scalePt e w2).re.natAbs := by
            rw [Work.FIArea4.scalePt_re]
          rw [h1, hg2]
        exact coprime_of_gcd_scalePt he hed hgw
      rw [ssU_eq_ssArrA hodd1 hcond.1, ssV_eq_ssArrB hodd2 hc2]
      exact ssFactor X j d e he hd hed u t ℓ β
        (fun z hz => Work.FIArea4.IsPrimBoxCoeff.coprime hβ hz) hb1 hb2 hcond.1 hc2 hcond.2
  · rw [if_neg hcond]
    by_cases hΔ0 : (Work.FIPlan.Delta w1 w2 : ZMod (4 * (d / e))) = 0
    · rw [if_pos hΔ0]
      have h4 : 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2 := by
        have h1 : ((4 * (d / e) : ℕ) : ℤ) ∣ Work.FIPlan.Delta w1 w2 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (Work.FIPlan.Delta w1 w2) (4 * (d / e))).mp hΔ0
        have h2 : ((4 * (d / e) : ℕ) : ℤ)
            ∣ (((Work.FIPlan.Delta w1 w2).natAbs : ℕ) : ℤ) := Int.dvd_natAbs.mpr h1
        have h3 : 4 * (d / e) ∣ (Work.FIPlan.Delta w1 w2).natAbs := by exact_mod_cast h2
        rwa [Work.FIPlan.absDelta]
      have hnc : ¬ Nat.Coprime w1.re.natAbs (d / e) := fun hc => hcond ⟨hc, h4⟩
      have hnotcop : ¬ Nat.Coprime w1.re.natAbs (4 * (d / e)) := fun hc4 =>
        hnc (hc4.coprime_dvd_right (dvd_mul_left (d / e) 4))
      have hz : ssU Pa e (d / e) β u t ℓ w1 = 0 := by rw [ssU, if_neg hnotcop]
      simp only [hz, zero_mul, mul_zero]
    · rw [if_neg hΔ0]

/-- Reindexing the `Re`-divisible part of the box: `A` is the image of `W` under `scalePt e`. -/
lemma sum_image_A_eq_sum_W (Pa : Work.FITop.Params) (e : ℕ) (he : 1 ≤ e)
    {α : Type*} [AddCommMonoid α] (F : GaussianInt → α) :
    (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => (e : ℤ) ∣ z.re), F z)
      = ∑ w ∈ (Work.FITop.boxN Pa).filter
            (fun w => Work.FIArea4.scalePt e w ∈ Work.FITop.boxN Pa),
          F (Work.FIArea4.scalePt e w) := by
  have hA : (Work.FITop.boxN Pa).filter (fun z => (e : ℤ) ∣ z.re)
      = ((Work.FITop.boxN Pa).filter
          (fun w => Work.FIArea4.scalePt e w ∈ Work.FITop.boxN Pa)).image
            (Work.FIArea4.scalePt e) := by
    ext z
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hz, hdvd⟩
      exact ⟨Work.FIArea4.unscalePt e z,
        Finset.mem_filter.mpr
          ⟨unscalePt_mem_boxN Pa hz, by rw [Work.FIArea4.scalePt_unscalePt e he hdvd]; exact hz⟩,
        Work.FIArea4.scalePt_unscalePt e he hdvd⟩
    · rintro ⟨w, hw, rfl⟩
      rw [Finset.mem_filter] at hw
      exact ⟨hw.2, ⟨w.re, by rw [Work.FIArea4.scalePt_re]⟩⟩
  rw [hA]
  refine Finset.sum_image (g := Work.FIArea4.scalePt e) ?_
  intro a _ b _ hab
  exact Work.FIArea4.scalePt_injective e he hab

lemma ssW_eq_ssT (Pa : Work.FITop.Params) (X j d e : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β)
    (hX : X < d) (he : 1 ≤ e) (hd : 1 ≤ d) (hed : e ∣ d) (w1 w2 : GaussianInt) :
    ssW X j d e β u t ℓ w1 w2 = ssT Pa X j d e β u t ℓ w1 w2 := by
  have hp := ssPoint Pa X j d e φ β ℓ u t hβ he hd hed w1 w2
  have hC : (Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e ∧ X < d
        ∧ 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2))
      ↔ (Nat.Coprime w1.re.natAbs (d / e) ∧ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2) := by
    have h1 : Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e
        ↔ Nat.Coprime w1.re.natAbs (d / e) := by
      rw [Work.FIArea4.scalePt_re]
      exact ⟨fun h => coprime_of_gcd_scalePt he hed h, fun h => gcd_scalePt_of_coprime hed h⟩
    have h2 : 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
          (Work.FIArea4.scalePt e w2)
        ↔ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2 := by
      rw [absDelta_scalePt]; exact four_mul_dvd_iff he hed
    rw [h1, h2]
    constructor
    · rintro ⟨ha, -, hb⟩; exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩; exact ⟨ha, hX, hb⟩
  simp only [ssW, ssT]
  rw [if_congr hC rfl rfl]
  exact hp

end SSE

end


end Work.FIArea4.S15red
