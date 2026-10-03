/-
# `Submission.Work.FIArea6V.S16RadialCoreTwoV_of_noClassTwoV`

`S16RadialNoClassTwoV → S16RadialCoreTwoV`: the τ-vacuous/axis-free **V-analogue** of the pinned
reduction `Submission.Work.FIArea6.S16RadialCoreTwo_of_noClassTwo`.

The (5.7) class congruence `SameClass8 z z0` of *FI* §16 is detected by the characters of
`(ℤ[i]/8ℤ[i])^*` (paper, remark after (16.25)): the detection replaces `χ` by `χψ` of modulus
`lcm(4d,8) = 4·lcm(d,2) ≤ 4·(2d)`, the free constant `C` absorbs the factor `2` of the modulus and
the free exponent constant `c` the loss in `(4d)^{-ε}`.  When the detected modulus `4·lcm(d,2)`
exceeds the admissible allowance `4·(log N)^{1/(2ε)}` the exponential factor
`exp(-ηc(4d)^{-ε}√log N)` in the target is bounded below by a constant and the *trivial* mass bound
(the sector τ-sum) suffices.

The only difference from the pinned reduction is that the class-free core `hNC` now carries the two
extra hypotheses `TauVac Pa φ` and `(∀ z, InPolarBox Pa φ z → IsAxisFree Pa z)`, which are simply
threaded through its single application (in case A); the support predicates of the two cores are
*identical*, so every line of the bookkeeping transports literally.
-/
import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea6.ClassDetectDefs
import Submission.Work.FIArea6.char8Of_isCharMod4dStrict
import Submission.Work.FIArea6.classDetect8Gauss
import Submission.Work.FIArea6.s16RadialSupportMass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.FIArea6V

open Finset
open scoped BigOperators
open Work.FIArea6

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary facts about the primary class modulo eight -/

/-- `gnorm` as a rational integer. -/
lemma gnorm_eq_int (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re * z.re + z.im * z.im := by
  have hnorm : z.norm = z.re * z.re + z.im * z.im := by
    simp only [Zsqrtd.norm]; ring
  have hge : (0 : ℤ) ≤ z.re * z.re + z.im * z.im :=
    add_nonneg (mul_self_nonneg z.re) (mul_self_nonneg z.im)
  rw [Work.FIPlan.gnorm, hnorm, Int.natAbs_of_nonneg hge]

/-- The class of `|z|²` modulo eight is the norm form of the class of `z` modulo eight. -/
lemma gnorm_zmod8_eq_sq (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ZMod 8) = (z.re : ZMod 8) ^ 2 + (z.im : ZMod 8) ^ 2 := by
  rw [← Int.cast_natCast (R := ZMod 8), gnorm_eq_int z]
  push_cast
  ring

/-- `gnorm` only depends on the class modulo eight. -/
lemma gnorm_zmod8_of_sameClass8 {z z0 : GaussianInt} (h : Work.FITop4.SameClass8 z z0) :
    ((Work.FIPlan.gnorm z : ℕ) : ZMod 8) = ((Work.FIPlan.gnorm z0 : ℕ) : ZMod 8) := by
  have h1 : ((z.re : ZMod 8), (z.im : ZMod 8)) = ((z0.re : ZMod 8), (z0.im : ZMod 8)) := h
  have hr : (z.re : ZMod 8) = (z0.re : ZMod 8) := congrArg Prod.fst h1
  have hi : (z.im : ZMod 8) = (z0.im : ZMod 8) := congrArg Prod.snd h1
  rw [gnorm_zmod8_eq_sq z, gnorm_zmod8_eq_sq z0, hr, hi]

/-- A primary Gaussian integer is odd, hence a unit modulo eight. -/
lemma isUnitMod4d_two_of_isPrimary {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Work.FIArea5.S16Hecke.IsUnitMod4d 2 z := by
  haveI : NeZero (4 * 2) := ⟨by norm_num⟩
  obtain ⟨hr, hi, -⟩ := hz
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hi
  have hdv : (2 : ℤ) ∣ ((Work.FIPlan.gnorm z : ℕ) : ℤ) - 1 := by
    rw [gnorm_eq_int z, ha, hb]
    exact ⟨2 * a * a + 2 * a + 2 * b * b, by ring⟩
  have hodd : Odd (Work.FIPlan.gnorm z) := by
    have h2 : ((Work.FIPlan.gnorm z : ℕ) : ℤ) % 2 = 1 := by omega
    have h3 : Work.FIPlan.gnorm z % 2 = 1 := by omega
    exact Nat.odd_iff.mpr h3
  rw [Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime]
  exact (Nat.coprime_two_right.mpr hodd).pow_right 3

/-- Being a unit modulo eight is a class-modulo-eight property. -/
lemma isUnitMod4d_two_of_sameClass8 {z z0 : GaussianInt} (h : Work.FITop4.SameClass8 z z0)
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d 2 z) :
    Work.FIArea5.S16Hecke.IsUnitMod4d 2 z0 := by
  haveI : NeZero (4 * 2) := ⟨by norm_num⟩
  rw [Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_isUnit_norm] at hz ⊢
  show IsUnit (((Work.FIPlan.gnorm z0 : ℕ)) : ZMod 8)
  rw [← gnorm_zmod8_of_sameClass8 h]
  exact hz

/-- A primary `z` in the class of `z0` forces `z0` to be a unit modulo eight. -/
lemma isUnitMod4d_two_of_isPrimary_sameClass8 {z z0 : GaussianInt}
    (hz : Work.FIPlan.IsPrimary z) (h : Work.FITop4.SameClass8 z z0) :
    Work.FIArea5.S16Hecke.IsUnitMod4d 2 z0 :=
  isUnitMod4d_two_of_sameClass8 h (isUnitMod4d_two_of_isPrimary hz)


/-! ## 1b. The product of a strict character modulo `4d` with one modulo eight -/

/-- `4d` divides `4·lcm(d,2)` in `ℤ[i]`. -/
private lemma gauss_fourDvd_lcm (d : ℕ) :
    (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (((4 * Nat.lcm d 2 : ℕ) : ℤ) : GaussianInt) := by
  obtain ⟨k, hk⟩ := Nat.dvd_lcm_left d 2
  refine ⟨((k : ℕ) : ℤ), ?_⟩
  rw [hk]
  push_cast
  ring

/-- `8` divides `4·lcm(d,2)` in `ℤ[i]`. -/
private lemma gauss_eightDvd_lcm (d : ℕ) :
    (((8 : ℕ) : ℤ) : GaussianInt) ∣ (((4 * Nat.lcm d 2 : ℕ) : ℤ) : GaussianInt) := by
  obtain ⟨k, hk⟩ := Nat.dvd_lcm_right d 2
  refine ⟨((k : ℕ) : ℤ), ?_⟩
  rw [hk]
  push_cast
  ring

/-- A unit modulo `4d` is a unit modulo `4·lcm(d,2)`. -/
private lemma isUnitMod4d_lcm_of_isUnitMod4d {d : ℕ} (hd1 : 1 ≤ d) {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) :
    Work.FIArea5.S16Hecke.IsUnitMod4d (Nat.lcm d 2) z := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  haveI : NeZero (4 * Nat.lcm d 2) := ⟨by
    have h2 : 2 ≤ Nat.lcm d 2 :=
      Nat.le_of_dvd (Nat.lcm_pos (by omega) (by norm_num)) (Nat.dvd_lcm_right d 2)
    omega⟩
  rw [Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime] at hz ⊢
  have h2 : Nat.Coprime (Work.FIPlan.gnorm z) 2 :=
    hz.coprime_dvd_right (by omega : 2 ∣ 4 * d)
  have h8 : Nat.Coprime (Work.FIPlan.gnorm z) 8 := by
    simpa using h2.pow_right 3
  refine (hz.mul_right h8).coprime_dvd_right ?_
  have hlcm : Nat.lcm d 2 ∣ 2 * d :=
    Nat.lcm_dvd (dvd_mul_left d 2) (dvd_mul_right 2 d)
  have h1 : 4 * Nat.lcm d 2 ∣ 4 * (2 * d) := Nat.mul_dvd_mul_left 4 hlcm
  have h2 : 4 * (2 * d) ∣ 4 * d * 8 := ⟨4, by ring⟩
  exact dvd_trans h1 h2

/-- **The product of a strict character modulo `4d` with one modulo eight.**  The product is a
strict character modulo `lcm(4d,8) = 4·lcm(d,2)`: the detection of the (5.7) congruence of §16
("changing `χ` in `ψ`") produces characters of exactly this shape. -/
private theorem strictChar8_mul_aux {d : ℕ} {chi psi : GaussianInt → ℂ} (hd1 : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hpsi : Work.FIArea5.S16Hecke.IsCharMod4dStrict 2 psi) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict (Nat.lcm d 2) (fun z => chi z * psi z) := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  haveI : NeZero (4 * 2) := ⟨by norm_num⟩
  haveI : NeZero (4 * Nat.lcm d 2) := ⟨by
    have h2 : 2 ≤ Nat.lcm d 2 :=
      Nat.le_of_dvd (Nat.lcm_pos (by omega) (by norm_num)) (Nat.dvd_lcm_right d 2)
    omega⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show chi 1 * psi 1 = 1
    rw [hchi.1.1, hpsi.1.1, mul_one]
  · intro z w
    show chi (z * w) * psi (z * w) = (chi z * psi z) * (chi w * psi w)
    rw [hchi.1.2.1 z w, hpsi.1.2.1 z w]
    ring
  · intro z
    show ‖chi z * psi z‖ ≤ 1
    rw [norm_mul]
    calc ‖chi z‖ * ‖psi z‖ ≤ 1 * 1 :=
          mul_le_mul (hchi.1.2.2.1 z) (hpsi.1.2.2.1 z) (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  · intro z w hzw
    show chi z * psi z = chi w * psi w
    rw [hchi.1.2.2.2.1 z w (dvd_trans (gauss_fourDvd_lcm d) hzw),
      hpsi.1.2.2.2.1 z w (dvd_trans (gauss_eightDvd_lcm d) hzw)]
  · intro z hz
    show chi z * psi z = 0
    rw [hchi.1.2.2.2.2 z (dvd_trans (gauss_fourDvd_lcm d) hz), zero_mul]
  · intro z hz
    exact mul_eq_zero_of_left (hchi.2 z (fun hcon => hz (isUnitMod4d_lcm_of_isUnitMod4d hd1 hcon))) _



/-! ## 1c. The trivial regime of the §16 core -/

/-- **The trivial regime.**  When the detected modulus `4·lcm(d,2)` of the (5.7) detection exceeds
the admissible allowance `4(log N)^{1/(2ε)}`, i.e. `d ≥ (log N)^{1/(2ε)}`, the exponential factor
`exp(-ηc(4d)^{-ε}√log N)` of the target is bounded below by the constant `exp(-c4^{-ε})` and the
*trivial* mass bound `(√N + θN)(log N)^9` of the sector divisor sum is dominated by the target: the
prefactor `(4d) ≥ 4(log N)^{1/(2ε)} ≥ 4` compensates the `(log N)^3` of the mass bound, while the
two log-powers `θ = (log x)^{-A'}` and `N^{-1/2} ≤ x^{-1/8}` are small. -/
private theorem radialTrivialCase_aux {ε c C₁ : ℝ} (hε0 : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hc : 0 < c) (hC₁ : 0 < C₁) :
    ∃ C x0 : ℝ, 0 < C ∧ 0 < x0 ∧ ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
      ∀ (d : ℕ), 1 ≤ d → 2 * (Real.log Pa.N) ^ (1 / (2 * ε)) ≤ (Nat.lcm d 2 : ℝ) →
        C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9 : ℕ)
          ≤ C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
  refine ⟨C₁ * 2 ^ (8 : ℕ) * Real.exp (c * (4 : ℝ) ^ (-ε)),
    Real.exp 100 + (48 : ℝ) ^ (48 : ℕ), by positivity, by positivity, ?_⟩
  intro Pa hx d hd1 hcaseB
  have hx100 : Real.exp 100 ≤ (Pa.x : ℝ) := by
    have h48 : (0 : ℝ) ≤ (48 : ℝ) ^ (48 : ℕ) := by positivity
    linarith
  have hx48 : (48 : ℝ) ^ (48 : ℕ) ≤ (Pa.x : ℝ) := by
    have h100 : (0 : ℝ) ≤ Real.exp 100 := (Real.exp_pos 100).le
    linarith
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hx100
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hx0 : (0 : ℝ) ≤ (Pa.x : ℝ) := hxpos.le
  have hε0' : (0 : ℝ) ≤ ε := hε0.le
  have hθ0 : (0 : ℝ) ≤ Pa.θ := Pa.hθ0.le
  have hC₁0 : (0 : ℝ) ≤ C₁ := hC₁.le
  have hlogx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 100) hx100
    rw [Real.log_exp] at h
    linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  have hE25 : Real.exp 25 ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (Real.exp 100) ^ ((1 : ℝ) / 4) = Real.exp 25 := by
      rw [← Real.exp_mul]; norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (Real.exp_pos 100).le hx100 (by norm_num)
  have hNgt : Real.exp 25 < Pa.N := by
    have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
    linarith [Pa.hNlo, hE25, h2]
  have hlogN : 25 < Real.log Pa.N := by
    have h2 := Real.log_lt_log (Real.exp_pos 25) hNgt
    rwa [Real.log_exp] at h2
  have hlogN1 : (1 : ℝ) < Real.log Pa.N := by linarith
  have hlogN0 : (0 : ℝ) < Real.log Pa.N := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log Pa.N := hlogN0.le
  have hN0 : 0 < Pa.N := lt_trans (Real.exp_pos 25) hNgt
  have hN0le : (0 : ℝ) ≤ Pa.N := hN0.le
  have hN2 : (2 : ℝ) ≤ Pa.N := by
    have h := Real.add_one_le_exp (25 : ℝ)
    linarith [hNgt, h]
  have hlogB : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 := by
    have h1 : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ (Real.log (Pa.x : ℝ)) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith [Pa.hB])
    rwa [Real.rpow_zero] at h1
  have hxhalf : Pa.N ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h5 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
      simpa using mul_le_mul_of_nonneg_left hlogB (Real.rpow_nonneg hx0 _)
    linarith [Pa.hNhi, h5]
  have hNx : Pa.N ≤ (Pa.x : ℝ) := by
    have h6 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) ≤ (Pa.x : ℝ) := by
      have h7 := Real.rpow_le_rpow_of_exponent_le hx1 (show ((1 : ℝ) / 2) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h7
    linarith
  have hη1 : Pa.η ≤ 1 := by
    by_contra hnot
    push_neg at hnot
    have h1 : (1 : ℝ) / 2 ≤ (1 : ℝ) / 4 + Pa.η := by linarith
    have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 h1
    linarith [Pa.hNlo, hxhalf, h2]
  have hlog2N : Real.log (2 + Pa.N) ≤ 2 * Real.log Pa.N := by
    have h1 : Real.log (2 + Pa.N) ≤ Real.log (2 * Pa.N) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hN0.ne'] at h1
    have h2 : Real.log 2 ≤ Real.log Pa.N := Real.log_le_log (by norm_num) hN2
    linarith
  have hsqrt : Real.sqrt Pa.N = Pa.N * Pa.N ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    conv_lhs => rw [show (1 : ℝ) / 2 = 1 + (-(1 / 2)) by norm_num]
    rw [Real.rpow_add hN0, Real.rpow_one]
  -- (iii) `θ·(log N)^3 ≤ 1`
  have htheta : Pa.θ * (Real.log Pa.N) ^ (3 : ℕ) ≤ 1 := by
    rw [Pa.hθ]
    have hLle : Real.log Pa.N ≤ Real.log (Pa.x : ℝ) := Real.log_le_log hN0 hNx
    have hA3 : (3 : ℝ) ≤ Pa.A' := by
      have h20 : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
      have h203 : (3 : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) := by norm_num
      linarith
    have h1 : (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Real.log Pa.N) ^ (3 : ℕ)
        ≤ (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Real.log (Pa.x : ℝ)) ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLle 3)
        (Real.rpow_nonneg hlogx0 _)
    have h2 : (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Real.log (Pa.x : ℝ)) ^ (3 : ℕ)
        = (Real.log (Pa.x : ℝ)) ^ (3 - Pa.A') := by
      rw [← Real.rpow_natCast (Real.log (Pa.x : ℝ)) 3, ← Real.rpow_add (by linarith)]
      ring_nf
    have h3 : (Real.log (Pa.x : ℝ)) ^ (3 - Pa.A') ≤ 1 := by
      calc (Real.log (Pa.x : ℝ)) ^ (3 - Pa.A')
          ≤ (Real.log (Pa.x : ℝ)) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
        _ = 1 := Real.rpow_zero _
    linarith [h1, h2, h3]
  -- (iv) `N^{-1/2}·(log N)^3 ≤ 1`
  have hNinv : Pa.N ^ (-(1 / 2 : ℝ)) * (Real.log Pa.N) ^ (3 : ℕ) ≤ 1 := by
    have hx14 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ Pa.N := by
      have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
      linarith [Pa.hNlo, h2]
    have hNinv_le : Pa.N ^ (-(1 / 2 : ℝ)) ≤ (Pa.x : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have h1 : Pa.N ^ (-(1 / 2 : ℝ)) ≤ ((Pa.x : ℝ) ^ ((1 : ℝ) / 4)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (Pa.x : ℝ)) _)
          hx14 (by norm_num)
      have h2 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4)) ^ (-(1 / 2 : ℝ))
          = (Pa.x : ℝ) ^ (-(1 / 8 : ℝ)) := by
        rw [← Real.rpow_mul (by positivity)]
        norm_num
      linarith [h1, h2]
    have hlogx : Real.log (Pa.x : ℝ) ≤ 48 * (Pa.x : ℝ) ^ ((1 : ℝ) / 48) := by
      have h1 : Real.log (Pa.x : ℝ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 48) / ((1 : ℝ) / 48) :=
        Real.log_le_rpow_div (by positivity) (by norm_num)
      have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 48) / ((1 : ℝ) / 48)
          = 48 * (Pa.x : ℝ) ^ ((1 : ℝ) / 48) := by
        rw [div_eq_mul_inv]; ring
      linarith [h1, h2]
    have hLle : Real.log Pa.N ≤ 24 * (Pa.x : ℝ) ^ ((1 : ℝ) / 48) := by
      have h1 : Real.log Pa.N ≤ (1 / 2) * Real.log (Pa.x : ℝ) := by
        have h4 := Real.log_le_log hN0 hxhalf
        rw [Real.log_rpow hxpos] at h4
        linarith
      linarith [hlogx]
    have hpow3 : (Real.log Pa.N) ^ (3 : ℕ) ≤ (24 * (Pa.x : ℝ) ^ ((1 : ℝ) / 48)) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hL0 (by linarith [hLle]) 3
    have hid : (Pa.x : ℝ) ^ (-(1 / 8 : ℝ)) * ((Pa.x : ℝ) ^ ((1 : ℝ) / 48)) ^ (3 : ℕ)
        = (Pa.x : ℝ) ^ (-(1 / 16 : ℝ)) := by
      rw [← Real.rpow_natCast ((Pa.x : ℝ) ^ ((1 : ℝ) / 48)) 3, ← Real.rpow_mul hx0,
        ← Real.rpow_add hxpos]
      congr 1
      norm_num
    have hx16 : (48 : ℝ) ^ (3 : ℕ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 16) := by
      have h2 : ((48 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 16) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 16) :=
        Real.rpow_le_rpow (by positivity) hx48 (by norm_num)
      have h3 : ((48 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 16) = (48 : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast (48 : ℝ) 48, ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith [h2, h3]
    have h24 : (24 : ℝ) ^ (3 : ℕ) ≤ (48 : ℝ) ^ (3 : ℕ) := by norm_num
    calc Pa.N ^ (-(1 / 2 : ℝ)) * (Real.log Pa.N) ^ (3 : ℕ)
        ≤ (Pa.x : ℝ) ^ (-(1 / 8 : ℝ)) * (24 * (Pa.x : ℝ) ^ ((1 : ℝ) / 48)) ^ (3 : ℕ) :=
          mul_le_mul hNinv_le hpow3 (by positivity) (Real.rpow_nonneg hx0 _)
      _ = (Pa.x : ℝ) ^ (-(1 / 8 : ℝ))
            * ((24 : ℝ) ^ (3 : ℕ) * ((Pa.x : ℝ) ^ ((1 : ℝ) / 48)) ^ (3 : ℕ)) := by rw [mul_pow]
      _ = (24 : ℝ) ^ (3 : ℕ)
            * ((Pa.x : ℝ) ^ (-(1 / 8 : ℝ)) * ((Pa.x : ℝ) ^ ((1 : ℝ) / 48)) ^ (3 : ℕ)) := by ring
      _ = (24 : ℝ) ^ (3 : ℕ) * (Pa.x : ℝ) ^ (-(1 / 16 : ℝ)) := by rw [hid]
      _ ≤ (48 : ℝ) ^ (3 : ℕ) * (Pa.x : ℝ) ^ (-(1 / 16 : ℝ)) :=
          mul_le_mul_of_nonneg_right h24 (Real.rpow_nonneg hx0 _)
      _ = (48 : ℝ) ^ (3 : ℕ) * ((Pa.x : ℝ) ^ ((1 : ℝ) / 16))⁻¹ := by
          rw [Real.rpow_neg hx0]
      _ ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 16) * ((Pa.x : ℝ) ^ ((1 : ℝ) / 16))⁻¹ :=
          mul_le_mul_of_nonneg_right hx16 (inv_nonneg.mpr (Real.rpow_nonneg hx0 _))
      _ = 1 := by
          rw [mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hxpos _))]
  -- (v) `d ≥ (log N)^{1/(2ε)}`
  have hdl : (Real.log Pa.N) ^ (1 / (2 * ε)) ≤ (d : ℝ) := by
    have hlcm : (Nat.lcm d 2 : ℝ) ≤ 2 * (d : ℝ) := by
      have h1 : Nat.lcm d 2 ≤ 2 * d :=
        Nat.le_of_dvd (by omega) (Nat.lcm_dvd (dvd_mul_left d 2) (dvd_mul_right 2 d))
      exact_mod_cast h1
    linarith [hcaseB, hlcm]
  have h4d_eq : ((4 * d : ℕ) : ℝ) = 4 * (d : ℝ) := by push_cast; ring
  -- (vi) `(4d)^{-ε}·√log N ≤ 4^{-ε}`
  have hpow : (4 : ℝ) ^ ε * (Real.log Pa.N) ^ ((1 : ℝ) / 2) ≤ ((4 * d : ℕ) : ℝ) ^ ε := by
    have hge : (4 : ℝ) * (Real.log Pa.N) ^ (1 / (2 * ε)) ≤ ((4 * d : ℕ) : ℝ) := by
      rw [h4d_eq]; linarith [hdl]
    have h1 : (4 * (Real.log Pa.N) ^ (1 / (2 * ε))) ^ ε ≤ ((4 * d : ℕ) : ℝ) ^ ε :=
      Real.rpow_le_rpow (by positivity) hge hε0'
    have h2 : (4 * (Real.log Pa.N) ^ (1 / (2 * ε))) ^ ε
        = (4 : ℝ) ^ ε * (Real.log Pa.N) ^ ((1 : ℝ) / 2) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hL0 _),
        ← Real.rpow_mul hL0]
      congr 1
      field_simp
    linarith [h1, h2]
  have hXle : ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N) ≤ (4 : ℝ) ^ (-ε) := by
    have h4dpos : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by positivity
    have hLpos : (0 : ℝ) < (Real.log Pa.N) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hlogN0 _
    have hdenpos : (0 : ℝ) < (4 : ℝ) ^ ε * (Real.log Pa.N) ^ ((1 : ℝ) / 2) := by positivity
    have h1 : (((4 * d : ℕ) : ℝ) ^ ε)⁻¹ ≤ ((4 : ℝ) ^ ε * (Real.log Pa.N) ^ ((1 : ℝ) / 2))⁻¹ :=
      (inv_le_inv₀ (Real.rpow_pos_of_pos h4dpos _) hdenpos).mpr hpow
    rw [← Real.rpow_neg h4dpos.le, mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      ← Real.rpow_neg hL0] at h1
    have h3 : ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)
        ≤ ((4 : ℝ) ^ (-ε) * (Real.log Pa.N) ^ (-(1 / 2 : ℝ))) * Real.sqrt (Real.log Pa.N) :=
      mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    have h4 : ((4 : ℝ) ^ (-ε) * (Real.log Pa.N) ^ (-(1 / 2 : ℝ))) * Real.sqrt (Real.log Pa.N)
        = (4 : ℝ) ^ (-ε) := by
      calc ((4 : ℝ) ^ (-ε) * (Real.log Pa.N) ^ (-(1 / 2 : ℝ))) * Real.sqrt (Real.log Pa.N)
          = (4 : ℝ) ^ (-ε)
            * ((Real.log Pa.N) ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log Pa.N)) := by ring
        _ = (4 : ℝ) ^ (-ε) * 1 := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hlogN0,
              show (-(1 / 2 : ℝ)) + (1 / 2 : ℝ) = 0 by norm_num, Real.rpow_zero]
        _ = (4 : ℝ) ^ (-ε) := by rw [mul_one]
    linarith [h3, h4]
  -- (vii) the two comparison steps
  have hLHS : C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9 : ℕ)
      ≤ C₁ * 2 ^ (10 : ℕ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
    have hLP : (Real.log (2 + Pa.N)) ^ (9 : ℕ) ≤ (2 * Real.log Pa.N) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog2N 9
    have h1 : C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9 : ℕ)
        ≤ C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (2 * Real.log Pa.N) ^ (9 : ℕ) :=
      mul_le_mul_of_nonneg_left hLP
        (mul_nonneg hC₁0 (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hθ0 hN0le)))
    have h2 : C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (2 * Real.log Pa.N) ^ (9 : ℕ)
        = C₁ * 2 ^ (9 : ℕ) * Pa.N
            * ((Pa.N ^ (-(1 / 2 : ℝ)) * (Real.log Pa.N) ^ (3 : ℕ))
                + Pa.θ * (Real.log Pa.N) ^ (3 : ℕ)) * (Real.log Pa.N) ^ (6 : ℕ) := by
      rw [mul_pow, hsqrt]
      ring
    have h3 : Pa.N ^ (-(1 / 2 : ℝ)) * (Real.log Pa.N) ^ (3 : ℕ)
        + Pa.θ * (Real.log Pa.N) ^ (3 : ℕ) ≤ 2 := by linarith [hNinv, htheta]
    have h4 : C₁ * 2 ^ (9 : ℕ) * Pa.N
          * ((Pa.N ^ (-(1 / 2 : ℝ)) * (Real.log Pa.N) ^ (3 : ℕ))
              + Pa.θ * (Real.log Pa.N) ^ (3 : ℕ)) * (Real.log Pa.N) ^ (6 : ℕ)
        ≤ C₁ * 2 ^ (9 : ℕ) * Pa.N * 2 * (Real.log Pa.N) ^ (6 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL0 6)
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    calc C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9 : ℕ)
        ≤ C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (2 * Real.log Pa.N) ^ (9 : ℕ) := h1
      _ = C₁ * 2 ^ (9 : ℕ) * Pa.N
            * ((Pa.N ^ (-(1 / 2 : ℝ)) * (Real.log Pa.N) ^ (3 : ℕ))
                + Pa.θ * (Real.log Pa.N) ^ (3 : ℕ)) * (Real.log Pa.N) ^ (6 : ℕ) := h2
      _ ≤ C₁ * 2 ^ (9 : ℕ) * Pa.N * 2 * (Real.log Pa.N) ^ (6 : ℕ) := h4
      _ = C₁ * 2 ^ (10 : ℕ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by ring
  have hE1 : Real.exp (-(c * (4 : ℝ) ^ (-ε)))
      ≤ Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N))) := by
    apply Real.exp_le_exp.mpr
    have hX0 : (0 : ℝ) ≤ ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.sqrt_nonneg _)
    have hstep : Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)
        = c * (Pa.η * (((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N))) := by ring
    rw [hstep]
    have h1 : Pa.η * (((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N))
        ≤ (4 : ℝ) ^ (-ε) := by
      calc Pa.η * (((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N))
          ≤ 1 * (((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)) :=
            mul_le_mul_of_nonneg_right hη1 hX0
        _ ≤ 1 * (4 : ℝ) ^ (-ε) := by rw [one_mul, one_mul]; exact hXle
        _ = (4 : ℝ) ^ (-ε) := by rw [one_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_left h1 hc.le)
  have h4dge : (4 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by
    rw [h4d_eq]
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    linarith
  have hE1' : Real.exp (-(c * (4 : ℝ) ^ (-ε)))
      ≤ Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
        + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))) := by
    have h2 : (0 : ℝ) < Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))) := Real.exp_pos _
    linarith [hE1]
  have hfinal : C₁ * 2 ^ (10 : ℕ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
      ≤ C₁ * 2 ^ (8 : ℕ) * Real.exp (c * (4 : ℝ) ^ (-ε))
          * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
    have hexp : Real.exp (c * (4 : ℝ) ^ (-ε)) * Real.exp (-(c * (4 : ℝ) ^ (-ε))) = 1 := by
      rw [← Real.exp_add,
        show c * (4 : ℝ) ^ (-ε) + -(c * (4 : ℝ) ^ (-ε)) = 0 by ring, Real.exp_zero]
    have hprod : (2 : ℝ) ^ (10 : ℕ)
        = 2 ^ (8 : ℕ) * (Real.exp (c * (4 : ℝ) ^ (-ε)) * Real.exp (-(c * (4 : ℝ) ^ (-ε))))
          * 4 := by
      rw [hexp]; ring
    have hB0 : (0 : ℝ) ≤ Real.exp (c * (4 : ℝ) ^ (-ε)) := Real.exp_pos _ |>.le
    calc C₁ * 2 ^ (10 : ℕ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
        = C₁ * 2 ^ (8 : ℕ)
            * (Real.exp (c * (4 : ℝ) ^ (-ε)) * Real.exp (-(c * (4 : ℝ) ^ (-ε))))
            * (4 : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by rw [hprod]; ring
      _ ≤ C₁ * 2 ^ (8 : ℕ) * (Real.exp (c * (4 : ℝ) ^ (-ε))
              * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                  + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
          gcongr
      _ = C₁ * 2 ^ (8 : ℕ) * Real.exp (c * (4 : ℝ) ^ (-ε))
            * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by ring
  calc C₁ * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9 : ℕ)
      ≤ C₁ * 2 ^ (10 : ℕ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hLHS
    _ ≤ C₁ * 2 ^ (8 : ℕ) * Real.exp (c * (4 : ℝ) ^ (-ε))
          * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hfinal

/-! ## 2. The two-constant radial §16 core from its class-free part -/

/-- **`S16RadialCoreTwo` from `S16RadialNoClassTwo`.**

*FI* §16, remark after (16.25).  Two regimes, according to the size of the modulus parameter of
the detected character `χψ` (whose modulus is `4·lcm(d,2)`):

* `lcm(d,2) ≤ 2(log N)^{1/(2ε)}`: the (5.7) class congruence is detected by the characters of
  `(ℤ[i]/8ℤ[i])^*` (the detection identity `classDetect8Gauss`) and the class-free bound is applied
  at the detected modulus `D = lcm(d,2) ≤ 2d`; the free constants absorb `lcm(d,2) ≤ 2d`;
* otherwise `d ≥ (log N)^{1/(2ε)}`, so `(4d)^{-ε}√log N ≤ 4^{-ε}`: the bracket of the target is
  bounded below by the constant `exp(-c4^{-ε})` and the *trivial* mass bound
  (`s16RadialSupportMass`, the sector divisor sum) suffices. -/
theorem S16RadialCoreTwoV_of_noClassTwoV (h : Work.FIArea6V.S16RadialNoClassTwoV) :
    Work.FIArea6V.S16RadialCoreTwoV := by
  intro ε hε0 hε4
  obtain ⟨c', C', x0', hc'0, hC'0, hx0'0, hNC⟩ := h ε hε0 hε4
  obtain ⟨Cm, hCm0, hmass⟩ := Work.FIArea6.s16RadialSupportMass
  set c : ℝ := c' * 2 ^ (-ε) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  obtain ⟨CB, x0B, hCB0, hx0B0, hB⟩ := radialTrivialCase_aux hε0 hε4 hc0 hCm0
  refine ⟨c, max (2 * C') CB, max (max x0' x0B) (Real.exp 100), hc0, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro Pa hx φ ν z0 d j chi q p hTau hAxis hν0 hνlt hd1 hdl hk hchi hqC hpC hqnn hqle hqsupp hqder hpnn hple hpsupp hpder
    have hx' : x0' ≤ (Pa.x : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hxB : x0B ≤ (Pa.x : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx100 : Real.exp 100 ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
    have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hx100
    have hE25 : Real.exp 25 ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1 : (Real.exp 100) ^ ((1 : ℝ) / 4) = Real.exp 25 := by
        rw [← Real.exp_mul]; norm_num
      rw [← h1]
      exact Real.rpow_le_rpow (Real.exp_pos 100).le hx100 (by norm_num)
    have hNgt : Real.exp 25 < Pa.N := by
      have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
      linarith [Pa.hNlo, hE25, h2]
    have hlogN : 25 < Real.log Pa.N := by
      have h2 := Real.log_lt_log (Real.exp_pos 25) hNgt
      rwa [Real.log_exp] at h2
    have hlogN1 : (1 : ℝ) < Real.log Pa.N := by linarith
    have hlogN0 : (0 : ℝ) < Real.log Pa.N := by linarith
    have hN0 : 0 < Pa.N := lt_trans (Real.exp_pos 25) hNgt
    have hbf : (0 : ℝ) ≤ (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
      have h1 : (0 : ℝ) ≤ (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) := by positivity
      have h2 : (0 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ Real.log Pa.N := by linarith
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hN0.le) (pow_nonneg h3 6)
    by_cases hcaseB : 2 * (Real.log Pa.N) ^ (1 / (2 * ε)) ≤ (Nat.lcm d 2 : ℝ)
    · -- ### Case B: the trivial mass bound
      have hF1 : ∀ z : GaussianInt,
          (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0) ≠ 0 →
          Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
          ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N ∧
          φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * Pa.θ ∧
          Squarefree (Work.FIPlan.gnorm z) := by
        intro z hz
        have hM6 : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) := by
          by_contra hc
          rw [if_neg hc] at hz
          exact hz rfl
        have hSz : ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j ≠ 0 := by
          intro h0
          rw [if_pos hM6, h0] at hz
          exact hz rfl
        have hqp : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≠ 0 := by
          intro h0
          apply hSz
          simp [h0]
        have hqne : q (Complex.arg z.toComplex - φ) ≠ 0 := fun h0 => hqp (by rw [h0, zero_mul])
        have hpne : p (Work.FIPlan.gnorm z) ≠ 0 := fun h0 => hqp (by rw [h0, mul_zero])
        obtain ⟨hna, hnb⟩ := hpsupp (Work.FIPlan.gnorm z) hpne
        obtain ⟨hqa, hqb⟩ := hqsupp (Complex.arg z.toComplex - φ) hqne
        refine ⟨hna, hnb, ?_, by linarith, ?_⟩
        · rcases lt_or_eq_of_le hqa with hlt | heq
          · linarith
          · exfalso
            have hq0 : q 0 = 0 := Work.FIArea6Hecke.mollQ_zero hqC hqsupp
            rw [← heq, hq0] at hqne
            exact hqne rfl
        · have hμ : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
            intro h0
            apply hSz
            simp [h0]
          exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
      have hF2 : ∀ z : GaussianInt,
          (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0) ≠ 0 →
          ‖(if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖
            ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
        intro z hz
        have hM6 : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) := by
          by_contra hc
          rw [if_neg hc] at hz
          exact hz rfl
        rw [if_pos hM6]
        have hSz : ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j ≠ 0 := by
          intro h0
          rw [if_pos hM6, h0] at hz
          exact hz rfl
        have hμ : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
          intro h0
          apply hSz
          simp [h0]
        have hgn : Work.FIPlan.gnorm z ≠ 0 := fun h0 => hμ (by rw [h0]; simp)
        have hgnR : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hgn
        have hqne : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≠ 0 := by
          intro h0
          apply hSz
          simp [h0]
        have hbp : ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖ ≤ 1 := by
          have hA := hqnn (Complex.arg z.toComplex - φ)
          have hB := hpnn (Work.FIPlan.gnorm z)
          have hC := hqle (Complex.arg z.toComplex - φ)
          have hD := hple (Work.FIPlan.gnorm z)
          rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> nlinarith
        have hbm : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 :=
          Work.FITop3.norm_moebius_le_one _
        have hbg : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
            ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact Work.FITop3.abs_gammaTrunc_le _ _
        have hbc : ‖chi z‖ ≤ 1 := hchi.1.2.2.1 z
        have hsq : ‖((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)‖
            = Real.sqrt (Work.FIPlan.gnorm z : ℝ) := by
          rw [Complex.norm_def, Complex.normSq_ofReal]
          exact Real.sqrt_mul_self (Real.sqrt_nonneg _)
        have hnω : ‖z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)‖ = 1 := by
          rw [norm_div, Work.FIArea4.norm_toComplex_eq_sqrt_gnorm z, hsq]
          exact div_self (ne_of_gt (Real.sqrt_pos.mpr hgnR))
        have hω : ‖(z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j‖ = 1 := by
          rw [norm_zpow, hnω, one_zpow]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        calc ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖
              * ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖
              * ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
              * ‖chi z‖ * ‖(z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j‖
            ≤ 1 * 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) * 1 * 1 := by
              rw [hω]
              exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul hbp hbm (norm_nonneg _) (by norm_num))
                hbg (by positivity) (by norm_num)) hbc (norm_nonneg _) (by norm_num)) le_rfl
                (by norm_num) (by norm_num)
          _ = (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
      have hm : ∑ z ∈ Work.FITop.boxN Pa, ‖(if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖
          ≤ Cm * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9:ℕ) :=
        hmass Pa φ (fun z => if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0) hF1 hF2
      have hB' := hB Pa hxB d hd1 hcaseB
      have htail : (0 : ℝ) ≤ (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
        have h1 : (0 : ℝ) ≤ (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) := by positivity
        exact mul_nonneg (mul_nonneg (mul_nonneg h1 (by positivity)) hN0.le) (pow_nonneg hlogN0.le 6)
      have hstepB : CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
          ≤ max (2 * C') CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
        have h1 : CB ≤ max (2 * C') CB := le_max_right _ _
        calc CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
            = CB * ((Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) := by ring
          _ ≤ max (2 * C') CB * ((Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) :=
              mul_le_mul_of_nonneg_right h1 htail
          _ = max (2 * C') CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by ring
      calc ‖∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖
          ≤ ∑ z ∈ Work.FITop.boxN Pa, ‖(if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖ := norm_sum_le _ _
        _ ≤ Cm * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9:ℕ) := hm
        _ ≤ CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hB'
        _ ≤ max (2 * C') CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hstepB
    · -- ### Case A: the mod-8 character detection
      have hAlt : (Nat.lcm d 2 : ℝ) < 2 * (Real.log Pa.N) ^ (1 / (2 * ε)) := not_le.mp hcaseB
      set D : ℕ := Nat.lcm d 2 with hDdef
      have hDlt : (D : ℝ) < 2 * (Real.log Pa.N) ^ (1 / (2 * ε)) := hAlt
      have hD2 : 2 ≤ D := by
        rw [hDdef]
        exact Nat.le_of_dvd (Nat.lcm_pos (by omega) (by norm_num)) (Nat.dvd_lcm_right d 2)
      have hD1 : 1 ≤ D := le_trans (by norm_num) hD2
      have hDle : D ≤ 2 * d := by
        rw [hDdef]
        exact Nat.le_of_dvd (by omega)
          (Nat.lcm_dvd (dvd_mul_left d 2) (dvd_mul_right 2 d))
      have hloglog : 0 < Real.log (Real.log Pa.N) := Real.log_pos hlogN1
      set V : ℝ := Real.log ((D : ℝ) / 2) / Real.log (Real.log Pa.N) with hVdef
      have hVlt : V < 1 / (2 * ε) := by
        rw [hVdef, div_lt_iff₀ hloglog]
        have h1 : Real.log ((D : ℝ) / 2) < Real.log ((Real.log Pa.N) ^ (1 / (2 * ε))) := by
          refine Real.log_lt_log (by positivity) ?_
          rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
          linarith [hDlt]
        rwa [Real.log_rpow hlogN0] at h1
      set ν' : ℝ := (max V 0 + 1 / (2 * ε)) / 2 with hν'def
      have hν'pos : 0 < ν' := by rw [hν'def]; positivity
      have hν'lt : ν' < 1 / (2 * ε) := by
        have h1 : max V 0 < 1 / (2 * ε) := max_lt hVlt (by positivity)
        rw [hν'def]; linarith
      have hDleν : (D : ℝ) ≤ 2 * (Real.log Pa.N) ^ ν' := by
        have hhalf : (D : ℝ) / 2 ≤ (Real.log Pa.N) ^ ν' := by
          rcases le_total 0 V with hV0 | hV0
          · have hle : V ≤ ν' := by
              have hmax : max V 0 = V := max_eq_left hV0
              rw [hν'def, hmax]; linarith
            have hVeq : (Real.log Pa.N) ^ V = (D : ℝ) / 2 := by
              rw [hVdef, Real.rpow_def_of_pos hlogN0]
              have harg : Real.log (Real.log Pa.N) * (Real.log ((D : ℝ) / 2) / Real.log (Real.log Pa.N))
                  = Real.log ((D : ℝ) / 2) := by
                rw [div_eq_mul_inv]
                calc Real.log (Real.log Pa.N)
                      * (Real.log ((D : ℝ) / 2) * (Real.log (Real.log Pa.N))⁻¹)
                    = Real.log ((D : ℝ) / 2)
                      * (Real.log (Real.log Pa.N) * (Real.log (Real.log Pa.N))⁻¹) := by ring
                  _ = Real.log ((D : ℝ) / 2) := by
                      rw [mul_inv_cancel₀ hloglog.ne', mul_one]
              rw [harg, Real.exp_log (by positivity)]
            calc (D : ℝ) / 2 = (Real.log Pa.N) ^ V := hVeq.symm
              _ ≤ (Real.log Pa.N) ^ ν' := Real.rpow_le_rpow_of_exponent_le hlogN1.le hle
          · have hDse : (D : ℝ) / 2 ≤ 1 := by
              by_contra hc
              push_neg at hc
              have h1 : 0 < Real.log ((D : ℝ) / 2) := Real.log_pos hc
              have h2 : 0 < Real.log ((D : ℝ) / 2) / Real.log (Real.log Pa.N) := div_pos h1 hloglog
              rw [hVdef] at hV0
              linarith
            calc (D : ℝ) / 2 ≤ 1 := hDse
              _ ≤ (Real.log Pa.N) ^ ν' := Real.one_le_rpow hlogN1.le hν'pos.le
        calc (D : ℝ) = 2 * ((D : ℝ) / 2) := by ring
          _ ≤ 2 * (Real.log Pa.N) ^ ν' := by linarith [hhalf]
      by_cases hz0u : Work.FIArea5.S16Hecke.IsUnitMod4d 2 z0
      · -- the detection regime
        have hterm : ∀ (ψ : AddChar (Additive G8) ℂ) (z : GaussianInt),
            ((if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * (chi z * char8Of ψ z)
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)
              = (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then (((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j) * char8Of ψ z else 0)) := by
          intro ψ z
          by_cases h : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z)
          · rw [if_pos h, if_pos h]; ring
          · rw [if_neg h, if_neg h]
        have hpt : ∀ z : GaussianInt, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)
            = (1 / (Fintype.card G8 : ℂ)) * ∑ ψ : AddChar (Additive G8) ℂ,
                star (char8Of ψ z0) * (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j * char8Of ψ z else 0) := by
          intro z
          have hqS : ∀ (_hM0 : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z)) (S : ℂ), (∑ ψ : AddChar (Additive G8) ℂ,
                star (char8Of ψ z0) * (S * char8Of ψ z))
                = S * ((Fintype.card G8 : ℂ) *
                    (if Work.FITop4.SameClass8 z z0 then 1 else 0)) := by
            intro _hM0 S
            have hdet := Work.FIArea6.classDetect8Gauss (z := z) (z0 := z0)
              (isUnitMod4d_two_of_isPrimary _hM0.1) hz0u
            calc (∑ ψ : AddChar (Additive G8) ℂ, star (char8Of ψ z0) * (S * char8Of ψ z))
                = S * ∑ ψ : AddChar (Additive G8) ℂ,
                    star (char8Of ψ z0) * char8Of ψ z := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun ψ _ => by ring
              _ = S * ∑ ψ : AddChar (Additive G8) ℂ,
                    char8Of ψ z * star (char8Of ψ z0) := by
                  congr 1
                  exact Finset.sum_congr rfl fun ψ _ => mul_comm _ _
              _ = S * ((Fintype.card G8 : ℂ) *
                    (if Work.FITop4.SameClass8 z z0 then 1 else 0)) := by rw [hdet]
          by_cases hM0 : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z)
          · by_cases h8 : Work.FITop4.SameClass8 z z0
            · have hM6 : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) := ⟨hM0.1, hM0.2.1, hM0.2.2.1, h8, hM0.2.2.2⟩
              have hNne : (Fintype.card G8 : ℂ) ≠ 0 := by
                exact_mod_cast Fintype.card_ne_zero
              rw [if_pos hM6]
              simp only [if_pos hM0]
              rw [hqS hM0, if_pos h8, mul_one]
              refine Eq.symm ?_
              rw [mul_comm (((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j) ((Fintype.card G8 : ℂ)), ← mul_assoc, one_div,
                inv_mul_cancel₀ hNne, one_mul]
            · have hnotM6 : ¬ ((Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z)) := fun hh => h8 hh.2.2.2.1
              rw [if_neg hnotM6]
              simp only [if_pos hM0]
              rw [hqS hM0, if_neg h8]
              simp
          · have hnotM6 : ¬ ((Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z)) :=
              fun hh => hM0 ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.2⟩
            rw [if_neg hnotM6]
            simp only [if_neg hM0]
            simp
        have hdecomp : (∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0))
            = (1 / (Fintype.card G8 : ℂ)) * ∑ ψ : AddChar (Additive G8) ℂ,
                star (char8Of ψ z0) *
                  (∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * (chi z * char8Of ψ z)
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)) := by
          calc (∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0))
              = ∑ z ∈ Work.FITop.boxN Pa,
                  (1 / (Fintype.card G8 : ℂ)) * ∑ ψ : AddChar (Additive G8) ℂ,
                    star (char8Of ψ z0) * (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then (((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j) * char8Of ψ z else 0) :=
                Finset.sum_congr rfl fun z _ => hpt z
            _ = (1 / (Fintype.card G8 : ℂ)) * ∑ z ∈ Work.FITop.boxN Pa,
                  ∑ ψ : AddChar (Additive G8) ℂ,
                    star (char8Of ψ z0) * (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then (((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j) * char8Of ψ z else 0) := by
                rw [Finset.mul_sum]
            _ = (1 / (Fintype.card G8 : ℂ)) * ∑ ψ : AddChar (Additive G8) ℂ,
                  ∑ z ∈ Work.FITop.boxN Pa,
                    star (char8Of ψ z0) * (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then (((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j) * char8Of ψ z else 0) := by
                rw [Finset.sum_comm]
            _ = (1 / (Fintype.card G8 : ℂ)) * ∑ ψ : AddChar (Additive G8) ℂ,
                  star (char8Of ψ z0) *
                    (∑ z ∈ Work.FITop.boxN Pa,
                      (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then (((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j) * char8Of ψ z else 0)) := by
                congr 1
                exact Finset.sum_congr rfl fun ψ _ => (Finset.mul_sum _ _ _).symm
            _ = (1 / (Fintype.card G8 : ℂ)) * ∑ ψ : AddChar (Additive G8) ℂ,
                  star (char8Of ψ z0) *
                    (∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * (chi z * char8Of ψ z)
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)) := by
                congr 1
                refine Finset.sum_congr rfl fun ψ _ => ?_
                congr 1
                exact Finset.sum_congr rfl fun z _ => (hterm ψ z).symm
        have hbndψ : ∀ ψ : AddChar (Additive G8) ℂ,
            ‖∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * (chi z * char8Of ψ z)
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖
              ≤ 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
          intro ψ
          have hchi' : Work.FIArea5.S16Hecke.IsCharMod4dStrict D
              (fun z => chi z * char8Of ψ z) :=
            strictChar8_mul_aux hd1 hchi (Work.FIArea6.char8Of_isCharMod4dStrict ψ)
          have hnc := hNC Pa hx' φ ν' D j (fun z => chi z * char8Of ψ z) q p
            hTau hAxis hν'pos hν'lt hD1 hDleν hk hchi' hqC hpC hqnn hqle hqsupp hqder hpnn hple hpsupp hpder
          have hE1 : Real.exp (-(Pa.η * c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              ≤ Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N))) := by
            apply Real.exp_le_exp.mpr
            have h4Dpos : (0 : ℝ) < ((4 * D : ℕ) : ℝ) := by positivity
            have h4dpos : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by positivity
            have h4Dle : ((4 * D : ℕ) : ℝ) ≤ 2 * ((4 * d : ℕ) : ℝ) := by
              have h4 : 4 * D ≤ 2 * (4 * d) := by omega
              exact_mod_cast h4
            have hpow : (2 : ℝ) ^ (-ε) * ((4 * d : ℕ) : ℝ) ^ (-ε)
                ≤ ((4 * D : ℕ) : ℝ) ^ (-ε) := by
              have h1 : (2 * ((4 * d : ℕ) : ℝ)) ^ (-ε)
                  = (2 : ℝ) ^ (-ε) * ((4 * d : ℕ) : ℝ) ^ (-ε) :=
                Real.mul_rpow (by norm_num) h4dpos.le
              rw [← h1]
              exact Real.rpow_le_rpow_of_nonpos h4Dpos (by linarith [h4Dle]) (by linarith [hε0])
            have h2 : c' * ((2 : ℝ) ^ (-ε) * ((4 * d : ℕ) : ℝ) ^ (-ε))
                ≤ c' * ((4 * D : ℕ) : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_left hpow hc'0.le
            have h3 : c * ((4 * d : ℕ) : ℝ) ^ (-ε) ≤ c' * ((4 * D : ℕ) : ℝ) ^ (-ε) := by
              rw [hcdef]
              nlinarith [h2]
            have h4 : c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)
                ≤ c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N) :=
              mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
            have h5 := mul_le_mul_of_nonneg_left h4 Pa.hη.le
            linarith [h5]
          have hCmp : C' * (Real.exp (-(Pa.η * c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
              * ((4 * D : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
              ≤ 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
            have h4Dle : ((4 * D : ℕ) : ℝ) ≤ 2 * ((4 * d : ℕ) : ℝ) := by
              have h4 : 4 * D ≤ 2 * (4 * d) := by omega
              exact_mod_cast h4
            have hbr : Real.exp (-(Pa.η * c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                  + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))
                ≤ (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) := by linarith [hE1]
            have hb0 : (0 : ℝ) ≤ (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) := by positivity
            have hslack : C' * (Real.exp (-(Pa.η * c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                  + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
                * ((4 * D : ℕ) : ℝ) ≤ 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) := by
              calc C' * (Real.exp (-(Pa.η * c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                    + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
                    * ((4 * D : ℕ) : ℝ)
                  ≤ C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * (2 * ((4 * d : ℕ) : ℝ)) := by
                    apply mul_le_mul (mul_le_mul_of_nonneg_left hbr hC'0.le) h4Dle (by positivity)
                    positivity
                _ = 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) := by ring
            calc C' * (Real.exp (-(Pa.η * c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                  + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
                  * ((4 * D : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
                ≤ (2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ)) * Pa.N
                    * (Real.log Pa.N) ^ (6 : ℕ) := by
                  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlogN0.le 6)
                  exact mul_le_mul_of_nonneg_right hslack hN0.le
              _ = 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := rfl
          calc ‖∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * (chi z * char8Of ψ z)
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖
              ≤ C' * (Real.exp (-(Pa.η * c' * ((4 * D : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
                  + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
                * ((4 * D : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hnc
            _ ≤ 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hCmp
        have hboundsum : ‖∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖
            ≤ 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
          rw [hdecomp, norm_mul]
          have hnormN : ‖(1 : ℂ) / (Fintype.card G8 : ℂ)‖ = 1 / (Fintype.card G8 : ℝ) := by
            rw [norm_div, norm_one, Complex.norm_natCast]
          calc ‖(1 / (Fintype.card G8 : ℂ))‖ * ‖∑ ψ : AddChar (Additive G8) ℂ,
                  star (char8Of ψ z0) *
                    (∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * (chi z * char8Of ψ z)
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0))‖
              ≤ (1 / (Fintype.card G8 : ℝ)) * ∑ ψ : AddChar (Additive G8) ℂ,
                  ‖star (char8Of ψ z0) *
                    (∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * (chi z * char8Of ψ z)
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0))‖ := by
                rw [hnormN]
                exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
            _ ≤ (1 / (Fintype.card G8 : ℝ)) * ∑ _ψ : AddChar (Additive G8) ℂ,
                  (1 * (2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Finset.sum_le_sum
                intro ψ _
                rw [norm_mul, norm_star]
                refine mul_le_mul ?_ (hbndψ ψ) (norm_nonneg _) (by norm_num)
                exact (Work.FIArea6.char8Of_isCharMod4dStrict ψ).1.2.2.1 z0
            _ = 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
                rw [AddChar.card_eq]
                rw [show Fintype.card (Additive G8) = Fintype.card G8 from rfl]
                have hNne : (((Fintype.card G8 : ℕ)) : ℝ) ≠ 0 := by
                  exact_mod_cast Fintype.card_ne_zero
                rw [← mul_assoc, one_div, inv_mul_cancel₀ hNne, one_mul]
        have hstepA : 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
            ≤ max (2 * C') CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
          have h1 : 2 * C' ≤ max (2 * C') CB := le_max_left _ _
          calc 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
              = (2 * C') * ((Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) := by ring
            _ ≤ max (2 * C') CB * ((Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) :=
                mul_le_mul_of_nonneg_right h1 hbf
            _ = max (2 * C') CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by ring
        calc ‖∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)‖
            ≤ 2 * C' * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hboundsum
          _ ≤ max (2 * C') CB * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := hstepA
      · -- `z0` is not a unit modulo eight: every support point is even, so the sum vanishes
        have hzero : (∑ z ∈ Work.FITop.boxN Pa, (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z) then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j else 0)) = 0 := by
          refine Finset.sum_eq_zero fun z _ => ?_
          by_cases hM6 : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
            (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
            Work.FITop4.IsAxisFree Pa z)
          · exfalso
            exact hz0u (isUnitMod4d_two_of_isPrimary_sameClass8 hM6.1 hM6.2.2.2.1)
          · rw [if_neg hM6]
        rw [hzero, norm_zero]
        have hmax : (0 : ℝ) ≤ max (2 * C') CB :=
          le_of_lt (lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * C') (le_max_left (2 * C') CB))
        have hbr : (0 : ℝ) ≤ Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε)
              * Real.sqrt (Real.log Pa.N)))
            + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))) := by positivity
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hmax hbr) (by positivity)) hN0.le)
          (pow_nonneg hlogN0.le 6)

end

end Work.FIArea6V
