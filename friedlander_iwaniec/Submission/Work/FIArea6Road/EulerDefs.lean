/-
# `Submission.Work.FIArea6Road.EulerDefs` — vocabulary for the Euler-product regrouping

The regrouping `Z(s) = M(s)·P(s)·Q(s)` of *FI* (16.30)–(16.34) for the Möbius-twisted Hecke
series of `TsumHeartDefs`.  The three factors `Mfac`, `Pfac`, `Qfac` are already defined in
`Submission.Work.FIArea6.TauPieces.TsumHeartDefs`; this module introduces the auxiliary objects
the proof is organised around:

* `PiPr Pa = Π = ∏_{p ≤ Pz} p`, the small-prime modulus;
* `locF χ m s p = 1 - λ_m(p)·p^{-s}`, the local Euler factor;
* `Wfac Pa χ m s = ∏_{p > Pz} locF`, i.e. the product `M(s)·P(s)`;
* `Gser Pa χ m s Q = Σ_{(n,Q)=1} λ_m(n)μ(n)n^{-s}`, the "shifted" series;
* `Fcoef Pa χ m s N = 1_{(N,Π)=1} λ_m(N)μ(N)N^{-s}`, the coefficient of `Z` before the
  truncation `γ`.
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.heckeLam_one
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg

set_option autoImplicit false

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `Π = ∏_{p ≤ Pz} p`, the product of the small primes. -/
def PiPr (Pa : Work.FITop.Params) : ℕ := ∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p

/-- The local Euler factor `1 - λ_m(p)·p^{-s}` of (16.31)/(16.33). -/
def locF (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (p : ℕ) : ℂ :=
  1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)

/-- `W = ∏_{p > Pz} (1 - λ(p)p^{-s})`, the product `M(s)·P(s)` of (16.31)/(16.33). -/
def Wfac (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (if (p : ℕ) ≤ Pa.Pz then 1 else locF chi m s (p : ℕ))

/-- `G(Q) = Σ_{(n,Q)=1} λ_m(n)μ(n)n^{-s}`, the "shifted" series of (16.30). -/
def Gser (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (Q : ℕ) : ℂ :=
  ∑' n : ℕ, (if Nat.Coprime n Q then 1 else 0)
    * (Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ))
    * (n : ℂ) ^ (-s)

/-- `F(N) = 1_{(N,Π)=1} λ_m(N)μ(N)N^{-s}`, the coefficient of `Z` without the truncation `γ`. -/
def Fcoef (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (N : ℕ) : ℂ :=
  (if Nat.Coprime N (PiPr Pa) then 1 else 0)
    * (Work.FIArea5.S16Hecke.heckeLam chi m N * (ArithmeticFunction.moebius N : ℂ))
    * (N : ℂ) ^ (-s)

lemma Mfac_eq_tprod_locF (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    Work.FIArea6.TauPieces.Mfac chi m s = ∏' p : Nat.Primes, locF chi m s (p : ℕ) := rfl

lemma Pfac_eq_prod_inv (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    Work.FIArea6.TauPieces.Pfac Pa chi m s
      = ∏ p ∈ Nat.primesBelow (Pa.Pz + 1), (locF chi m s p)⁻¹ := rfl

lemma Qfac_eq (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    Work.FIArea6.TauPieces.Qfac Pa chi m s
      = ∑ c ∈ (Finset.Icc 1 ⌊Pa.C⌋₊).filter
          (fun c => Squarefree c ∧ Nat.Coprime c (PiPr Pa)),
          Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
            * ∏ p ∈ c.primeFactors, (locF chi m s p)⁻¹ := rfl

lemma Zsfun_eq_tsum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    Work.FIArea6.TauPieces.Zsfun Pa chi m s
      = ∑' N : ℕ, Work.FIArea6.TauPieces.tcoef Pa chi m N * (N : ℂ) ^ (-s) := rfl

/-- `n` is coprime to `Π` iff no prime `≤ Pz` divides it. -/
lemma NoSmallPrimesNat_iff_coprime (Pa : Work.FITop.Params) (n : ℕ) :
    Work.FIArea6Hecke.NoSmallPrimesNat Pa n ↔ Nat.Coprime n (PiPr Pa) := by
  rw [Work.FIArea6Hecke.NoSmallPrimesNat, PiPr, Nat.coprime_prod_right_iff]
  constructor
  · intro h q hq
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Nat.mem_primesBelow.mp hq).2]
    exact fun hqd => h q (Nat.mem_primesBelow.mp hq).2
      (by have := Nat.mem_primesBelow.mp hq; omega) hqd
  · intro h q hq hqle hqd
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mp (Nat.coprime_comm.mpr
      (h q (Nat.mem_primesBelow.mpr ⟨by omega, hq⟩)))) hqd

lemma one_le_PiPr (Pa : Work.FITop.Params) : 1 ≤ PiPr Pa := by
  rw [PiPr]
  exact Finset.one_le_prod₀ fun p hp => (Nat.prime_of_mem_primesBelow hp).one_le

lemma two_le_PiPr (Pa : Work.FITop.Params) : 2 ≤ PiPr Pa := by
  rw [PiPr]
  refine Finset.single_le_prod' (fun p hp => (Nat.prime_of_mem_primesBelow hp).one_le)
    (Nat.mem_primesBelow.mpr ⟨by have := Pa.hP2; omega, Nat.prime_two⟩)

/-- `‖λ_m(p)‖ ≤ 2` at a rational prime. -/
lemma norm_heckeLam_prime_le_two {chi : GaussianInt → ℂ} (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (m : ℤ) {p : ℕ} (hp : p.Prime) : ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ≤ 2 := by
  by_cases h4 : p % 4 = 1
  · exact Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two hp h4 hb
  · rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four hp h4]; norm_num

/-- For a prime `q`, `q ∣ Π` exactly when `q ≤ Pz`. -/
lemma prime_dvd_PiPr_iff {Pa : Work.FITop.Params} {q : ℕ} (hq : q.Prime) :
    q ∣ PiPr Pa ↔ q ≤ Pa.Pz := by
  rw [PiPr]
  constructor
  · intro h
    obtain ⟨p, hp, hpq⟩ := (Prime.dvd_finsetProd_iff hq.prime (fun x => x)).mp h
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hpp).mp hpq
    have := Nat.mem_primesBelow.mp hp
    omega
  · intro hle
    exact Finset.dvd_prod_of_mem (fun x => x) (Nat.mem_primesBelow.mpr ⟨by omega, hq⟩)

/-- `Σ_p ‖locF p - 1‖` converges for `re s > 1`. -/
lemma summable_norm_locF_sub_one (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => ‖locF chi m s (p : ℕ) - 1‖) := by
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (((Nat.Primes.summable_rpow (r := -s.re)).mpr (by linarith)).mul_left 2)
  have hde : locF chi m s (p : ℕ) - 1
      = -(Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) := by
    rw [locF]; ring
  rw [hde, norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos (-s), Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (norm_heckeLam_prime_le_two hchibd m p.2)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The Euler product `∏_p locF p` is multipliable for `re s > 1`. -/
lemma multipliable_locF (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : Nat.Primes => locF chi m s (p : ℕ)) :=
  (multipliable_one_add_of_summable (summable_norm_locF_sub_one chi m hchibd hs)).congr
    (fun p => by ring)

/-- Any sub-product of the multipliable family `locF` is multipliable (written with multiplicative
indicators). -/
lemma multipliable_locF_indicator (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (S : Set Nat.Primes) :
    Multipliable (fun p : Nat.Primes => S.mulIndicator (fun q : Nat.Primes => locF chi m s (q : ℕ)) p) := by
  refine (multipliable_one_add_of_summable (f := fun p : Nat.Primes =>
    S.mulIndicator (fun q : Nat.Primes => locF chi m s (q : ℕ)) p - 1) ?_).congr
    (fun p => by ring)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (summable_norm_locF_sub_one chi m hchibd hs)
  by_cases hp : p ∈ S
  · rw [Set.mulIndicator_of_mem hp]
  · rw [Set.mulIndicator_of_notMem hp]
    simp

/-- The local factor `1 - λ_m(p)p^{-s}` does not vanish for `re s > 1`. -/
lemma locF_ne_zero (chi : GaussianInt → ℂ) (m : ℤ) {s : ℂ} (hs : 1 < s.re)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    locF chi m s p ≠ 0 := by
  intro h
  have h2 : Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s) = 1 := by
    have hh := h
    rw [locF, sub_eq_zero] at hh
    exact hh.symm
  have hbnd : ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ≤ 2 :=
    norm_heckeLam_prime_le_two hchibd m hp
  have h3 : ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖ ≤ 2 * (p : ℝ) ^ (-s.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos (-s), Complex.neg_re]
    exact mul_le_mul_of_nonneg_right hbnd (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  rw [h2, norm_one] at h3
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h4 : (p : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have h5 : (2 : ℝ) ^ (-s.re) < 1 / 2 := by
    have h6 : (2 : ℝ) ^ (-s.re) < (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
    have h7 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num [Real.rpow_neg_one]
    rw [h7] at h6
    linarith
  linarith

/-- The norm of `N^{-s}` as a real power. -/
lemma norm_natCast_cpow_neg (N : ℕ) {s : ℂ} (hs : s.re ≠ 0) :
    ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hs0 : (-s) ≠ 0 := by
      rw [neg_ne_zero]; intro h; exact hs (by simp [h])
    have h1 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
      rw [Nat.cast_zero]; exact Complex.zero_cpow hs0
    have h2 : ((0 : ℕ) : ℝ) ^ (-s.re) = 0 := by
      rw [Nat.cast_zero]; exact Real.zero_rpow (by simpa using hs)
    rw [h1, h2, norm_zero]
  · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN) (-s)]
    simp [Complex.neg_re]

lemma norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

/-- `Fcoef` is absolutely summable for `re s > 1`. -/
lemma summable_norm_Fcoef (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) {s : ℂ}
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun N : ℕ => ‖Fcoef Pa chi m s N‖) := by
  have hsre : s.re ≠ 0 := by linarith
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_)
    ((Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg hs).mul_left 4)
  have h1 : ‖Fcoef Pa chi m s N‖
      ≤ ‖Work.FIArea5.S16Hecke.heckeLam chi m N * (ArithmeticFunction.moebius N : ℂ)‖
          * (N : ℝ) ^ (-s.re) := by
    rw [Fcoef, norm_mul, norm_mul, norm_natCast_cpow_neg N hsre]
    have h2 : ‖(if Nat.Coprime N (PiPr Pa) then (1 : ℂ) else 0)‖ ≤ 1 := by
      split <;> simp
    calc ‖(if Nat.Coprime N (PiPr Pa) then (1 : ℂ) else 0)‖
            * ‖Work.FIArea5.S16Hecke.heckeLam chi m N * (ArithmeticFunction.moebius N : ℂ)‖
            * (N : ℝ) ^ (-s.re)
        ≤ 1 * ‖Work.FIArea5.S16Hecke.heckeLam chi m N * (ArithmeticFunction.moebius N : ℂ)‖
            * (N : ℝ) ^ (-s.re) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖Work.FIArea5.S16Hecke.heckeLam chi m N * (ArithmeticFunction.moebius N : ℂ)‖
            * (N : ℝ) ^ (-s.re) := by ring
  have h4 : ‖Work.FIArea5.S16Hecke.heckeLam chi m N * (ArithmeticFunction.moebius N : ℂ)‖
      ≤ 4 * (N.divisors.card : ℝ) := by
    rw [norm_mul]
    rcases eq_or_ne N 0 with rfl | hN
    · simp [Work.FIArea5.S16Hecke.heckeLam_zero]
    · have hm := Work.FIArea5.S16Hecke.heckeLam_bound chi m hchibd (n := N)
        (Nat.one_le_iff_ne_zero.mpr hN)
      calc ‖Work.FIArea5.S16Hecke.heckeLam chi m N‖ * ‖(ArithmeticFunction.moebius N : ℂ)‖
          ≤ (4 * (N.divisors.card : ℝ)) * 1 :=
            mul_le_mul hm (norm_moebius_le_one N) (norm_nonneg _) (by positivity)
        _ = 4 * (N.divisors.card : ℝ) := by ring
  calc ‖Fcoef Pa chi m s N‖
      ≤ (4 * (N.divisors.card : ℝ)) * (N : ℝ) ^ (-s.re) :=
        le_trans h1 (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = 4 * ((N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re)) := by ring

end

end Work.FIArea6Road
