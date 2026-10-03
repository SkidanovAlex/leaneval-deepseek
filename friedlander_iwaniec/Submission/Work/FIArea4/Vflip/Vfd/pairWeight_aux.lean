import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.JacobiFlip.jacobiSym_oddPart_flip
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.A4varbounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for `pairWeight_flip`

This module collects the elementary ingredients of the "flipping of moduli" identity
`pairWeight_flip`:

* `zmod_eq_pairAbs_iff` : the congruence `r₁s₂ ≡ r₂s₁ (mod d)` is the divisibility
  `d ∣ pairC r₁ r₂ * pairAbs r₁ r₂ s₁ s₂`;
* `sum_moebius_divisors_filter` : the Möbius inversion `Σ_{m ∣ c, m ∣ k} μ m = [c ⟂ k]`;
* `jw_mul_eq_pairR` : the Jacobi weight of the pair reduces by the common divisor `pairC`;
* `jw_flip_pairR` : the per-divisor reciprocity flip in `jw`-form;
* the four `PW*` normal forms in which the two sides of `pairWeight_flip` are compared.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about the reduced pair -/

lemma pairC_mul_pairR_left (r1 r2 : ℕ) : pairC r1 r2 * pairR r1 r2 = r1 := by
  simp only [pairC, pairR]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left r1 r2)

lemma pairC_mul_pairR_right (r1 r2 : ℕ) : pairC r1 r2 * pairR r2 r1 = r2 := by
  simp only [pairC, pairR, Nat.gcd_comm r2 r1]
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right r1 r2)

/-- `pairC r₁ r₂ * pairAbs r₁ r₂ s₁ s₂ = |r₁ s₂ − r₂ s₁|`. -/
lemma pairC_mul_pairAbs_eq (r1 r2 s1 s2 : ℕ) :
    pairC r1 r2 * pairAbs r1 r2 s1 s2
      = ((r1:ℤ)*(s2:ℤ) - (r2:ℤ)*(s1:ℤ)).natAbs := by
  have hc1 := pairC_mul_pairR_left r1 r2
  have hc2 := pairC_mul_pairR_right r1 r2
  have e1 : (r1 : ℤ) = (pairC r1 r2 : ℤ) * (pairR r1 r2 : ℤ) := by
    rw [← Nat.cast_mul, hc1]
  have e2 : (r2 : ℤ) = (pairC r1 r2 : ℤ) * (pairR r2 r1 : ℤ) := by
    rw [← Nat.cast_mul, hc2]
  have h : ((r1:ℤ)*(s2:ℤ) - (r2:ℤ)*(s1:ℤ))
      = (pairC r1 r2 : ℤ) * ((pairR r1 r2 : ℤ)*(s2:ℤ) - (pairR r2 r1 : ℤ)*(s1:ℤ)) := by
    rw [e1, e2]; ring
  rw [h, Int.natAbs_mul, pairAbs]
  simp

/-- The congruence condition of `pairWeight` is the divisibility by `pairC * pairAbs`. -/
lemma zmod_eq_pairAbs_iff (r1 s1 r2 s2 d : ℕ) :
    (((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
      ↔ d ∣ pairC r1 r2 * pairAbs r1 r2 s1 s2 := by
  have key1 : (d ∣ ((r1*s2:ℤ) - (r2*s1:ℤ)).natAbs) ↔ (d:ℤ) ∣ ((r1*s2:ℤ) - (r2*s1:ℤ)) := by
    rw [← Int.ofNat_dvd, Int.dvd_natAbs]
  rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd, pairC_mul_pairAbs_eq, key1]
  push_cast
  rw [show ((r2:ℤ)*(s1:ℤ) - (r1:ℤ)*(s2:ℤ))
      = -((r1:ℤ)*(s2:ℤ) - (r2:ℤ)*(s1:ℤ)) by ring, dvd_neg]

/-- Möbius inversion over the common divisors of `c` and `k`: `Σ_{m ∣ c, m ∣ k} μ m = [c ⟂ k]`. -/
theorem sum_moebius_divisors_filter (c k : ℕ) (hc : 0 < c) :
    ∑ m ∈ c.divisors.filter (fun m => m ∣ k), (ArithmeticFunction.moebius m : ℂ)
      = if Nat.Coprime c k then 1 else 0 := by
  have hset : c.divisors.filter (fun m => m ∣ k) = (Nat.gcd c k).divisors := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hmc, hc0⟩, hmk⟩
      exact ⟨Nat.dvd_gcd hmc hmk, (Nat.gcd_pos_of_pos_left k hc).ne'⟩
    · rintro ⟨hmg, hg0⟩
      exact ⟨⟨hmg.trans (Nat.gcd_dvd_left c k), hc.ne'⟩,
        hmg.trans (Nat.gcd_dvd_right c k)⟩
  rw [hset]
  rw [show (∑ m ∈ (c.gcd k).divisors, (ArithmeticFunction.moebius m : ℂ))
      = ∑ m ∈ (c.gcd k).divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℂ) m from rfl]
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := (ArithmeticFunction.moebius : ArithmeticFunction ℂ)),
    ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- The Jacobi weight of a pair reduces by the common divisor `c = pairC r₁ r₂`:
`(r₁|d')(r₂|d') = [c ⟂ d] · (r₁'|d')(r₂'|d')`. -/
theorem jw_mul_eq_pairR (r1 r2 d : ℕ) (hodd1 : Odd r1) (hodd2 : Odd r2) (hd : 0 < d) :
    Work.FIArea4.jw d r1 * Work.FIArea4.jw d r2
      = (if Nat.Coprime (pairC r1 r2) d then 1 else 0)
        * (Work.FIArea4.jw d (pairR r1 r2) * Work.FIArea4.jw d (pairR r2 r1)) := by
  have hcodd : Odd (pairC r1 r2) := by
    simp only [pairC]; exact hodd1.of_dvd_nat (Nat.gcd_dvd_left r1 r2)
  have hc1 := pairC_mul_pairR_left r1 r2
  have hc2 := pairC_mul_pairR_right r1 r2
  have e1 : (r1:ℤ) = (pairC r1 r2 : ℤ) * (pairR r1 r2 : ℤ) := by rw [← Nat.cast_mul, hc1]
  have e2 : (r2:ℤ) = (pairC r1 r2 : ℤ) * (pairR r2 r1 : ℤ) := by rw [← Nat.cast_mul, hc2]
  have hkey1 : Work.FIArea4.jw d r1
      = Work.FIArea4.jw d (pairC r1 r2) * Work.FIArea4.jw d (pairR r1 r2) := by
    rw [Work.FIArea4.jw, Work.FIArea4.jw, Work.FIArea4.jw]
    rw [e1, jacobiSym.mul_left]
    push_cast; ring
  have hkey2 : Work.FIArea4.jw d r2
      = Work.FIArea4.jw d (pairC r1 r2) * Work.FIArea4.jw d (pairR r2 r1) := by
    rw [Work.FIArea4.jw, Work.FIArea4.jw, Work.FIArea4.jw]
    rw [e2, jacobiSym.mul_left]
    push_cast; ring
  by_cases hcop : Nat.Coprime (pairC r1 r2) d
  · rw [if_pos hcop, one_mul, hkey1, hkey2]
    have hcop' : Nat.Coprime (pairC r1 r2) (Work.FIPlan.oddPart d) :=
      hcop.coprime_dvd_right (Work.FIArea4.oddPart_dvd d)
    have hsq : (Work.FIArea4.jw d (pairC r1 r2))^2 = 1 := by
      rw [Work.FIArea4.jw]
      have hj : jacobiSym ((pairC r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart d) ^ 2 = 1 :=
        jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hcop'.gcd_eq_one)
      rw [← Int.cast_pow, hj]; norm_num
    rw [show (Work.FIArea4.jw d (pairC r1 r2) * Work.FIArea4.jw d (pairR r1 r2))
          * (Work.FIArea4.jw d (pairC r1 r2) * Work.FIArea4.jw d (pairR r2 r1))
        = (Work.FIArea4.jw d (pairC r1 r2))^2
          * (Work.FIArea4.jw d (pairR r1 r2) * Work.FIArea4.jw d (pairR r2 r1)) from by ring,
        hsq, one_mul]
  · rw [if_neg hcop, zero_mul]
    have hg : Nat.gcd (pairC r1 r2) d ≠ 1 := fun h => hcop (Nat.coprime_iff_gcd_eq_one.mpr h)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
    have hpc : p ∣ pairC r1 r2 := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpd : p ∣ d := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpodd : Odd p := hcodd.of_dvd_nat hpc
    have hp2 : ¬ (2 ∣ p) := by
      intro h; rw [Nat.odd_iff] at hpodd
      have : p % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      omega
    have hpcross : p ∣ Work.FIPlan.oddPart d :=
      Nat.dvd_ordCompl_of_dvd_not_dvd (p := 2) (d := p) (n := d) hpd hp2
    have hpr1 : p ∣ r1 := hpc.trans (by simp only [pairC]; exact Nat.gcd_dvd_left r1 r2)
    have hg1 : Nat.gcd r1 (Work.FIPlan.oddPart d) ≠ 1 := by
      intro h
      have h2 : p ∣ Nat.gcd r1 (Work.FIPlan.oddPart d) := Nat.dvd_gcd hpr1 hpcross
      rw [h] at h2
      exact Nat.Prime.not_dvd_one hp h2
    haveI : NeZero (Work.FIPlan.oddPart d) := ⟨(Work.FIArea4.oddPart_pos hd.ne').ne'⟩
    have hj0 : Work.FIArea4.jw d r1 = 0 := by
      rw [Work.FIArea4.jw]
      have h0 : jacobiSym (r1:ℤ) (Work.FIPlan.oddPart d) = 0 := by
        rw [jacobiSym.eq_zero_iff_not_coprime (b := Work.FIPlan.oddPart d)]
        rw [Int.gcd_natCast_natCast]
        exact hg1
      rw [h0]; norm_num
    rw [hj0, zero_mul]

/-- The reciprocity flip for the reduced pair, in `jw`-form: for `d ∣ A`,
`(r₁'|d')(r₂'|d') = C · (r₁'|(A/d)')(r₂'|(A/d)')` with `C = (s₁|r₁')(s₂|r₂')`. -/
theorem jw_flip_pairR (r1 s1 r2 s2 d : ℕ) (hodd1 : Odd r1) (hodd2 : Odd r2)
    (h8 : r1 % 8 = r2 % 8) (hs1 : Nat.Coprime s1 r1) (hs2 : Nat.Coprime s2 r2)
    (hA : 0 < pairAbs r1 r2 s1 s2) (hdvd : d ∣ pairAbs r1 r2 s1 s2) (hd : 0 < d) :
    Work.FIArea4.jw d (pairR r1 r2) * Work.FIArea4.jw d (pairR r2 r1)
      = ((jacobiSym (s1:ℤ) (pairR r1 r2) * jacobiSym (s2:ℤ) (pairR r2 r1) : ℤ) : ℂ)
        * (Work.FIArea4.jw (pairAbs r1 r2 s1 s2 / d) (pairR r1 r2)
            * Work.FIArea4.jw (pairAbs r1 r2 s1 s2 / d) (pairR r2 r1)) := by
  have hr1pos : 0 < r1 := by have := Nat.odd_iff.mp hodd1; omega
  have hgpos : 0 < r1.gcd r2 := Nat.gcd_pos_of_pos_left r2 hr1pos
  have hc1 := pairC_mul_pairR_left r1 r2
  have hc2 := pairC_mul_pairR_right r1 r2
  have hodd1' : Odd (pairR r1 r2) := by
    simp only [pairR, pairC]; exact hodd1.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r1 r2))
  have hodd2' : Odd (pairR r2 r1) := by
    simp only [pairR, pairC]; rw [Nat.gcd_comm r2 r1]
    exact hodd2.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right r1 r2))
  have hcop' : Nat.Coprime (pairR r1 r2) (pairR r2 r1) := by
    simp only [pairR, pairC]
    rw [Nat.gcd_comm r2 r1]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have h8' : pairR r1 r2 % 8 = pairR r2 r1 % 8 := by
    have hcm : pairC r1 r2 * pairR r1 r2 ≡ pairC r1 r2 * pairR r2 r1 [MOD 8] := by
      rw [hc1, hc2]; exact h8
    have hgc : Nat.gcd 8 (pairC r1 r2) = 1 := by
      have hodd' : Odd (pairC r1 r2) := by
        simp only [pairC]; exact hodd1.of_dvd_nat (Nat.gcd_dvd_left r1 r2)
      have hcp : Nat.Coprime 8 (pairC r1 r2) := by
        have h2 : Nat.Coprime 2 (pairC r1 r2) := by
          rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
          rw [Nat.odd_iff] at hodd'
          intro h
          have : (pairC r1 r2) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
          omega
        simpa using h2.pow_left 3
      exact hcp.gcd_eq_one
    exact Nat.ModEq.cancel_left_of_coprime hgc hcm
  have hs1' : Nat.Coprime s1 (pairR r1 r2) := by
    simp only [pairR, pairC]
    exact hs1.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r1 r2))
  have hs2' : Nat.Coprime s2 (pairR r2 r1) := by
    simp only [pairR, pairC]; rw [Nat.gcd_comm r2 r1]
    exact hs2.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right r1 r2))
  have hflip := JacobiFlip.jacobiSym_oddPart_flip (r1 := pairR r1 r2) (r2 := pairR r2 r1)
    (s1 := s1) (s2 := s2) (d := d) hodd1' hodd2' hcop' h8' hs1' hs2' hd hdvd
  rw [Work.FIArea4.jw, Work.FIArea4.jw, Work.FIArea4.jw, Work.FIArea4.jw]
  have hAB : (↑(jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart d)) : ℂ)
      * (↑(jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart d)) : ℂ)
      = (↑((jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart d))
          * (jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart d))) : ℂ) := by push_cast; ring
  rw [hAB, hflip, pairAbs]
  push_cast
  ring

/-! ## The four normal forms compared in the proof of `pairWeight_flip` -/

/-- `Σ_{d ∣ pairC·pairAbs} bump(d/D) (r₁|d')(r₂|d')`, the divisor-sum form of `pairWeight`. -/
def PWfull (D r1 r2 s1 s2 : ℕ) : ℂ :=
  ∑ d ∈ (pairC r1 r2 * pairAbs r1 r2 s1 s2).divisors,
    (bump ((d:ℝ)/D) : ℂ) * (Work.FIArea4.jw d r1 * Work.FIArea4.jw d r2)

/-- The reduced form: only the divisors of `pairAbs` coprime to `pairC` occur, and the Jacobi
weights are those of the reduced pair `(pairR r₁ r₂, pairR r₂ r₁)`. -/
def PWred (D r1 r2 s1 s2 : ℕ) : ℂ :=
  ∑ d ∈ (pairAbs r1 r2 s1 s2).divisors.filter (fun d => Nat.Coprime (pairC r1 r2) d),
    (bump ((d:ℝ)/D) : ℂ) * (Work.FIArea4.jw d (pairR r1 r2) * Work.FIArea4.jw d (pairR r2 r1))

/-- The right-hand side of `pairWeight_flip`, verbatim. -/
def PWrhs (D r1 r2 s1 s2 : ℕ) : ℂ :=
  (((jacobiSym (s1 : ℤ) (pairR r1 r2) * jacobiSym (s2 : ℤ) (pairR r2 r1) : ℤ) : ℂ)) *
    ∑ m ∈ (pairC r1 r2).divisors, (ArithmeticFunction.moebius m : ℂ) *
      ∑ q ∈ (pairAbs r1 r2 s1 s2).divisors.filter
          (fun q => m * q ∣ pairAbs r1 r2 s1 s2),
        ((bump (((pairAbs r1 r2 s1 s2 / q : ℕ) : ℝ) / D) : ℂ)) *
          ((jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart q)
            * jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart q) : ℤ) : ℂ)

/-- The Möbius sum of `PWrhs` after carrying out the sum over `m` (the coprimality filter). -/
def PWrhsQ (D r1 r2 s1 s2 : ℕ) : ℂ :=
  (((jacobiSym (s1 : ℤ) (pairR r1 r2) * jacobiSym (s2 : ℤ) (pairR r2 r1) : ℤ) : ℂ)) *
    ∑ q ∈ (pairAbs r1 r2 s1 s2).divisors.filter
        (fun q => Nat.Coprime (pairC r1 r2) (pairAbs r1 r2 s1 s2 / q)),
      ((bump (((pairAbs r1 r2 s1 s2 / q : ℕ) : ℝ) / D) : ℂ)) *
        ((jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart q)
          * jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart q) : ℤ) : ℂ)

end

end Work.FIArea4.Vflip.Vfd
