import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.pairWeight_aux
import Submission.Work.FIArea4.Vflip.JacobiFlip.jacobiSym_oddPart_flip
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The four normal-form steps of `pairWeight_flip`
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma bump_div_eq_zero_of_gt (D d : ℕ) (h : 3*D < d) : bump ((d:ℝ)/D) = 0 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    rw [show (((0:ℕ)):ℝ) = 0 by norm_num, div_zero,
      bump_eq_zero_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  · have hD' : (0:ℝ) < D := by exact_mod_cast hD
    apply bump_eq_zero_of_ge
    rw [le_div_iff₀ hD']
    have : (3:ℝ) * D < d := by exact_mod_cast h
    linarith

theorem pairWeight_eq_PWfull (D r1 s1 r2 s2 : ℕ) (hodd1 : Odd r1) (hodd2 : Odd r2)
    (hA : 0 < pairAbs r1 r2 s1 s2) :
    pairWeight D (r1, s1) (r2, s2) = PWfull D r1 r2 s1 s2 := by
  have hr1pos : 0 < r1 := by have := Nat.odd_iff.mp hodd1; omega
  have hcpos : 0 < pairC r1 r2 := by
    simp only [pairC]; exact Nat.gcd_pos_of_pos_left r2 hr1pos
  have hnpos : 0 < pairC r1 r2 * pairAbs r1 r2 s1 s2 := Nat.mul_pos hcpos hA
  rw [pairWeight, PWfull]
  have h1 : (∑ d ∈ Finset.Icc 1 (3 * D),
        (bump ((d : ℝ) / D) : ℂ) * (if ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)
          then Work.FIArea4.jw d r1 * Work.FIArea4.jw d r2 else 0))
      = ∑ d ∈ Finset.Icc 1 (3 * D),
          (if d ∣ pairC r1 r2 * pairAbs r1 r2 s1 s2 then
            (bump ((d : ℝ) / D) : ℂ) * (Work.FIArea4.jw d r1 * Work.FIArea4.jw d r2) else 0) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases h : ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)
    · rw [if_pos h, if_pos (zmod_eq_pairAbs_iff r1 s1 r2 s2 d |>.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (zmod_eq_pairAbs_iff r1 s1 r2 s2 d |>.mpr hh)),
        mul_zero]
  have hset : (Finset.Icc 1 (3 * D)).filter
        (fun d => d ∣ pairC r1 r2 * pairAbs r1 r2 s1 s2)
      = (pairC r1 r2 * pairAbs r1 r2 s1 s2).divisors.filter (fun d => d ≤ 3 * D) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc⟩
      exact ⟨⟨hc, hnpos.ne'⟩, hb⟩
    · rintro ⟨⟨hc, _⟩, hb⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hc hnpos, hb⟩, hc⟩
  have hS : (∑ d ∈ (pairC r1 r2 * pairAbs r1 r2 s1 s2).divisors.filter (fun d => d ≤ 3 * D),
        (bump ((d : ℝ) / D) : ℂ) * (Work.FIArea4.jw d r1 * Work.FIArea4.jw d r2))
      = ∑ d ∈ (pairC r1 r2 * pairAbs r1 r2 s1 s2).divisors,
        (bump ((d : ℝ) / D) : ℂ) * (Work.FIArea4.jw d r1 * Work.FIArea4.jw d r2) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun x hx hxs => ?_)
    have hxle : ¬ x ≤ 3 * D := fun h => hxs (Finset.mem_filter.mpr ⟨hx, h⟩)
    have h3 : 3 * D < x := by omega
    rw [bump_div_eq_zero_of_gt D x h3]
    simp
  rw [h1, ← Finset.sum_filter, hset, hS]

theorem PWfull_eq_PWred (D r1 r2 s1 s2 : ℕ) (hodd1 : Odd r1) (hodd2 : Odd r2) :
    PWfull D r1 r2 s1 s2 = PWred D r1 r2 s1 s2 := by
  have hr1pos : 0 < r1 := by have := Nat.odd_iff.mp hodd1; omega
  have hcpos : 0 < pairC r1 r2 := by
    simp only [pairC]; exact Nat.gcd_pos_of_pos_left r2 hr1pos
  rw [PWfull, PWred]
  have h1 : (∑ d ∈ (pairC r1 r2 * pairAbs r1 r2 s1 s2).divisors,
        (bump ((d:ℝ)/D) : ℂ) * (Work.FIArea4.jw d r1 * Work.FIArea4.jw d r2))
      = ∑ d ∈ (pairC r1 r2 * pairAbs r1 r2 s1 s2).divisors.filter
            (fun d => Nat.Coprime (pairC r1 r2) d),
          (bump ((d:ℝ)/D) : ℂ)
            * (Work.FIArea4.jw d (pairR r1 r2) * Work.FIArea4.jw d (pairR r2 r1)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [jw_mul_eq_pairR r1 r2 d hodd1 hodd2 hdpos]
    by_cases hcop : Nat.Coprime (pairC r1 r2) d
    · simp only [if_pos hcop, one_mul]
    · simp only [if_neg hcop, zero_mul, mul_zero]
  have h2 : (pairC r1 r2 * pairAbs r1 r2 s1 s2).divisors.filter
          (fun d => Nat.Coprime (pairC r1 r2) d)
      = (pairAbs r1 r2 s1 s2).divisors.filter (fun d => Nat.Coprime (pairC r1 r2) d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdvd, hne⟩, hcop⟩
      have hdvd' : d ∣ pairAbs r1 r2 s1 s2 * pairC r1 r2 := by
        rw [mul_comm]; exact hdvd
      have hAne : pairAbs r1 r2 s1 s2 ≠ 0 := by
        rintro h0; exact hne (by rw [h0, mul_zero])
      exact ⟨⟨hcop.symm.dvd_of_dvd_mul_right hdvd', hAne⟩, hcop⟩
    · rintro ⟨⟨hdvd, hne⟩, hcop⟩
      obtain ⟨k, hk⟩ := hdvd
      exact ⟨⟨⟨k * pairC r1 r2, by rw [hk]; ring⟩,
        Nat.mul_ne_zero hcpos.ne' hne⟩, hcop⟩
  rw [h1, h2]

theorem PWrhs_eq_PWrhsQ (D r1 r2 s1 s2 : ℕ) (hodd1 : Odd r1)
    (hA : 0 < pairAbs r1 r2 s1 s2) :
    PWrhs D r1 r2 s1 s2 = PWrhsQ D r1 r2 s1 s2 := by
  have hr1pos : 0 < r1 := by have := Nat.odd_iff.mp hodd1; omega
  have hcpos : 0 < pairC r1 r2 := by
    simp only [pairC]; exact Nat.gcd_pos_of_pos_left r2 hr1pos
  rw [PWrhs, PWrhsQ]
  congr 1
  set X : ℕ → ℂ := fun q => (bump (((pairAbs r1 r2 s1 s2 / q : ℕ) : ℝ) / D) : ℂ) *
      ((jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart q)
        * jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart q) : ℤ) : ℂ) with hX
  have step1 : (∑ m ∈ (pairC r1 r2).divisors, (ArithmeticFunction.moebius m : ℂ) *
        ∑ q ∈ (pairAbs r1 r2 s1 s2).divisors.filter (fun q => m * q ∣ pairAbs r1 r2 s1 s2),
          X q)
      = ∑ m ∈ (pairC r1 r2).divisors, ∑ q ∈ (pairAbs r1 r2 s1 s2).divisors,
          if m * q ∣ pairAbs r1 r2 s1 s2 then (ArithmeticFunction.moebius m : ℂ) * X q else 0 := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : m * q ∣ pairAbs r1 r2 s1 s2
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, mul_zero]
  have step3 : ∀ q ∈ (pairAbs r1 r2 s1 s2).divisors,
      (∑ m ∈ (pairC r1 r2).divisors,
          if m * q ∣ pairAbs r1 r2 s1 s2 then (ArithmeticFunction.moebius m : ℂ) * X q else 0)
      = if Nat.Coprime (pairC r1 r2) (pairAbs r1 r2 s1 s2 / q) then X q else 0 := by
    intro q hq
    have hqdvd : q ∣ pairAbs r1 r2 s1 s2 := Nat.dvd_of_mem_divisors hq
    have hmul : ∀ m, m * q ∣ pairAbs r1 r2 s1 s2 ↔ m ∣ pairAbs r1 r2 s1 s2 / q := by
      intro m
      rw [Nat.dvd_div_iff_mul_dvd hqdvd]
      exact ⟨fun h => by rwa [Nat.mul_comm] at h, fun h => by rwa [Nat.mul_comm] at h⟩
    calc ∑ m ∈ (pairC r1 r2).divisors,
            (if m * q ∣ pairAbs r1 r2 s1 s2 then (ArithmeticFunction.moebius m : ℂ) * X q else 0)
        = ∑ m ∈ (pairC r1 r2).divisors,
            (if m ∣ pairAbs r1 r2 s1 s2 / q then (ArithmeticFunction.moebius m : ℂ) * X q else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          by_cases hm : m * q ∣ pairAbs r1 r2 s1 s2
          · rw [if_pos hm, if_pos ((hmul m).mp hm)]
          · rw [if_neg hm, if_neg (fun h => hm ((hmul m).mpr h))]
      _ = (∑ m ∈ (pairC r1 r2).divisors,
            (if m ∣ pairAbs r1 r2 s1 s2 / q then (ArithmeticFunction.moebius m : ℂ) else 0)) * X q := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          by_cases hm : m ∣ pairAbs r1 r2 s1 s2 / q
          · rw [if_pos hm, if_pos hm]
          · rw [if_neg hm, if_neg hm, zero_mul]
      _ = (∑ m ∈ (pairC r1 r2).divisors.filter (fun m => m ∣ pairAbs r1 r2 s1 s2 / q),
            (ArithmeticFunction.moebius m : ℂ)) * X q := by rw [Finset.sum_filter]
      _ = (if Nat.Coprime (pairC r1 r2) (pairAbs r1 r2 s1 s2 / q) then 1 else 0) * X q := by
          rw [sum_moebius_divisors_filter (pairC r1 r2) (pairAbs r1 r2 s1 s2 / q) hcpos]
      _ = if Nat.Coprime (pairC r1 r2) (pairAbs r1 r2 s1 s2 / q) then X q else 0 := by
          by_cases h : Nat.Coprime (pairC r1 r2) (pairAbs r1 r2 s1 s2 / q)
          · rw [if_pos h, if_pos h, one_mul]
          · rw [if_neg h, if_neg h, zero_mul]
  rw [step1, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q hq => step3 q hq)

theorem PWrhsQ_eq_PWred (D r1 r2 s1 s2 : ℕ) (hodd1 : Odd r1) (hodd2 : Odd r2)
    (h8 : r1 % 8 = r2 % 8) (hs1 : Nat.Coprime s1 r1) (hs2 : Nat.Coprime s2 r2)
    (hA : 0 < pairAbs r1 r2 s1 s2) :
    PWrhsQ D r1 r2 s1 s2 = PWred D r1 r2 s1 s2 := by
  have hAne : pairAbs r1 r2 s1 s2 ≠ 0 := hA.ne'
  rw [PWrhsQ, PWred]
  set C : ℂ := ((jacobiSym (s1:ℤ) (pairR r1 r2) * jacobiSym (s2:ℤ) (pairR r2 r1) : ℤ) : ℂ)
    with hCdef
  set X : ℕ → ℂ := fun q => (bump (((pairAbs r1 r2 s1 s2 / q : ℕ) : ℝ) / D) : ℂ) *
      ((jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart q)
        * jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart q) : ℤ) : ℂ) with hX
  set G : ℕ → ℂ := fun d => (bump ((d:ℝ)/D) : ℂ) *
      (Work.FIArea4.jw d (pairR r1 r2) * Work.FIArea4.jw d (pairR r2 r1)) with hG
  have hC2 : C * C = 1 := by
    have hs1' : Nat.Coprime s1 (pairR r1 r2) := by
      simp only [pairR, pairC]
      exact hs1.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r1 r2))
    have hs2' : Nat.Coprime s2 (pairR r2 r1) := by
      simp only [pairR, pairC]; rw [Nat.gcd_comm r2 r1]
      exact hs2.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right r1 r2))
    have h1 : jacobiSym (s1:ℤ) (pairR r1 r2) ^ 2 = 1 :=
      jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hs1'.gcd_eq_one)
    have h2 : jacobiSym (s2:ℤ) (pairR r2 r1) ^ 2 = 1 :=
      jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hs2'.gcd_eq_one)
    have hprod : (jacobiSym (s1:ℤ) (pairR r1 r2) * jacobiSym (s2:ℤ) (pairR r2 r1))
        * (jacobiSym (s1:ℤ) (pairR r1 r2) * jacobiSym (s2:ℤ) (pairR r2 r1)) = (1:ℤ) := by
      rw [show (jacobiSym (s1:ℤ) (pairR r1 r2) * jacobiSym (s2:ℤ) (pairR r2 r1))
            * (jacobiSym (s1:ℤ) (pairR r1 r2) * jacobiSym (s2:ℤ) (pairR r2 r1))
          = jacobiSym (s1:ℤ) (pairR r1 r2)^2 * jacobiSym (s2:ℤ) (pairR r2 r1)^2 by ring,
        h1, h2, mul_one]
    rw [hCdef, ← Int.cast_mul, hprod, Int.cast_one]
  have stepX : ∀ d ∈ (pairAbs r1 r2 s1 s2).divisors,
      X (pairAbs r1 r2 s1 s2 / d) = C * G d := by
    intro d hd
    have hdvd : d ∣ pairAbs r1 r2 s1 s2 := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdiv : pairAbs r1 r2 s1 s2 / (pairAbs r1 r2 s1 s2 / d) = d :=
      Nat.div_div_self hdvd hAne
    rw [hX, hG]
    simp only []
    rw [show ((jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart (pairAbs r1 r2 s1 s2 / d))
          * jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart (pairAbs r1 r2 s1 s2 / d)) : ℤ) : ℂ)
        = Work.FIArea4.jw (pairAbs r1 r2 s1 s2 / d) (pairR r1 r2)
            * Work.FIArea4.jw (pairAbs r1 r2 s1 s2 / d) (pairR r2 r1) from by
          rw [Work.FIArea4.jw, Work.FIArea4.jw]; push_cast; ring]
    rw [jw_flip_pairR r1 s1 r2 s2 (pairAbs r1 r2 s1 s2 / d) hodd1 hodd2 h8 hs1 hs2 hA
        (Nat.div_dvd_of_dvd hdvd) (Nat.div_pos (Nat.le_of_dvd hA hdvd) hdpos)]
    rw [hdiv]
    ring
  have reindex :
      (∑ q ∈ (pairAbs r1 r2 s1 s2).divisors.filter
          (fun q => Nat.Coprime (pairC r1 r2) (pairAbs r1 r2 s1 s2 / q)), X q)
      = ∑ d ∈ (pairAbs r1 r2 s1 s2).divisors.filter (fun d => Nat.Coprime (pairC r1 r2) d),
          X (pairAbs r1 r2 s1 s2 / d) := by
    refine Finset.sum_bij (fun q _ => pairAbs r1 r2 s1 s2 / q) ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hq.1), hAne⟩,
        hq.2⟩
    · intro a1 ha1 a2 ha2 h
      have h1 : a1 = pairAbs r1 r2 s1 s2 / (pairAbs r1 r2 s1 s2 / a1) :=
        (Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ha1).1) hAne).symm
      rw [h1, h]
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ha2).1) hAne
    · intro d hd
      refine ⟨pairAbs r1 r2 s1 s2 / d, ?_,
        Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hAne⟩
      rw [Finset.mem_filter]
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1), hAne⟩, ?_⟩
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hAne]
      exact (Finset.mem_filter.mp hd).2
    · intro q hq
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hq).1) hAne]
  rw [reindex, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdA : d ∈ (pairAbs r1 r2 s1 s2).divisors := (Finset.mem_filter.mp hd).1
  rw [stepX d hdA]
  rw [show C * (C * G d) = (C * C) * G d by ring, hC2, one_mul]


end

end Work.FIArea4.Vflip.Vfd
