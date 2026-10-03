import Mathlib
import Submission.Work.FIArea7.prop232Defs
import Submission.Work.FIArea7.KStarDiscDefs
import Submission.Work.FIArea7.KStar_bound
import Submission.Work.FIArea7.KSum_bound
import Submission.Work.FIArea7.exists_omega
import Submission.Work.FIArea7.card_bad_r_le
import Submission.Work.FIArea7.sum_sqrt_Icc_le
import Submission.Work.FIArea7.sum_inv_sqrt_Icc_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem good_pointwise_disc :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (w : GaussianInt) (k : ℤ)
      (chi : GaussianInt → ℂ) (N : ℕ),
      Work.FIPlan.IsPrimary w → IsCoprime w.re w.im → 1 ≤ N →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∀ (a b : ℤ), chi (⟨a, b + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a, b⟩) →
      ∀ r ∈ Finset.Icc (-(Work.FIArea7.discSqrt N)) (Work.FIArea7.discSqrt N),
      Odd r → Work.FIArea7.goodR d (Work.FIPlan.gnorm w) r →
      ‖Work.FIArea7.KInnerStar (Work.FIArea7.discFib N r) w k chi r‖
        ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ)
            * ((((Work.FIPlan.gnorm w)).divisors).card : ℝ)
            * (Real.sqrt |(r : ℝ)| + 2 * (Work.FIArea7.discSqrt N : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹)
            * Real.log (2 + Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) * (N : ℝ)) := by
  obtain ⟨Cg, hCgpos, hGood⟩ := KInnerStar_good_bound_exists
  refine ⟨2 * Cg, by positivity, ?_⟩
  intro d hd w k chi N hw hcop hN hchi hper2 r hrIcc hrOdd hrGood
  obtain ⟨ω, hωsq, hωlin⟩ := exists_omega w hw hcop
  have hrn : r ≠ 0 := goodR_ne_zero hrGood
  have h1 := hGood d hd (discFib N r) (discFib_nonneg N r) w k chi r ω hw hcop hchi hper2
    hrOdd hrn hωlin hωsq hrGood
  set A : ℝ := Cg * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ)
      * ((((Work.FIPlan.gnorm w)).divisors).card : ℝ) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have h2 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ |(k:ℝ)|+1 := by positivity
    have h4 : (0:ℝ) ≤ Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) := Real.sqrt_nonneg _
    have h5 : (0:ℝ) ≤ (((Work.FIPlan.gnorm w)).divisors).card := Nat.cast_nonneg _
    positivity
  have hbr1 : Real.sqrt |(r : ℝ)| + 2 * ((discFib N r : ℤ) : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹
      ≤ Real.sqrt |(r : ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹ := by
    have h2 : ((discFib N r : ℤ) : ℝ) ≤ (discSqrt N : ℝ) := by
      exact_mod_cast discFib_le_discSqrt N r
    have h3 : 0 ≤ (Real.sqrt |(r : ℝ)|)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    nlinarith [h2, h3]
  have hbr0 : 0 ≤ Real.sqrt |(r : ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹ := by
    have h1 : 0 ≤ Real.sqrt |(r:ℝ)| := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ (discSqrt N : ℝ) := by exact_mod_cast discSqrt_nonneg N
    have h3 : 0 ≤ (Real.sqrt |(r:ℝ)|)⁻¹ := inv_nonneg.mpr h1
    nlinarith [h1, h2, h3]
  have hlg0 : 0 ≤ Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ)) := by
    apply Real.log_nonneg
    have h1 : (0:ℝ) ≤ (r.natAbs : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ (((Work.FIPlan.gnorm w : ℕ)) : ℝ) := Nat.cast_nonneg _
    have h3 := mul_nonneg h1 h2
    linarith
  have hlg2 : Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ))
      ≤ 2 * Real.log (2 + Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) * (N : ℝ)) :=
    log_discFib_le (Work.FIPlan.gnorm w) N r hN hrIcc
  calc ‖KInnerStar (discFib N r) w k chi r‖
      ≤ A * (Real.sqrt |(r : ℝ)| + 2 * ((discFib N r : ℤ) : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹)
          * Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ)) := h1
    _ ≤ A * (Real.sqrt |(r : ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹)
          * Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr1 hA0) hlg0
    _ ≤ A * (Real.sqrt |(r : ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹)
          * (2 * Real.log (2 + Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hlg2 (mul_nonneg hA0 hbr0)
    _ = 2 * Cg * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ)
          * ((((Work.FIPlan.gnorm w)).divisors).card : ℝ)
          * (Real.sqrt |(r : ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹)
          * Real.log (2 + Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) * (N : ℝ)) := by
        rw [hAdef]; ring

open Classical in
theorem bad_sum_bound_disc :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (w : GaussianInt) (k : ℤ)
      (chi : GaussianInt → ℂ) (N : ℕ),
      Work.FIPlan.IsPrimary w → IsCoprime w.re w.im → 1 ≤ N →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∑ r ∈ (Finset.Icc (-(Work.FIArea7.discSqrt N)) (Work.FIArea7.discSqrt N)).filter
          (fun r : ℤ => Odd r ∧ ¬ Work.FIArea7.goodR d (Work.FIPlan.gnorm w) r),
        ‖Work.FIArea7.KInnerStar (Work.FIArea7.discFib N r) w k chi r‖)
        ≤ C * (d : ℝ) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ)
            * ((Work.FIArea7.discSqrt N : ℝ) * Real.sqrt (Work.FIArea7.discSqrt N : ℝ)) := by
  refine ⟨144, by norm_num, ?_⟩
  intro d hd w k chi N hw hcop hN hchi
  have hw0 : w ≠ 0 := by rintro rfl; exact Int.not_odd_zero (by simpa using hw.1)
  have hq1 : 1 ≤ Work.FIPlan.gnorm w :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hw0 (gnorm_eq_zero_iff.mp h))
  have hR1 : 1 ≤ discSqrt N := one_le_discSqrt hN
  have hR0 : (0:ℝ) ≤ (discSqrt N : ℝ) := by exact_mod_cast discSqrt_nonneg N
  have hR1r : (1:ℝ) ≤ (discSqrt N : ℝ) := by exact_mod_cast hR1
  set F : Finset ℤ := (Finset.Icc (-(discSqrt N)) (discSqrt N)).filter
      (fun r : ℤ => Odd r ∧ ¬ goodR d (Work.FIPlan.gnorm w) r) with hFdef
  have hpt : ∀ r ∈ F, ‖KInnerStar (discFib N r) w k chi r‖ ≤ 2 * (discSqrt N : ℝ) + 1 := by
    intro r hr
    have h1 := KInnerStar_le_card (discFib N r) w k chi r hchi
    have h2 : ((((2 * discFib N r + 1).toNat : ℕ)) : ℝ) ≤ 2 * (discSqrt N : ℝ) + 1 := by
      have h4 : discFib N r ≤ discSqrt N := discFib_le_discSqrt N r
      have h5 : 0 ≤ 2 * discFib N r + 1 := by linarith [discFib_nonneg N r]
      have h6 : 0 ≤ 2 * discSqrt N + 1 := by linarith [discSqrt_nonneg N]
      have h3 : (2 * discFib N r + 1).toNat ≤ (2 * discSqrt N + 1).toNat :=
        Int.toNat_le_toNat (by omega)
      calc ((((2 * discFib N r + 1).toNat : ℕ)) : ℝ)
          ≤ ((((2 * discSqrt N + 1).toNat : ℕ)) : ℝ) := by exact_mod_cast h3
        _ = 2 * (discSqrt N : ℝ) + 1 := by
            have h7 : ((((2 * discSqrt N + 1).toNat : ℕ)) : ℤ) = 2 * discSqrt N + 1 :=
              Int.toNat_of_nonneg h6
            exact_mod_cast h7
    linarith
  have hsum : (∑ r ∈ F, ‖KInnerStar (discFib N r) w k chi r‖)
      ≤ ((F.card : ℝ)) * (2 * (discSqrt N : ℝ) + 1) := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := card_bad_r_le d (Work.FIPlan.gnorm w) hd hq1 (discSqrt N)
  have hmax : max (discSqrt N) 0 = discSqrt N := max_eq_left (discSqrt_nonneg N)
  rw [hmax] at hcard
  have hcard' : (F.card : ℝ)
      ≤ 24 * (d:ℝ) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) * (Real.sqrt (discSqrt N : ℝ) + 1) := by
    simpa [hFdef, goodR, discSqrt] using hcard
  have hkey : (24 * (d:ℝ) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) * (Real.sqrt (discSqrt N : ℝ) + 1))
      * (2 * (discSqrt N : ℝ) + 1)
      ≤ 144 * (d:ℝ) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ)
          * ((discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ)) := by
    have hs0 : (0:ℝ) ≤ Real.sqrt (discSqrt N : ℝ) := Real.sqrt_nonneg _
    have hs1 : (1:ℝ) ≤ Real.sqrt (discSqrt N : ℝ) := Real.one_le_sqrt.mpr hR1r
    have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
    have hq0 : (0:ℝ) ≤ Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) := Real.sqrt_nonneg _
    have h1 : Real.sqrt (discSqrt N : ℝ) + 1 ≤ 2 * Real.sqrt (discSqrt N : ℝ) := by linarith
    have h2 : 2 * (discSqrt N : ℝ) + 1 ≤ 3 * (discSqrt N : ℝ) := by
      have := hR1r; nlinarith
    have h3 : (Real.sqrt (discSqrt N : ℝ) + 1) * (2 * (discSqrt N : ℝ) + 1)
        ≤ 6 * ((discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ)) := by
      have h1' : 0 ≤ Real.sqrt (discSqrt N : ℝ) + 1 := by linarith
      have h2' : 0 ≤ 2 * (discSqrt N : ℝ) + 1 := by linarith
      nlinarith [h1, h2, hR0, hs0, mul_nonneg hR0 hs0]
    nlinarith [h3, hd0, hq0, hs0, mul_nonneg hR0 hs0]
  calc (∑ r ∈ F, ‖KInnerStar (discFib N r) w k chi r‖)
      ≤ ((F.card : ℝ)) * (2 * (discSqrt N : ℝ) + 1) := hsum
    _ ≤ (24 * (d:ℝ) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) * (Real.sqrt (discSqrt N : ℝ) + 1))
          * (2 * (discSqrt N : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right hcard'
        linarith
    _ ≤ 144 * (d:ℝ) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ)
          * ((discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ)) := hkey

theorem odd_sqrt_sum_disc :
    ∀ R : ℤ, 1 ≤ R →
      (∑ r ∈ (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r),
        (Real.sqrt |(r : ℝ)| + 2 * (R : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹))
        ≤ 128 * ((R : ℝ) * Real.sqrt (R : ℝ)) := by
  intro R hR
  have hR0 : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast (by linarith : (0:ℤ) ≤ R)
  have hR1r : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hsq : Real.sqrt (R:ℝ) ^ 2 = (R:ℝ) := Real.sq_sqrt hR0
  have hsq0 : (0:ℝ) ≤ Real.sqrt (R:ℝ) := Real.sqrt_nonneg _
  have hmax : max R 0 = R := max_eq_left (by linarith)
  have hRt : (((R.toNat : ℕ)) : ℝ) = (R:ℝ) := by
    rw [← hmax]
    exact_mod_cast (Int.toNat_of_nonneg (le_max_right R 0))
  have hfe : (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r)
      = (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r ∧ r ≠ 0) := by
    apply Finset.filter_congr
    intro r _
    exact ⟨fun h => ⟨h, by rintro rfl; exact Int.not_odd_zero h⟩, fun h => h.1⟩
  have h1 := sum_sqrt_Icc_le R
  have h2 := sum_inv_sqrt_Icc_le R
  rw [hmax, hRt] at h1 h2
  have hsum1 : (∑ r ∈ (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r), Real.sqrt |(r:ℝ)|)
      ≤ 4 * Real.sqrt (R:ℝ)^3 + 8 := by
    rw [hfe]; exact h1
  have hsum2 : (∑ r ∈ (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r), (Real.sqrt |(r:ℝ)|)⁻¹)
      ≤ 4 * Real.sqrt (R:ℝ) + 8 := by
    rw [hfe]; exact h2
  have hgoal : (∑ r ∈ (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r),
        (Real.sqrt |(r : ℝ)| + 2 * (R : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹))
      = (∑ r ∈ (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r), Real.sqrt |(r:ℝ)|)
        + 2 * (R:ℝ) * (∑ r ∈ (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r),
            (Real.sqrt |(r:ℝ)|)⁻¹) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hgoal]
  have h2R0 : (0:ℝ) ≤ 2 * (R:ℝ) := by linarith
  have hsum2' : 2 * (R:ℝ) * (∑ r ∈ (Finset.Icc (-R) R).filter (fun r : ℤ => Odd r), (Real.sqrt |(r:ℝ)|)⁻¹)
      ≤ 2 * (R:ℝ) * (4 * Real.sqrt (R:ℝ) + 8) :=
    mul_le_mul_of_nonneg_left hsum2 h2R0
  have hpow : Real.sqrt (R:ℝ)^3 = (R:ℝ) * Real.sqrt (R:ℝ) := by
    calc Real.sqrt (R:ℝ)^3 = Real.sqrt (R:ℝ)^2 * Real.sqrt (R:ℝ) := by ring
      _ = (R:ℝ) * Real.sqrt (R:ℝ) := by rw [hsq]
  have hcomb : (4 * Real.sqrt (R:ℝ)^3 + 8) + 2 * (R:ℝ) * (4 * Real.sqrt (R:ℝ) + 8)
      ≤ 128 * ((R:ℝ) * Real.sqrt (R:ℝ)) := by
    rw [hpow]
    have hRS0 : 0 ≤ (R:ℝ) * Real.sqrt (R:ℝ) := mul_nonneg hR0 hsq0
    have hRS1 : 1 ≤ (R:ℝ) * Real.sqrt (R:ℝ) := by
      have h := mul_le_mul hR1r (Real.one_le_sqrt.mpr hR1r) (by norm_num : (0:ℝ) ≤ 1) hR0
      simpa using h
    have hRSR : (R:ℝ) ≤ (R:ℝ) * Real.sqrt (R:ℝ) := by
      have h := mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hR1r) hR0
      simpa using h
    nlinarith [hRS0, hRS1, hRSR]
  linarith [hsum1, hsum2', hcomb]

/-- pure arithmetic folding of the good/bad bounds into the target shape -/
lemma fold_arith_disc (Cg Cb : ℝ) (hCg : 0 ≤ Cg) (hCb : 0 ≤ Cb)
    (d : ℕ) (k : ℤ) (q N : ℕ) (tau : ℝ)
    (hq : 1 ≤ q) (hN : 1 ≤ N) (htau : 1 ≤ tau) :
    128 * Cg * (d:ℝ) * (|(k:ℝ)|+1) * Real.sqrt ((q:ℝ)) * tau
        * ((discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ))
        * Real.log (2 + Real.sqrt ((q:ℝ)) * (N:ℝ))
      + Cb * (d:ℝ) * Real.sqrt ((q:ℝ)) * ((discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ))
    ≤ 1000 * (Cg + Cb + 1) * (d:ℝ) * (|(k:ℝ)|+1) * Real.sqrt ((q:ℝ)) * tau
        * (N:ℝ)^((3:ℝ)/4) * Real.log (2 + Real.sqrt ((q:ℝ)) * (N:ℝ)) := by
  set SQ : ℝ := Real.sqrt ((q:ℝ)) with hSQdef
  set DD : ℝ := (d:ℝ) with hDDdef
  set KK : ℝ := (|(k:ℝ)|+1) with hKKdef
  set TT : ℝ := (N:ℝ)^((3:ℝ)/4) with hTTdef
  set RR : ℝ := (discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ) with hRRdef
  set LL : ℝ := Real.log (2 + SQ * (N:ℝ)) with hLLdef
  have hSQ0 : 0 ≤ SQ := by rw [hSQdef]; exact Real.sqrt_nonneg _
  have hDD0 : 0 ≤ DD := by rw [hDDdef]; exact Nat.cast_nonneg _
  have hKK1 : 1 ≤ KK := by rw [hKKdef]; linarith [abs_nonneg (k:ℝ)]
  have hTT0 : 0 ≤ TT := by rw [hTTdef]; exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hRR0 : 0 ≤ RR := by
    rw [hRRdef]
    have h1 : (0:ℝ) ≤ (discSqrt N : ℝ) := by exact_mod_cast discSqrt_nonneg N
    positivity
  have hRRTT : RR ≤ TT := by
    rw [hRRdef, hTTdef]
    exact discSqrt_mul_sqrt_le N hN
  have hLL0 : 0 ≤ LL := by
    rw [hLLdef]
    apply Real.log_nonneg
    have h1 : 0 ≤ SQ * (N:ℝ) := mul_nonneg hSQ0 (Nat.cast_nonneg N)
    linarith
  have hLL2 : Real.log 2 ≤ LL := by
    rw [hLLdef]
    apply Real.log_le_log (by norm_num)
    have h1 : 0 ≤ SQ * (N:ℝ) := mul_nonneg hSQ0 (Nat.cast_nonneg N)
    linarith
  have htau0 : 0 ≤ tau := by linarith
  have hcG : 0 ≤ 128 * Cg * DD * KK * SQ * tau * LL := by positivity
  have hcB : 0 ≤ Cb * DD * SQ := by positivity
  have hG : 128 * Cg * DD * KK * SQ * tau * RR * LL ≤ 128 * Cg * DD * KK * SQ * tau * TT * LL := by
    have he1 : 128 * Cg * DD * KK * SQ * tau * RR * LL
        = (128 * Cg * DD * KK * SQ * tau * LL) * RR := by ring
    have he2 : 128 * Cg * DD * KK * SQ * tau * TT * LL
        = (128 * Cg * DD * KK * SQ * tau * LL) * TT := by ring
    rw [he1, he2]
    exact mul_le_mul_of_nonneg_left hRRTT hcG
  have hB1 : Cb * DD * SQ * RR ≤ Cb * DD * SQ * TT := by
    have he1 : Cb * DD * SQ * RR = (Cb * DD * SQ) * RR := by ring
    have he2 : Cb * DD * SQ * TT = (Cb * DD * SQ) * TT := by ring
    rw [he1, he2]
    exact mul_le_mul_of_nonneg_left hRRTT hcB
  have hB2 : Cb * DD * SQ * TT ≤ 2 * Cb * DD * KK * SQ * tau * TT * LL := by
    have hKL : (1:ℝ)/2 ≤ KK * tau * LL := by
      have h1 : (1:ℝ) ≤ KK * tau := one_le_mul_of_one_le_of_one_le hKK1 htau
      have h2 : (1:ℝ)/2 ≤ LL := by linarith [Real.log_two_gt_d9, hLL2]
      have h3 : LL ≤ (KK * tau) * LL := by
        calc LL = (1:ℝ) * LL := by ring
          _ ≤ (KK * tau) * LL := mul_le_mul_of_nonneg_right h1 hLL0
      linarith
    have hkey : Cb ≤ (2 * Cb) * (KK * tau * LL) := by
      have h2 : (1:ℝ) ≤ 2 * (KK * tau * LL) := by linarith
      calc Cb = Cb * 1 := by ring
        _ ≤ Cb * (2 * (KK * tau * LL)) := mul_le_mul_of_nonneg_left h2 hCb
        _ = (2 * Cb) * (KK * tau * LL) := by ring
    have hDDST0 : 0 ≤ DD * SQ * TT := mul_nonneg (mul_nonneg hDD0 hSQ0) hTT0
    have hm := mul_le_mul_of_nonneg_right hkey hDDST0
    have he1 : Cb * DD * SQ * TT = Cb * (DD * SQ * TT) := by ring
    have he2 : (2 * Cb * (KK * tau * LL)) * (DD * SQ * TT)
        = 2 * Cb * DD * KK * SQ * tau * TT * LL := by ring
    rw [← he1, he2] at hm
    exact hm
  have hsum : 128 * Cg * DD * KK * SQ * tau * RR * LL + Cb * DD * SQ * RR
      ≤ (128 * Cg + 2 * Cb) * (DD * KK * SQ * tau * TT * LL) := by
    have h1 := add_le_add hG (hB1.trans hB2)
    have he : 128 * Cg * DD * KK * SQ * tau * TT * LL
        + 2 * Cb * DD * KK * SQ * tau * TT * LL
        = (128 * Cg + 2 * Cb) * (DD * KK * SQ * tau * TT * LL) := by ring
    rwa [he] at h1
  have hconst : 128 * Cg + 2 * Cb ≤ 1000 * (Cg + Cb + 1) := by linarith
  have hW0 : 0 ≤ DD * KK * SQ * tau * TT * LL := by positivity
  calc 128 * Cg * DD * KK * SQ * tau * RR * LL + Cb * DD * SQ * RR
      ≤ (128 * Cg + 2 * Cb) * (DD * KK * SQ * tau * TT * LL) := hsum
    _ ≤ (1000 * (Cg + Cb + 1)) * (DD * KK * SQ * tau * TT * LL) :=
        mul_le_mul_of_nonneg_right hconst hW0
    _ = 1000 * (Cg + Cb + 1) * DD * KK * SQ * tau * TT * LL := by ring

theorem KStarDisc_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (w : GaussianInt) (k : ℤ)
      (chi : GaussianInt → ℂ) (N : ℕ),
      Work.FIPlan.IsPrimary w → IsCoprime w.re w.im → 1 ≤ N →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∀ (a b : ℤ), chi ⟨a + 4 * (d : ℤ), b⟩ = chi ⟨a, b⟩) →
      (∀ (a b : ℤ), chi ⟨a, b + 4 * (d : ℤ)⟩ = chi ⟨a, b⟩) →
      ‖Work.FIArea7.KStarDisc N w k chi‖
        ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * ‖w.toComplex‖
            * (((Work.FIPlan.gnorm w).divisors).card : ℝ)
            * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log (2 + ‖w.toComplex‖ * (N : ℝ)) := by
  obtain ⟨Cg, hCgpos, hGood⟩ := good_pointwise_disc
  obtain ⟨Cb, hCbpos, hBad⟩ := bad_sum_bound_disc
  refine ⟨1000 * (Cg + Cb + 1), by positivity, ?_⟩
  intro d hd w k chi N hw hcop hN hchi hper1 hper2
  set q : ℕ := Work.FIPlan.gnorm w with hqdef
  set hv : ℝ := Real.sqrt (((q : ℕ)) : ℝ) with hvdef
  set tau : ℝ := ((q.divisors).card : ℝ) with htaudef
  set RR : ℝ := (discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ) with hRRdef
  set L : ℝ := Real.log (2 + hv * (N : ℝ)) with hLdef
  set Fg : Finset ℤ := (Finset.Icc (-(discSqrt N)) (discSqrt N)).filter (fun r : ℤ => Odd r ∧ goodR d q r) with hFgdef
  set Fb : Finset ℤ := (Finset.Icc (-(discSqrt N)) (discSqrt N)).filter (fun r : ℤ => Odd r ∧ ¬ goodR d q r) with hFbdef
  set Fo : Finset ℤ := (Finset.Icc (-(discSqrt N)) (discSqrt N)).filter (fun r : ℤ => Odd r) with hFodef
  let f : ℤ → ℝ := fun r => ‖KInnerStar (discFib N r) w k chi r‖
  have hw0 : w ≠ 0 := by rintro rfl; exact Int.not_odd_zero (by simpa using hw.1)
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hw0 (gnorm_eq_zero_iff.mp h))
  have hR1 : 1 ≤ discSqrt N := one_le_discSqrt hN
  have hv0 : 0 ≤ hv := by rw [hvdef]; exact Real.sqrt_nonneg _
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have htau1 : 1 ≤ tau := by
    rw [htaudef]
    have hmem : 1 ∈ q.divisors := by
      rw [Nat.mem_divisors]
      exact ⟨one_dvd _, fun h => (Nat.one_le_iff_ne_zero.mp hq1) h⟩
    exact_mod_cast Finset.one_le_card.mpr ⟨1, hmem⟩
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    have h1 : 0 ≤ hv * (N:ℝ) := mul_nonneg hv0 hN0
    linarith
  have hnorm : ‖w.toComplex‖ = hv := by
    rw [hvdef]
    exact norm_toComplex_eq_sqrt w
  have hA1 : ‖KStarDisc N w k chi‖ ≤ ∑ r ∈ Finset.Icc (-(discSqrt N)) (discSqrt N), f r := by
    rw [KStarDisc_eq_sum]
    exact norm_sum_le _ _
  have hA2 : (∑ r ∈ Finset.Icc (-(discSqrt N)) (discSqrt N), f r) = ∑ r ∈ Fo, f r := by
    rw [hFodef, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : Odd r
    · rw [if_pos h]
    · rw [if_neg h]
      show ‖KInnerStar (discFib N r) w k chi r‖ = 0
      rw [KInnerStar_eq_zero_of_not_odd h, norm_zero]
  have hA3 : (∑ r ∈ Fo, f r) = (∑ r ∈ Fg, f r) + (∑ r ∈ Fb, f r) := by
    have h1 := Finset.sum_filter_add_sum_filter_not Fo (fun r : ℤ => goodR d q r) f
    rw [hFodef, Finset.filter_filter, Finset.filter_filter] at h1
    rw [← hFgdef, ← hFbdef] at h1
    exact h1.symm
  have hS : ‖KStarDisc N w k chi‖ ≤ (∑ r ∈ Fg, f r) + (∑ r ∈ Fb, f r) :=
    hA1.trans (le_of_eq (hA2.trans hA3))
  have hgood_sum : (∑ r ∈ Fg, f r) ≤ 128 * Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * RR * L := by
    have hbr_nn : ∀ r : ℤ, (0:ℝ) ≤ Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹ := by
      intro r
      have h1 : (0:ℝ) ≤ Real.sqrt |(r:ℝ)| := Real.sqrt_nonneg _
      have h2 : (0:ℝ) ≤ (discSqrt N : ℝ) := by exact_mod_cast discSqrt_nonneg N
      have h3 : (0:ℝ) ≤ (Real.sqrt |(r:ℝ)|)⁻¹ := inv_nonneg.mpr h1
      nlinarith [h1, h2, h3]
    have hpt : ∀ r ∈ Fg, f r ≤ Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau
        * (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹) * L := by
      intro r hr
      rw [hFgdef, Finset.mem_filter] at hr
      obtain ⟨hrIcc, hrOdd, hrGood⟩ := hr
      exact hGood d hd w k chi N hw hcop hN hchi hper2 r hrIcc hrOdd hrGood
    have hC1 : (0:ℝ) ≤ Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * L := by positivity
    have hsum1 : (∑ r ∈ Fg, f r) ≤ ∑ r ∈ Fg, (Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau
        * (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹) * L) :=
      Finset.sum_le_sum hpt
    have hsum2 : (∑ r ∈ Fg, (Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau
        * (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹) * L))
        = Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * L
          * (∑ r ∈ Fg, (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    have hsub : Fg ⊆ Fo := by
      intro r hr
      rw [hFgdef] at hr
      rw [hFodef]
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, hr.2.1⟩
    have hsub2 : (∑ r ∈ Fg, (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹))
        ≤ (∑ r ∈ Fo, (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hbr_nn r)
    have hodd : (∑ r ∈ Fo, (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹)) ≤ 128 * RR := by
      rw [hFodef, hRRdef]
      exact odd_sqrt_sum_disc (discSqrt N) hR1
    calc (∑ r ∈ Fg, f r)
        ≤ ∑ r ∈ Fg, (Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau
            * (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹) * L) := hsum1
      _ = Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * L
            * (∑ r ∈ Fg, (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹)) := hsum2
      _ ≤ Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * L
            * (∑ r ∈ Fo, (Real.sqrt |(r:ℝ)| + 2 * (discSqrt N : ℝ) * (Real.sqrt |(r:ℝ)|)⁻¹)) :=
          mul_le_mul_of_nonneg_left hsub2 hC1
      _ ≤ Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * L * (128 * RR) :=
          mul_le_mul_of_nonneg_left hodd hC1
      _ = 128 * Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * RR * L := by ring
  have hbad_sum : (∑ r ∈ Fb, f r) ≤ Cb * (d:ℝ) * hv * RR := by
    have h := hBad d hd w k chi N hw hcop hN hchi
    rw [hFbdef, hRRdef]
    exact h
  have hfinal : ‖KStarDisc N w k chi‖
      ≤ 128 * Cg * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * RR * L + Cb * (d:ℝ) * hv * RR :=
    hS.trans (add_le_add hgood_sum hbad_sum)
  have hfold := fold_arith_disc Cg Cb hCgpos.le hCbpos.le d k q N tau hq1 hN htau1
  have hmain : ‖KStarDisc N w k chi‖
      ≤ 1000 * (Cg + Cb + 1) * (d:ℝ) * (|(k:ℝ)|+1) * hv * tau * (N:ℝ)^((3:ℝ)/4) * L := by
    refine hfinal.trans ?_
    exact hfold
  rw [hnorm]
  exact hmain


end

end Work.FIArea7
