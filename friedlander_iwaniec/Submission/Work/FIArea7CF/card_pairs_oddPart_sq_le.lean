/-
# `Submission.Work.FIArea7CF.card_pairs_oddPart_sq_le` — clash-free copy of `Submission.Work.FIArea7.card_pairs_oddPart_sq_le`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.oddPartKernelDefs
import Submission.Work.FIArea7.sq_iff_sqfreeKernel_eq
import Submission.Work.FIArea7.Kern_of_mem_gBox
import Submission.Work.FIArea7.sqfree_kernel_prime_sum
import Submission.Work.FIArea7CF.aCount_bound
import Submission.Work.FIArea7.pairCount_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The cardinality of the box `gBox R` is `((2R+1).toNat)²`. -/
lemma card_gBox_sq (R : ℤ) :
    (Work.FIPlan.gBox R).card = ((2 * R + 1).toNat) ^ 2 := by
  rw [Work.FIPlan.gBox, Finset.card_image_of_injective _ Work.FIPlan.gaussMk_injective,
    Finset.product_eq_sprod, Finset.card_product]
  have hIcc : (Finset.Icc (-R) R).card = (2 * R + 1).toNat := by
    rw [Int.card_Icc]; congr 1; ring
  rw [hIcc]; ring

/-- For `R < 0` the box is empty. -/
lemma gBox_eq_empty_of_neg {R : ℤ} (hR : R < 0) : Work.FIPlan.gBox R = ∅ := by
  have h : Finset.Icc (-R) R = (∅ : Finset ℤ) := by
    rw [Finset.Icc_eq_empty_iff]; omega
  rw [Work.FIPlan.gBox, h]; simp

theorem card_pairs_oddPart_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℤ,
      (((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
          (fun p : GaussianInt × GaussianInt =>
            Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
              = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2))).card : ℝ))
        ≤ C * (((2 * R + 1).toNat : ℝ) ^ 2)
            * (1 + Real.log (2 + ((2 * R + 1).toNat : ℝ))) ^ 5 := by
  obtain ⟨Ca, hCa, hCaB⟩ := aCount_bound
  obtain ⟨CS, hCS, hSB⟩ := sqfree_kernel_prime_sum
  refine ⟨3 + 8 * Ca ^ 2 * CS, by nlinarith [hCa, hCS, sq_nonneg Ca], ?_⟩
  intro R
  by_cases hR : R < 0
  · have hempty : Work.FIPlan.gBox R = ∅ := gBox_eq_empty_of_neg hR
    have hN0 : (2 * R + 1).toNat = 0 := by
      apply Int.toNat_of_nonpos; omega
    rw [hempty]; simp [hN0]
  · push_neg at hR
    set N0 : ℝ := ((2 * R + 1).toNat : ℝ) with hN0def
    set L : ℝ := 1 + Real.log (2 + ((2 * R + 1).toNat : ℝ)) with hLdef
    have hn : (0 : ℝ) ≤ ((2 * R + 1).toNat : ℝ) := Nat.cast_nonneg _
    have h2n : (0 : ℝ) < 2 + ((2 * R + 1).toNat : ℝ) := by linarith
    have hN0ge1 : 1 ≤ N0 := by
      rw [hN0def]; exact_mod_cast (by omega : 1 ≤ (2 * R + 1).toNat)
    have hN0pos : 0 < N0 := lt_of_lt_of_le one_pos hN0ge1
    have hN0nn : 0 ≤ N0 := le_of_lt hN0pos
    have hN0H : N0 = ((2 * R + 1).toNat : ℝ) := hN0def
    have hlog2n : 0 ≤ Real.log (2 + ((2 * R + 1).toNat : ℝ)) := Real.log_nonneg (by linarith)
    have hLge1 : 1 ≤ L := by rw [hLdef]; linarith
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hLge1
    have hLnn : 0 ≤ L := le_of_lt hLpos
    have hcardR : ((Work.FIPlan.gBox R).card : ℝ) = N0 ^ 2 := by
      rw [card_gBox_sq, hN0def]; push_cast; ring
    -- bound the sum of squares of aCount
    have hsum : ∑ d ∈ Sset R, ((aCount R d : ℝ)) ^ 2
        ≤ Ca ^ 2 * N0 ^ 2 * L ^ 2
            * ∑ d ∈ Sset R, ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun d hd => ?_)
      rw [Sset, Finset.mem_filter] at hd
      obtain ⟨_, hdne, _, _⟩ := hd
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hdne)
      have hs : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
      have hp : ((2 : ℝ) ^ (ArithmeticFunction.cardFactors d)) ^ 2
          = (4 : ℝ) ^ (ArithmeticFunction.cardFactors d) := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
          mul_comm (ArithmeticFunction.cardFactors d) 2]
      have hkey : (Ca * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) / Real.sqrt (d : ℝ)
            * N0 * L) ^ 2
          = Ca ^ 2 * N0 ^ 2 * L ^ 2
              * ((4 : ℝ) ^ ArithmeticFunction.cardFactors d / (d : ℝ)) := by
        have hgen : ∀ (x r : ℝ), (Ca * x / r * N0 * L) ^ 2
            = Ca ^ 2 * N0 ^ 2 * L ^ 2 * (x ^ 2 / r ^ 2) := by intro x r; ring
        rw [hgen, hp, hs]
      have hb := hCaB R d hdne
      calc ((aCount R d : ℝ)) ^ 2
          ≤ (Ca * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) / Real.sqrt (d : ℝ)
              * N0 * L) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
        _ = _ := hkey
    have hSbd : ∑ d ∈ Sset R, ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ)
        ≤ CS * (1 + Real.log (2 + N0 ^ 2)) ^ 3 := by
      have h := hSB (((2 * R + 1).toNat) ^ 2)
      have hcast : (((((2 * R + 1).toNat) ^ 2 : ℕ)) : ℝ) = N0 ^ 2 := by
        rw [hN0def]; push_cast; ring
      rw [hcast] at h
      simpa [Sset] using h
    have hLsq : 1 + Real.log (2 + N0 ^ 2) ≤ 2 * L := by
      rw [hLdef]
      have h2 : Real.log (2 + N0 ^ 2) ≤ 2 * Real.log (2 + ((2 * R + 1).toNat : ℝ)) := by
        rw [show (2 : ℝ) * Real.log (2 + ((2 * R + 1).toNat : ℝ))
              = Real.log ((2 + ((2 * R + 1).toNat : ℝ)) ^ 2) from (Real.log_pow _ 2).symm]
        apply Real.log_le_log (by positivity)
        rw [hN0def]; nlinarith [hN0ge1]
      linarith
    have hcube : (1 + Real.log (2 + N0 ^ 2)) ^ 3 ≤ 8 * L ^ 3 := by
      have h0 : 0 ≤ 1 + Real.log (2 + N0 ^ 2) := by
        have : 0 ≤ Real.log (2 + N0 ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg N0])
        linarith
      have h1 : (1 + Real.log (2 + N0 ^ 2)) ^ 3 ≤ (2 * L) ^ 3 :=
        pow_le_pow_left₀ h0 hLsq 3
      rw [mul_pow] at h1; norm_num at h1; linarith
    have hnn : (0 : ℝ) ≤ Ca ^ 2 * N0 ^ 2 * L ^ 2 := by positivity
    have hfinal : ((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
          (fun p : GaussianInt × GaussianInt =>
            Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
              = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2))).card : ℝ)
        ≤ (3 + 8 * Ca ^ 2 * CS) * N0 ^ 2 * L ^ 5 := by
      have hp1 := pairCount_le R
      rw [hcardR] at hp1
      have hstep : 2 * N0 ^ 2 + 1 + Ca ^ 2 * N0 ^ 2 * L ^ 2
            * (CS * (1 + Real.log (2 + N0 ^ 2)) ^ 3)
          ≤ (3 + 8 * Ca ^ 2 * CS) * N0 ^ 2 * L ^ 5 := by
        have e1 : 2 * N0 ^ 2 + 1 ≤ 3 * N0 ^ 2 * L ^ 5 := by
          have hN02 : 1 ≤ N0 ^ 2 := one_le_pow₀ hN0ge1
          have hL5 : 1 ≤ L ^ 5 := one_le_pow₀ hLge1
          have ha : 2 * N0 ^ 2 + 1 ≤ 3 * N0 ^ 2 := by nlinarith [hN02]
          have hb : 3 * N0 ^ 2 ≤ 3 * N0 ^ 2 * L ^ 5 := by nlinarith [hL5, sq_nonneg N0]
          linarith
        have e2 : Ca ^ 2 * N0 ^ 2 * L ^ 2 * (CS * (1 + Real.log (2 + N0 ^ 2)) ^ 3)
            ≤ 8 * Ca ^ 2 * CS * N0 ^ 2 * L ^ 5 := by
          have h4 : Ca ^ 2 * N0 ^ 2 * L ^ 2 * (CS * (1 + Real.log (2 + N0 ^ 2)) ^ 3)
              ≤ Ca ^ 2 * N0 ^ 2 * L ^ 2 * (CS * (8 * L ^ 3)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hcube hCS.le
          have h5 : Ca ^ 2 * N0 ^ 2 * L ^ 2 * (CS * (8 * L ^ 3))
              = 8 * Ca ^ 2 * CS * N0 ^ 2 * L ^ 5 := by ring
          linarith [h4, h5.le]
        linarith [e1, e2]
      have hstep2 : 2 * N0 ^ 2 + 1 + Ca ^ 2 * N0 ^ 2 * L ^ 2
            * ∑ d ∈ Sset R, ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ)
          ≤ 2 * N0 ^ 2 + 1 + Ca ^ 2 * N0 ^ 2 * L ^ 2
            * (CS * (1 + Real.log (2 + N0 ^ 2)) ^ 3) := by
        nlinarith [hSbd, hnn]
      linarith [hp1, hsum, hstep2, hstep]
    calc _ ≤ (3 + 8 * Ca ^ 2 * CS) * N0 ^ 2 * L ^ 5 := hfinal
      _ = (3 + 8 * Ca ^ 2 * CS) * (((2 * R + 1).toNat : ℝ) ^ 2)
            * (1 + Real.log (2 + ((2 * R + 1).toNat : ℝ))) ^ 5 := by
          rw [hN0def, hLdef]

end

end Work.FIArea7
