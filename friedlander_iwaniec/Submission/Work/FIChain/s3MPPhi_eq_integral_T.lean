import Mathlib
import Submission.Work.FIChain.s3MainLevelAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Pointwise identification of the level integrand with the `(b,e,u)`-integrand.**
For *every* real `u`, the `n`-indicator of the `(1.7)`-level block equals the product of the four
individual indicators, and the `d`-sum factors out, giving the integrand of `s3MPT`. -/
lemma mp_phi_pointwise (n x b e : ℕ) (u z sz : ℝ) (Cm : ℕ) (hz0 : 0 ≤ z) (hsz0 : 0 ≤ sz)
    (hn : n ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
        ((ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b * e) * d)) *
        (if n ∈ Finset.Icc (⌊max (((b * e : ℕ) : ℝ) * z) (((b * e : ℕ) : ℝ) * (Cm : ℝ) * u)⌋₊ + 1)
            (⌊min (((b * e : ℕ) : ℝ) * sz) ((x : ℝ))⌋₊) then (1 : ℝ) else 0)) / u
      = (if (((b * e : ℕ) : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then
          (if (((b * e : ℕ) : ℝ) * z < (n : ℝ)) then (1 : ℝ) else 0)
            * (if ((n : ℝ) ≤ ((b * e : ℕ) : ℝ) * sz) then (1 : ℝ) else 0)
            * ((1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
                (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b * e) * d)))
          else 0) := by
  rw [ite_mem_Icc_eq_prod n (b * e) x u z sz Cm hz0 hsz0, if_pos hn]
  by_cases h : ((b * e : ℕ) : ℝ) * (Cm : ℝ) * u < (n : ℝ)
  · rw [if_pos h, if_pos h, ← Finset.sum_mul]
    ring
  · rw [if_neg h, if_neg h, Finset.sum_eq_zero (fun d _ => by ring)]
    simp

/-- The level summand `s3MPPhi` equals the integral of `s3MPT` over `[1, sz/Cm]`. -/
lemma s3MPPhi_eq_integral_T (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (n b e : ℕ)
    (hx : 1 ≤ x) (hCm : 1 ≤ Cm) (hb : 1 ≤ b) (he : 1 ≤ e) (hz : 1 ≤ z)
    (hCmsz : (Cm : ℝ) ≤ sz) (hn : n ≤ x) :
    Work.FIChain.s3MPPhi lam x z sz Cm n b e
      = ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), Work.FIChain.s3MPT lam x z sz Cm n b e u := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast hCm
  have hz0 : 0 ≤ z := by linarith
  have hsz0 : 0 ≤ sz := by
    have h1 : (1 : ℝ) ≤ sz := le_trans (by exact_mod_cast hCm) hCmsz
    linarith
  have hB1 : (1 : ℝ) ≤ sz / (Cm : ℝ) := by rw [le_div_iff₀ hCmpos]; simpa using hCmsz
  have hLpos : 0 < ((b * e : ℕ) : ℝ) := by
    have hbe1 : (1 : ℕ) ≤ b * e := by simpa using Nat.mul_le_mul hb he
    have h2 : (1 : ℝ) ≤ ((b * e : ℕ) : ℝ) := by exact_mod_cast hbe1
    linarith
  have hcpos : 0 < ((b * e : ℕ) : ℝ) * (Cm : ℝ) := mul_pos hLpos hCmpos
  have hcast : ((b * e : ℕ) : ℝ) = (b : ℝ) * (e : ℝ) := by push_cast; ring
  by_cases hP : (b : ℝ) * (e : ℝ) * z ≤ (x : ℝ)
  ·
    have hP' : ((b * e : ℕ) : ℝ) * z ≤ (x : ℝ) := by rw [hcast]; exact hP
    have hLHS : s3MPPhi lam x z sz Cm n b e
        = Submission.ASP.rhoOf lam (b * e) *
          ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ))
              ((x : ℝ) / (((b * e : ℕ) : ℝ) * (Cm : ℝ)))),
            (if (((b * e : ℕ) : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then
              (if (((b * e : ℕ) : ℝ) * z < (n : ℝ)) then (1 : ℝ) else 0)
                * (if ((n : ℝ) ≤ ((b * e : ℕ) : ℝ) * sz) then (1 : ℝ) else 0)
                * ((1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
                    (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b * e) * d)))
              else 0) := by
      rw [s3MPPhi, if_pos hP]
      congr 1
      exact intervalIntegral.integral_congr
        (fun u _ => mp_phi_pointwise n x b e u z sz Cm hz0 hsz0 hn)
    have hRHS : (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), s3MPT lam x z sz Cm n b e u)
        = Submission.ASP.rhoOf lam (b * e) *
          ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
            (if (((b * e : ℕ) : ℝ) * (Cm : ℝ) * u < (n : ℝ)) then
              (if (((b * e : ℕ) : ℝ) * z < (n : ℝ)) then (1 : ℝ) else 0)
                * (if ((n : ℝ) ≤ ((b * e : ℕ) : ℝ) * sz) then (1 : ℝ) else 0)
                * ((1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
                    (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b * e) * d)))
              else 0) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      simp only [s3MPT]
      rw [← hcast, if_pos hP', if_pos hn]
      split_ifs <;> ring
    rw [hLHS, hRHS]
    congr 1
    exact integral_range_lt_mul
      (fun u => (if (((b * e : ℕ) : ℝ) * z < (n : ℝ)) then (1 : ℝ) else 0)
        * (if ((n : ℝ) ≤ ((b * e : ℕ) : ℝ) * sz) then (1 : ℝ) else 0)
        * ((1 / u) * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
            (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b * e) * d))))
      hcpos hB1 rfl (by exact_mod_cast hn)
  · simp only [s3MPPhi, s3MPT, if_neg hP]
    simp

end

end Work.FIChain
