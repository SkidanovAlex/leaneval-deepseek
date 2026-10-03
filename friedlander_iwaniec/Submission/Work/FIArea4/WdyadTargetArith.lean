import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.Wdyad_units
import Submission.Work.FIArea4.WdyadStratTau
import Submission.Work.FIArea4.WdyadGen.braceV_toolbox
import Submission.Work.FIArea4.box_lemmas
import Submission.Work.FIArea4.Wdyad_le_trivial

/-!
# Arithmetic of the two brackets

Compares the bracket of Friedlander–Iwaniec (11.23) (`B1123`) and the bracket `braceV` of (11.19)
with the *target* bracket `braceV + D·min R S·(RS)^ε` produced by the strata/divisor-count bound.

* **Route B** (`B1123_le_target`): when `S` dominates `D^{3/2}(DR)^ε` (and `D ≤ S`), every term of
  `B1123` is dominated by a term of the target bracket.
* **Route S** (`tau_mul_braceV_le`): when `S ≤ 16 D^2(RS)^{2ε}`, the divisor-count loss
  `C_τ(2(RS))^{ε/2}` applied to `braceV(·,ε/2)` is absorbed by the target bracket.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `1 ≤ (RS)^ε` for `R,S ≥ 1`, `ε ≥ 0`. -/
lemma one_le_RS_rpow {R S : ℕ} (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hε : 0 ≤ ε) :
    (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := by
  have h1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have h2 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  exact Real.one_le_rpow (by nlinarith) hε

/-- `(RS)^{ε/2} ≤ (RS)^ε` for `R,S ≥ 1`. -/
lemma RS_rpow_half_le {R S : ℕ} (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hε : 0 ≤ ε) :
    ((R : ℝ) * (S : ℝ)) ^ (ε / 2) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := by
  have h1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have h2 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith)

/-- `min (R:ℝ) (S:ℝ) = S` when `S ≤ R`. -/
lemma cast_min_eq_right {R S : ℕ} (h : S ≤ R) : min (R : ℝ) (S : ℝ) = (S : ℝ) :=
  min_eq_right (by exact_mod_cast h)

/-- **Route B arithmetic.** -/
lemma B1123_le_target (ε : ℝ) (hε : 0 < ε) {D R S : ℕ} (hD : 1 ≤ D) (hDS : D ≤ S)
    (hSR : S ≤ R) (hk : (D : ℝ) ^ ((3 : ℝ) / 2) * (((D : ℝ) * (R : ℝ)) ^ ε) ≤ 16 * (S : ℝ)) :
    B1123 D R S ε ≤ 20 * (braceV D R S ε
      + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)) := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast (le_trans hD hDS)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    have hDR : D ≤ R := le_trans hDS hSR
    exact_mod_cast (le_trans hD hDR)
  have hDS1 : (D : ℝ) ≤ (S : ℝ) := by exact_mod_cast hDS
  have hmin : (min R S : ℝ) = (S : ℝ) := cast_min_eq_right hSR
  have hQ0 : (0 : ℝ) < (R : ℝ) * (S : ℝ) := by positivity
  have hQe0 : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.rpow_nonneg hQ0.le _
  have hQe1 : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε :=
    one_le_RS_rpow ε (le_trans hD (le_trans hDS hSR)) (le_trans hD hDS) hε.le
  have hDR0 : (0 : ℝ) < (D : ℝ) * (R : ℝ) := by positivity
  have hDRS : (D : ℝ) * (R : ℝ) ≤ (R : ℝ) * (S : ℝ) := by nlinarith [hDS1, hR1]
  have hθ : ((D : ℝ) * (R : ℝ)) ^ ε ≤ ((R : ℝ) * (S : ℝ)) ^ ε :=
    Real.rpow_le_rpow hDR0.le hDRS hε.le
  have hA : (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((D : ℝ) * (R : ℝ)) ^ ε)
      ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) :=
    mul_le_mul_of_nonneg_left hθ (by positivity)
  have hB : (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((D : ℝ) * (R : ℝ)) ^ ε)
      ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε) :=
    mul_le_mul_of_nonneg_left hθ (by positivity)
  have hDpow : (D : ℝ) ^ ((3 : ℝ) / 2) * (D : ℝ) ^ (-(1 : ℝ) / 2) = (D : ℝ) := by
    rw [← Real.rpow_add (by positivity), show (3 : ℝ) / 2 + (-(1 : ℝ) / 2) = 1 by norm_num,
      Real.rpow_one]
  have hC : (D : ℝ) * (R : ℝ) * (((D : ℝ) * (R : ℝ)) ^ ε)
      ≤ 16 * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)) := by
    have hstep : (D : ℝ) * (R : ℝ) * (((D : ℝ) * (R : ℝ)) ^ ε)
        = (D : ℝ) ^ (-(1 : ℝ) / 2)
            * ((D : ℝ) ^ ((3 : ℝ) / 2) * (((D : ℝ) * (R : ℝ)) ^ ε)) * (R : ℝ) := by
      have he : (D : ℝ) ^ (-(1 : ℝ) / 2)
            * ((D : ℝ) ^ ((3 : ℝ) / 2) * (((D : ℝ) * (R : ℝ)) ^ ε)) * (R : ℝ)
          = ((D : ℝ) ^ ((3 : ℝ) / 2) * (D : ℝ) ^ (-(1 : ℝ) / 2))
              * ((((D : ℝ) * (R : ℝ)) ^ ε) * (R : ℝ)) := by ring
      rw [he, hDpow]; ring
    rw [hstep]
    calc (D : ℝ) ^ (-(1 : ℝ) / 2) * ((D : ℝ) ^ ((3 : ℝ) / 2) * (((D : ℝ) * (R : ℝ)) ^ ε))
            * (R : ℝ)
        ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (16 * (S : ℝ)) * (R : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 16 * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)) := by ring
  have hL : B1123 D R S ε
      = (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((D : ℝ) * (R : ℝ)) ^ ε)
        + (D : ℝ) * (R : ℝ) * (((D : ℝ) * (R : ℝ)) ^ ε)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((D : ℝ) * (R : ℝ)) ^ ε) := by
    unfold B1123; ring_nf
  have hRt : braceV D R S ε + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)
      = (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε)
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)
        + (D : ℝ) * (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    unfold braceV; rw [hmin]; ring_nf
  rw [hL, hRt]
  have n1 : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
  have n2 : (0 : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε) :=
    by positivity
  have n3 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    positivity
  have n4 : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    positivity
  have n5 : (0 : ℝ) ≤ (D : ℝ) * (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
  linarith [hA, hB, hC, n1, n2, n3, n4, n5]

/-- **Route S, key estimate.** -/
lemma rpow_half_mul_le (ε : ℝ) (hε : 0 < ε) {D R S : ℕ} (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hsmall : (S : ℝ) ≤ 16 * (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε))) :
    (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
      ≤ 2 * ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by positivity
  have hR0 : (0 : ℝ) < (R : ℝ) := by positivity
  have hS0 : (0 : ℝ) < (S : ℝ) := by positivity
  have hQ0 : (0 : ℝ) < (R : ℝ) * (S : ℝ) := by positivity
  have hQh0 : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ (ε / 2) := Real.rpow_nonneg hQ0.le _
  have hkey : (S : ℝ) ^ ((1 : ℝ) / 4)
      ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) := by
    have h1 : (S : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (16 * (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε))) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hS0.le hsmall (by norm_num)
    have h2 : (16 * (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε))) ^ ((1 : ℝ) / 4)
        = 2 * (D : ℝ) ^ ((1 : ℝ) / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (by positivity)]
      have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
          ← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hDq : ((D : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) = (D : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast (D : ℝ) 2, ← Real.rpow_mul hD0.le]
        norm_num
      have hQq : (((R : ℝ) * (S : ℝ)) ^ (2 * ε)) ^ ((1 : ℝ) / 4)
          = ((R : ℝ) * (S : ℝ)) ^ (ε / 2) := by
        rw [← Real.rpow_mul hQ0.le]
        ring_nf
      rw [h16, hDq, hQq]
    linarith [h1, h2.le, h2.ge]
  have hSpow : (S : ℝ) ^ ((1 : ℝ) / 4) * (S : ℝ) ^ ((3 : ℝ) / 4) = (S : ℝ) := by
    rw [← Real.rpow_add hS0]
    norm_num
  have hQh_le : ((R : ℝ) * (S : ℝ)) ^ (ε / 2) ≤ ((R : ℝ) * (S : ℝ)) ^ ε :=
    RS_rpow_half_le ε hR hS hε.le
  have hQhfac : (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))
      = ((R : ℝ) * (S : ℝ)) ^ ε := by
    rw [← Real.rpow_add hQ0, show ε / 2 + ε / 2 = ε by ring]
  have hk2 : (S : ℝ) ^ ((1 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))
      ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 2) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    have h := mul_le_mul_of_nonneg_right hkey hQh0
    calc (S : ℝ) ^ ((1 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))
        ≤ (2 * (D : ℝ) ^ ((1 : ℝ) / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)))
            * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) := h
      _ = 2 * (D : ℝ) ^ ((1 : ℝ) / 2) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
          rw [← hQhfac]; ring
  have hDinv : (D : ℝ) ^ (-(1 : ℝ) / 2) * (D : ℝ) ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hD0, show -(1 : ℝ) / 2 + (1 : ℝ) / 2 = 0 by norm_num, Real.rpow_zero]
  calc (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
      = (((R : ℝ) * (S : ℝ)) ^ (ε / 2))
          * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ)
              * ((S : ℝ) ^ ((1 : ℝ) / 4) * (S : ℝ) ^ ((3 : ℝ) / 4))) := by
        rw [hSpow]
    _ = (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
          * ((S : ℝ) ^ ((1 : ℝ) / 4) * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)) := by ring
    _ ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
          * (2 * (D : ℝ) ^ ((1 : ℝ) / 2) * (((R : ℝ) * (S : ℝ)) ^ ε)) :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
    _ = 2 * ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
        calc (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
              * (2 * (D : ℝ) ^ ((1 : ℝ) / 2) * (((R : ℝ) * (S : ℝ)) ^ ε))
            = 2 * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (D : ℝ) ^ ((1 : ℝ) / 2))
                * ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)) := by
              ring
          _ = 2 * ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)) := by
              rw [hDinv]; ring
          _ = 2 * ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
              ring

/-- **Route S arithmetic.** -/
lemma tau_mul_braceV_le (ε : ℝ) (hε : 0 < ε) (Cτ : ℝ) (hCτ : 0 < Cτ) {D R S : ℕ}
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hsmall : (S : ℝ) ≤ 16 * (D : ℝ) ^ 2 * (((R : ℝ) * (S : ℝ)) ^ (2 * ε))) :
    (Cτ * (2 : ℝ) ^ (ε / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))) * braceV D R S (ε / 2)
      ≤ 3 * Cτ * (2 : ℝ) ^ (ε / 2) * (braceV D R S ε
          + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)) := by
  have hQ0 : (0 : ℝ) < (R : ℝ) * (S : ℝ) := by positivity
  have hQh0 : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ (ε / 2) := Real.rpow_nonneg hQ0.le _
  have hQe0 : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.rpow_nonneg hQ0.le _
  have hQhfac : (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))
      = ((R : ℝ) * (S : ℝ)) ^ ε := by
    rw [← Real.rpow_add hQ0, show ε / 2 + ε / 2 = ε by ring]
  have hBs : braceV D R S (ε / 2)
      = (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) := by
    unfold braceV; ring_nf
  have hBe : braceV D R S ε
      = (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε)
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    unfold braceV; ring_nf
  have hkey := rpow_half_mul_le ε hε hD hR hS hsmall
  have hLe : (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * braceV D R S (ε / 2)
      ≤ 2 * ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε))
        + braceV D R S ε := by
    have h1 : (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * braceV D R S (ε / 2)
        = (((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
          + ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
              + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
            * ((((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))) := by
      rw [hBs]; ring
    rw [h1, hQhfac, hBe]
    have hw : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
    have hA : (0 : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) := by positivity
    have hB : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have hC : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    nlinarith [hkey, hw, hA, hB, hC, mul_nonneg hA hQe0, mul_nonneg hB hQe0, mul_nonneg hC hQe0]
  have hterm : (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)
      ≤ braceV D R S ε := by
    rw [hBe]
    have h1 : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
        * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
    have h3 : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)
        * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
    linarith [h1, h2, h3]
  have hCτ2 : (0 : ℝ) < Cτ * (2 : ℝ) ^ (ε / 2) := by
    have h2p : (0 : ℝ) < (2 : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hstep : (Cτ * (2 : ℝ) ^ (ε / 2) * (((R : ℝ) * (S : ℝ)) ^ (ε / 2))) * braceV D R S (ε / 2)
      = Cτ * (2 : ℝ) ^ (ε / 2) * ((((R : ℝ) * (S : ℝ)) ^ (ε / 2)) * braceV D R S (ε / 2)) := by
    ring
  rw [hstep]
  have h2 := mul_le_mul_of_nonneg_left hLe hCτ2.le
  have h3 := mul_le_mul_of_nonneg_left hterm hCτ2.le
  have hmnn : (0 : ℝ) ≤ (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
  nlinarith [h2, h3, hmnn, hCτ2.le]


/-- The `R ≤ S` case of the target, for *arbitrary* coefficients: FI (11.23) (`Wdyad_le_1123`)
disposes of the range `D ≤ S`, and the trivial bound of the range `D > S`.  (A self-contained copy
of `Wdyad_le_of_R_le_S`, so that this development does not depend on the `R > S` reduction.) -/
lemma Wdyad_le_of_RleS (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → R ≤ S →
      Wdyad D R S γ ≤ C * braceV D R S ε *
        (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  obtain ⟨C₁, hC₁pos, hC₁'⟩ := Wdyad_le_1123 ε hε
  obtain ⟨C₂, hC₂pos, hC₂'⟩ := Wdyad_le_trivial
  have hC₁ : ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      Wdyad D R S γ ≤ C₁ * B1123 D R S ε * WE D γ := by
    intro D R S γ hD hR hS
    simpa only [B1123, WE] using hC₁' D R S γ hD hR hS
  have hC₂ : ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      Wdyad D R S γ ≤ C₂ * Btriv D R S * WE D γ := by
    intro D R S γ hD hR hS
    simpa only [Btriv, WE] using hC₂' D R S γ hD hR hS
  refine ⟨2 * (C₁ + 3 * C₂), by positivity, ?_⟩
  intro D R S γ hD hR hS hRS
  have hEnn : 0 ≤ WE D γ := by
    unfold WE
    exact Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hTnn : 0 ≤ WTb D R S ε := by unfold WTb; positivity
  have hc : (0 : ℝ) ≤ C₁ + 3 * C₂ := by linarith
  have hWv : WTb D R S ε ≤ 2 * braceV D R S ε := WdyadGen.WTb_le_two_braceV D R S ε hR hS
  have hbracket : (C₁ + 3 * C₂) * WTb D R S ε ≤ (C₁ + 3 * C₂) * (2 * braceV D R S ε) :=
    mul_le_mul_of_nonneg_left hWv hc
  have hfin : (C₁ + 3 * C₂) * WTb D R S ε * WE D γ
      ≤ 2 * (C₁ + 3 * C₂) * braceV D R S ε * WE D γ := by
    calc (C₁ + 3 * C₂) * WTb D R S ε * WE D γ
        = ((C₁ + 3 * C₂) * WTb D R S ε) * WE D γ := by ring
      _ ≤ ((C₁ + 3 * C₂) * (2 * braceV D R S ε)) * WE D γ :=
            mul_le_mul_of_nonneg_right hbracket hEnn
      _ = 2 * (C₁ + 3 * C₂) * braceV D R S ε * WE D γ := by ring
  by_cases hDS : D ≤ S
  · have hb := hC₁ D R S γ hD hR hS
    have hbr := bracket_A hε hDS hRS
    have h1 : C₁ * B1123 D R S ε ≤ (C₁ + 3 * C₂) * WTb D R S ε := by
      have h2 : C₁ * B1123 D R S ε ≤ C₁ * WTb D R S ε :=
        mul_le_mul_of_nonneg_left hbr hC₁pos.le
      have h3 : C₁ * WTb D R S ε ≤ (C₁ + 3 * C₂) * WTb D R S ε :=
        mul_le_mul_of_nonneg_right (by linarith) hTnn
      linarith [h2, h3]
    have hW : Wdyad D R S γ ≤ (C₁ + 3 * C₂) * WTb D R S ε * WE D γ := by
      calc Wdyad D R S γ ≤ C₁ * B1123 D R S ε * WE D γ := hb
        _ = (C₁ * B1123 D R S ε) * WE D γ := by ring
        _ ≤ ((C₁ + 3 * C₂) * WTb D R S ε) * WE D γ := mul_le_mul_of_nonneg_right h1 hEnn
        _ = (C₁ + 3 * C₂) * WTb D R S ε * WE D γ := by ring
    exact hW.trans hfin
  · have hSD : S < D := not_le.mp hDS
    have hb := hC₂ D R S γ hD hR hS
    have hbr := bracket_B hε hR hS hRS hSD.le
    have h1 : C₂ * Btriv D R S ≤ (C₁ + 3 * C₂) * WTb D R S ε := by
      have h2 : C₂ * Btriv D R S ≤ C₂ * (3 * WTb D R S ε) :=
        mul_le_mul_of_nonneg_left hbr hC₂pos.le
      have h3 : C₂ * (3 * WTb D R S ε) ≤ (C₁ + 3 * C₂) * WTb D R S ε := by
        have h4 : C₂ * 3 ≤ C₁ + 3 * C₂ := by linarith
        calc C₂ * (3 * WTb D R S ε) = (C₂ * 3) * WTb D R S ε := by ring
          _ ≤ (C₁ + 3 * C₂) * WTb D R S ε := mul_le_mul_of_nonneg_right h4 hTnn
      linarith [h2, h3]
    have hW : Wdyad D R S γ ≤ (C₁ + 3 * C₂) * WTb D R S ε * WE D γ := by
      calc Wdyad D R S γ ≤ C₂ * Btriv D R S * WE D γ := hb
        _ = (C₂ * Btriv D R S) * WE D γ := by ring
        _ ≤ ((C₁ + 3 * C₂) * WTb D R S ε) * WE D γ := mul_le_mul_of_nonneg_right h1 hEnn
        _ = (C₁ + 3 * C₂) * WTb D R S ε * WE D γ := by ring
    exact hW.trans hfin

end

end Work.FIArea4
