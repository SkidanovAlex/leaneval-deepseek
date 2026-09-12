import Mathlib
import Submission.QuantileMean
import Submission.QuantileSums
import Submission.SerreExample
import Submission.SerreMean

/-!
# A quantitative closeness bound for averages of pruned quantiles

The roots of the early-ints polynomial are (mostly) the *pruned* quantiles
`alpha (N+2) (k+2)` (`k : Fin N`), i.e. the quantiles of index `2..N+1` out of
`1..N+2`.  This module records:

* a fixed rate constant `qRateC` for `QuantileMean.quantile_mean_rate`;
* membership of the quantiles in `[aSerre,bSerre]`;
* the closeness of the pruned-quantile average to the first moment:
  `|(Σ_{k:Fin N} alpha (N+2) (k+2))/N − ∫x∂muS| ≤ (4·bSerre + qRateC)/N`
  (the two pruned endpoints cost `≤ 4·bSerre/N` plus the `qRateC/N` rate).

Namespace `Submission.QuantileMeanBound`.  Only Quantile/QuantileMean-level
modules (no early-ints dependency).
-/

noncomputable section
open MeasureTheory
open scoped Real BigOperators Topology ENNReal
open Filter

namespace Submission.QuantileMeanBound

open Submission.Quantile
open Submission.QuantileMean
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.SerreMean
open Submission.QuantileSums

/-- The rate constant of `QuantileMean.quantile_mean_rate`. -/
noncomputable def qRateC : ℝ := Classical.choose (quantile_mean_rate)

/-- `qRateC > 0`. -/
lemma qRateC_pos : 0 < qRateC :=
  (Classical.choose_spec quantile_mean_rate).1

/-- Quantitative bound with `qRateC`. -/
lemma qRateC_bound (n : ℕ) (hn : 2 ≤ n) :
    |((∑ i ∈ Finset.Icc 1 n, (alpha n i : ℝ)) / (n : ℝ)) - (∫ x : ℝ, x ∂muS)|
      ≤ qRateC / (n : ℝ) :=
  (Classical.choose_spec quantile_mean_rate).2 n hn

/-- `aSerre ≤ √(aSerre·bSerre) ≤ bSerre`. -/
lemma sqrt_ab_mem : aSerre ≤ Real.sqrt (aSerre * bSerre) ∧ Real.sqrt (aSerre * bSerre) ≤ bSerre := by
  have hleab : aSerre ≤ bSerre := le_of_lt a_lt_b
  have ha2 : aSerre ^ 2 ≤ aSerre * bSerre := by
    nlinarith [mul_le_mul_of_nonneg_left hleab (le_of_lt aSerre_pos)]
  have hb2 : aSerre * bSerre ≤ bSerre ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hleab (le_of_lt bSerre_pos)]
  have hsq_a : Real.sqrt (aSerre ^ 2) = aSerre := by
    exact Real.sqrt_sq (le_of_lt aSerre_pos)
  have hsq_b : Real.sqrt (bSerre ^ 2) = bSerre := by
    exact Real.sqrt_sq (le_of_lt bSerre_pos)
  constructor
  · have h : Real.sqrt (aSerre ^ 2) ≤ Real.sqrt (aSerre * bSerre) := Real.sqrt_le_sqrt ha2
    rwa [hsq_a] at h
  · have h : Real.sqrt (aSerre * bSerre) ≤ Real.sqrt (bSerre ^ 2) := Real.sqrt_le_sqrt hb2
    rwa [hsq_b] at h

/-- The first moment of μ lies in `[0,bSerre]`. -/
lemma mu_bounds : 0 ≤ (∫ x : ℝ, x ∂muS) ∧ (∫ x : ℝ, x ∂muS) ≤ bSerre := by
  have hm : (∫ x : ℝ, x ∂muS) = gSerre * Real.sqrt (aSerre * bSerre) +
      (1 - gSerre) * (aSerre + bSerre) / 2 := by
    unfold muS
    exact serre_mean (a := aSerre) (b := bSerre) (γ := gSerre)
      aSerre_pos a_lt_b gSerre_pos.le gSerre_le_one
  have hγ0 : 0 ≤ gSerre := le_of_lt gSerre_pos
  have h1γ0 : 0 ≤ 1 - gSerre := by linarith [gSerre_le_one]
  have hs := sqrt_ab_mem
  have hmida : aSerre ≤ (aSerre + bSerre) / 2 := by linarith
  have hmidb : (aSerre + bSerre) / 2 ≤ bSerre := by linarith
  constructor
  · have h1 : gSerre * aSerre ≤ gSerre * Real.sqrt (aSerre * bSerre) :=
      mul_le_mul_of_nonneg_left hs.1 hγ0
    have h2' : (1 - gSerre) * aSerre ≤ (1 - gSerre) * ((aSerre + bSerre) / 2) :=
      mul_le_mul_of_nonneg_left hmida h1γ0
    have h2 : (1 - gSerre) * aSerre ≤ (1 - gSerre) * (aSerre + bSerre) / 2 := by
      rwa [show (1 - gSerre) * ((aSerre + bSerre) / 2) = (1 - gSerre) * (aSerre + bSerre) / 2 by ring] at h2'
    calc
      (0 : ℝ) ≤ aSerre := le_of_lt aSerre_pos
      _ = gSerre * aSerre + (1 - gSerre) * aSerre := by ring
      _ ≤ gSerre * Real.sqrt (aSerre * bSerre) + (1 - gSerre) * (aSerre + bSerre) / 2 := by
        exact add_le_add h1 h2
      _ = (∫ x : ℝ, x ∂muS) := by
        rw [hm]
  · have h1 : gSerre * Real.sqrt (aSerre * bSerre) ≤ gSerre * bSerre :=
      mul_le_mul_of_nonneg_left hs.2 hγ0
    have h2' : (1 - gSerre) * ((aSerre + bSerre) / 2) ≤ (1 - gSerre) * bSerre :=
      mul_le_mul_of_nonneg_left hmidb h1γ0
    have h2 : (1 - gSerre) * (aSerre + bSerre) / 2 ≤ (1 - gSerre) * bSerre := by
      rwa [show (1 - gSerre) * ((aSerre + bSerre) / 2) = (1 - gSerre) * (aSerre + bSerre) / 2 by ring] at h2'
    calc
      (∫ x : ℝ, x ∂muS) = gSerre * Real.sqrt (aSerre * bSerre) + (1 - gSerre) * (aSerre + bSerre) / 2 := by
        rw [hm]
      _ ≤ gSerre * bSerre + (1 - gSerre) * bSerre := by
        exact add_le_add h1 h2
      _ = bSerre := by ring


lemma prune_avg_close {N : ℕ} (hN : 1 ≤ N) :
    |((∑ k : Fin N, alpha (N + 2) (k.val + 2)) / (N : ℝ)) - (∫ x : ℝ, x ∂muS)|
      ≤ (4 * bSerre + qRateC) / (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  let Sfin : ℝ := ∑ k : Fin N, alpha (N + 2) (k.val + 2)
  let Sall : ℝ := ∑ i ∈ Finset.Icc 1 (N + 2), alpha (N + 2) i
  let Sint : ℝ := ∑ i ∈ Finset.Icc 2 (N + 1), alpha (N + 2) i
  have hre : Sfin = Sint := by
    dsimp [Sfin, Sint]
    exact (sum_Icc_two_shift_fin (N := N) (g := alpha (N + 2))).symm
  have hsplit : Sall = alpha (N + 2) 1 + alpha (N + 2) (N + 2) + Sint := by
    dsimp [Sall, Sint]
    exact sum_Icc_one_split (N := N) (g := alpha (N + 2))
  have hq : |Sall / (((N + 2 : ℕ) : ℝ)) - (∫ x : ℝ, x ∂muS)| ≤ qRateC / (((N + 2 : ℕ) : ℝ)) := by
    dsimp [Sall]
    exact qRateC_bound (N + 2) (by omega)
  have halpha_i (i : ℕ) (hi : i ∈ Finset.Icc 1 (N + 2)) :
      aSerre ≤ alpha (N + 2) i ∧ alpha (N + 2) i ≤ bSerre :=
    alpha_mem_Icc (n := N + 2) (hn := by omega)
      (hi := (Finset.mem_Icc.mp hi).1) (hin := (Finset.mem_Icc.mp hi).2)
  have hSall0 : 0 ≤ Sall := by
    dsimp [Sall]
    exact Finset.sum_nonneg (fun i hi => le_trans (le_of_lt aSerre_pos) (halpha_i i hi).1)
  have hSall_b : Sall ≤ (((N + 2 : ℕ) : ℝ)) * bSerre := by
    dsimp [Sall]
    have hsum : (∑ i ∈ Finset.Icc 1 (N + 2), alpha (N + 2) i) ≤
        (∑ i ∈ Finset.Icc 1 (N + 2), bSerre) := by
      exact Finset.sum_le_sum (fun i hi => (halpha_i i hi).2)
    have hcard : (Finset.Icc 1 (N + 2)).card = N + 2 := by
      rw [Nat.card_Icc]
      omega
    rw [Finset.sum_const, hcard] at hsum
    simpa using hsum
  have hscale : |Sall / (N : ℝ) - Sall / (((N + 2 : ℕ) : ℝ))| ≤ (2 * bSerre) / (N : ℝ) := by
    have hM0 : (((N + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hfrac : (N : ℝ)⁻¹ - (((N + 2 : ℕ) : ℝ))⁻¹ = 2 / ((N : ℝ) * (((N + 2 : ℕ) : ℝ))) := by
      field_simp [hN0, hM0]
      push_cast
      ring
    have hdiff : Sall / (N : ℝ) - Sall / (((N + 2 : ℕ) : ℝ)) =
        Sall * (2 / ((N : ℝ) * (((N + 2 : ℕ) : ℝ)))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      rw [← mul_sub]
      rw [hfrac]
    have hnonneg : 0 ≤ Sall / (N : ℝ) - Sall / (((N + 2 : ℕ) : ℝ)) := by
      rw [hdiff]
      exact mul_nonneg hSall0 (by positivity)
    rw [abs_of_nonneg hnonneg]
    rw [hdiff]
    calc
      Sall * (2 / ((N : ℝ) * (((N + 2 : ℕ) : ℝ)))) ≤
          (((N + 2 : ℕ) : ℝ)) * bSerre * (2 / ((N : ℝ) * (((N + 2 : ℕ) : ℝ)))) := by
        exact mul_le_mul_of_nonneg_right hSall_b (by positivity)
      _ = (2 * bSerre) / (N : ℝ) := by
        field_simp [hN0, hM0]
  have hq2 : |Sall / (N : ℝ) - (∫ x : ℝ, x ∂muS)|
      ≤ (2 * bSerre) / (N : ℝ) + qRateC / (((N + 2 : ℕ) : ℝ)) := by
    have htri : |Sall / (N : ℝ) - (∫ x : ℝ, x ∂muS)| ≤
        |Sall / (N : ℝ) - Sall / (((N + 2 : ℕ) : ℝ))| +
          |Sall / (((N + 2 : ℕ) : ℝ)) - (∫ x : ℝ, x ∂muS)| := by
      rw [show Sall / (N : ℝ) - (∫ x : ℝ, x ∂muS) =
          (Sall / (N : ℝ) - Sall / (((N + 2 : ℕ) : ℝ))) +
            (Sall / (((N + 2 : ℕ) : ℝ)) - (∫ x : ℝ, x ∂muS)) by ring]
      exact abs_add_le _ _
    exact le_trans htri (add_le_add hscale hq)
  have abs_sub_le_abs_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    rw [sub_eq_add_neg]
    simpa using abs_add_le a (-b)
  have hend : |(alpha (N + 2) 1 + alpha (N + 2) (N + 2)) / (N : ℝ)| ≤ (2 * bSerre) / (N : ℝ) := by
    have hb1n : 0 ≤ alpha (N + 2) 1 :=
      le_trans (le_of_lt aSerre_pos) ((halpha_i 1 (by rw [Finset.mem_Icc]; omega)).1)
    have hbMn : 0 ≤ alpha (N + 2) (N + 2) :=
      le_trans (le_of_lt aSerre_pos) ((halpha_i (N + 2) (by rw [Finset.mem_Icc]; omega)).1)
    have hb1 : alpha (N + 2) 1 ≤ bSerre := (halpha_i 1 (by rw [Finset.mem_Icc]; omega)).2
    have hbM : alpha (N + 2) (N + 2) ≤ bSerre := (halpha_i (N + 2) (by rw [Finset.mem_Icc]; omega)).2
    have hpos : 0 ≤ alpha (N + 2) 1 + alpha (N + 2) (N + 2) := add_nonneg hb1n hbMn
    rw [abs_of_nonneg (div_nonneg hpos (le_of_lt hNpos))]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hNpos)
  have hmain : |Sfin / (N : ℝ) - (∫ x : ℝ, x ∂muS)| ≤
      (2 * bSerre) / (N : ℝ) + qRateC / (((N + 2 : ℕ) : ℝ)) + (2 * bSerre) / (N : ℝ) := by
    have hS : Sint = Sall - alpha (N + 2) 1 - alpha (N + 2) (N + 2) := by
      rw [hsplit]
      ring
    calc
      |Sfin / (N : ℝ) - (∫ x : ℝ, x ∂muS)| = |Sint / (N : ℝ) - (∫ x : ℝ, x ∂muS)| := by
        rw [hre]
      _ = |(Sall / (N : ℝ) - (alpha (N + 2) 1 + alpha (N + 2) (N + 2)) / (N : ℝ)) -
            (∫ x : ℝ, x ∂muS)| := by
        congr 1
        rw [hS]
        ring
      _ ≤ |Sall / (N : ℝ) - (∫ x : ℝ, x ∂muS)| +
          |(alpha (N + 2) 1 + alpha (N + 2) (N + 2)) / (N : ℝ)| := by
        rw [show (Sall / (N : ℝ) - ((alpha (N + 2) 1 + alpha (N + 2) (N + 2)) / (N : ℝ))) -
              (∫ x : ℝ, x ∂muS)
            = (Sall / (N : ℝ) - (∫ x : ℝ, x ∂muS)) -
                ((alpha (N + 2) 1 + alpha (N + 2) (N + 2)) / (N : ℝ)) by ring]
        exact abs_sub_le_abs_abs (Sall / (N : ℝ) - (∫ x : ℝ, x ∂muS))
          ((alpha (N + 2) 1 + alpha (N + 2) (N + 2)) / (N : ℝ))
      _ ≤ (2 * bSerre) / (N : ℝ) + qRateC / (((N + 2 : ℕ) : ℝ)) + (2 * bSerre) / (N : ℝ) := by
        exact add_le_add hq2 hend
  have hfinal : (2 * bSerre) / (N : ℝ) + qRateC / (((N + 2 : ℕ) : ℝ)) + (2 * bSerre) / (N : ℝ)
      ≤ (4 * bSerre + qRateC) / (N : ℝ) := by
    have hdiv : qRateC / (((N + 2 : ℕ) : ℝ)) ≤ qRateC / (N : ℝ) := by
      exact div_le_div_of_nonneg_left (le_of_lt qRateC_pos) hNpos
        (by exact_mod_cast (by omega : N ≤ N + 2))
    have hbN : (4 * bSerre) / (N : ℝ) = (2 * bSerre) / (N : ℝ) + (2 * bSerre) / (N : ℝ) := by
      field_simp [hN0]
      ring
    calc
      (2 * bSerre) / (N : ℝ) + qRateC / (((N + 2 : ℕ) : ℝ)) + (2 * bSerre) / (N : ℝ)
          = ((2 * bSerre) / (N : ℝ) + (2 * bSerre) / (N : ℝ)) + qRateC / (((N + 2 : ℕ) : ℝ)) := by ring
      _ = (4 * bSerre) / (N : ℝ) + qRateC / (((N + 2 : ℕ) : ℝ)) := by rw [hbN]
      _ ≤ (4 * bSerre) / (N : ℝ) + qRateC / (N : ℝ) := by
        exact add_le_add le_rfl hdiv
      _ = (4 * bSerre + qRateC) / (N : ℝ) := by
        field_simp [hN0]
  calc
    |((∑ k : Fin N, alpha (N + 2) (k.val + 2)) / (N : ℝ)) - (∫ x : ℝ, x ∂muS)|
        = |Sfin / (N : ℝ) - (∫ x : ℝ, x ∂muS)| := by
          dsimp [Sfin]
    _ ≤ (2 * bSerre) / (N : ℝ) + qRateC / (((N + 2 : ℕ) : ℝ)) + (2 * bSerre) / (N : ℝ) := hmain
    _ ≤ (4 * bSerre + qRateC) / (N : ℝ) := hfinal



/-- Bound on the mean of a disjoint union of `N` pruned quantiles and `Dr`
arbitrary points of `[0,bSerre]`: with `n = N + Dr`,
`|((Σpruned + Σβ)/n) − μ₁| ≤ (4·bSerre + qRateC + bSerre·Dr)/n`. -/
lemma split_avg_close {N Dr : ℕ} {β : Fin Dr → ℝ}
    (hN : 1 ≤ N) (hβ : ∀ l, 0 ≤ β l ∧ β l ≤ bSerre) :
    |(((∑ k : Fin N, alpha (N + 2) (k.val + 2)) + (∑ l : Fin Dr, β l)) /
        ((N + Dr : ℕ) : ℝ)) - (∫ x : ℝ, x ∂muS)|
      ≤ (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (((N + Dr : ℕ) : ℝ)) := by
  have hpa := prune_avg_close hN
  let G : ℝ := ∑ k : Fin N, alpha (N + 2) (k.val + 2)
  let B : ℝ := ∑ l : Fin Dr, β l
  let n : ℕ := N + Dr
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hnpos : 0 < (n : ℝ) := by
    dsimp [n]
    positivity
  have hnpos : 0 < (((N + Dr : ℕ) : ℝ)) := by
    rw [Nat.cast_add]
    have hDn : 0 ≤ (Dr : ℝ) := by positivity
    nlinarith [hNpos, hDn]
  have hn0 : (((N + Dr : ℕ) : ℝ)) ≠ 0 := ne_of_gt hnpos
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun l hl => (hβ l).1)
  have hBb : B ≤ (Dr : ℝ) * bSerre := by
    dsimp [B]
    have hsum : (∑ l ∈ (Finset.univ : Finset (Fin Dr)), β l) ≤
        (∑ l ∈ (Finset.univ : Finset (Fin Dr)), bSerre) := by
      exact Finset.sum_le_sum (fun l hl => (hβ l).2)
    have hcard : (Finset.univ : Finset (Fin Dr)).card = Dr := by simp
    rw [Finset.sum_const, hcard] at hsum
    simpa using hsum
  have hb := mu_bounds
  by_cases hDr0 : Dr = 0
  · subst Dr
    -- B = 0 and n = N; the goal reduces to `hpa`
    simpa [n, B] using hpa
  · have hDr1 : 1 ≤ Dr := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hDr0)
    have hDrpos : 0 < (Dr : ℝ) := by exact_mod_cast hDr1
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hDr0R : (Dr : ℝ) ≠ 0 := ne_of_gt hDrpos
    have hBavg : |B / (Dr : ℝ) - (∫ x : ℝ, x ∂muS)| ≤ bSerre := by
      have hBavg0 : 0 ≤ B / (Dr : ℝ) := div_nonneg hB0 (le_of_lt hDrpos)
      have hBavgle : B / (Dr : ℝ) ≤ bSerre := by
        rw [div_le_iff₀ hDrpos]
        simpa [mul_comm] using hBb
      have hμ0 : 0 ≤ (∫ x : ℝ, x ∂muS) := hb.1
      have hμle : (∫ x : ℝ, x ∂muS) ≤ bSerre := hb.2
      have h1 : B / (Dr : ℝ) - (∫ x : ℝ, x ∂muS) ≤ bSerre := by linarith
      have h2 : -bSerre ≤ B / (Dr : ℝ) - (∫ x : ℝ, x ∂muS) := by linarith
      rw [abs_le]
      exact ⟨h2, h1⟩
    have hG : |G / (N : ℝ) - (∫ x : ℝ, x ∂muS)| ≤ (4 * bSerre + qRateC) / (N : ℝ) := by
      simpa [G] using hpa
    have hdecomp : (G + B) / (n : ℝ) - (∫ x : ℝ, x ∂muS) =
        (N : ℝ) / (n : ℝ) * (G / (N : ℝ) - (∫ x : ℝ, x ∂muS)) +
          (Dr : ℝ) / (n : ℝ) * (B / (Dr : ℝ) - (∫ x : ℝ, x ∂muS)) := by
      dsimp [n]
      field_simp [hN0, hDr0R, hn0]
      simp [Nat.cast_add]
      ring
    have htri : |(G + B) / (n : ℝ) - (∫ x : ℝ, x ∂muS)| ≤
        (N : ℝ) / (n : ℝ) * |G / (N : ℝ) - (∫ x : ℝ, x ∂muS)| +
          (Dr : ℝ) / (n : ℝ) * |B / (Dr : ℝ) - (∫ x : ℝ, x ∂muS)| := by
      rw [hdecomp]
      have h1 := abs_add_le ((N : ℝ) / (n : ℝ) * (G / (N : ℝ) - (∫ x : ℝ, x ∂muS)))
        ((Dr : ℝ) / (n : ℝ) * (B / (Dr : ℝ) - (∫ x : ℝ, x ∂muS)))
      -- |aX + cY| ≤ |aX| + |cY|; aX term: |a·X| = a|X|
      rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg (le_of_lt hNpos) (le_of_lt hnpos)),
        abs_of_nonneg (div_nonneg (le_of_lt hDrpos) (le_of_lt hnpos))] at h1
      exact h1
    have hmain : |(G + B) / (n : ℝ) - (∫ x : ℝ, x ∂muS)| ≤
        (N : ℝ) / (n : ℝ) * ((4 * bSerre + qRateC) / (N : ℝ)) +
          (Dr : ℝ) / (n : ℝ) * bSerre := by
      exact le_trans htri (add_le_add
        (mul_le_mul_of_nonneg_left hG (div_nonneg (le_of_lt hNpos) (le_of_lt hnpos)))
        (mul_le_mul_of_nonneg_left hBavg (div_nonneg (le_of_lt hDrpos) (le_of_lt hnpos))))
    have hcoll : (N : ℝ) / (n : ℝ) * ((4 * bSerre + qRateC) / (N : ℝ)) +
          (Dr : ℝ) / (n : ℝ) * bSerre ≤
        (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (n : ℝ) := by
      dsimp [n]
      field_simp [hN0, hn0]
      exact le_rfl
    have hfin : |(G + B) / ((N + Dr : ℕ) : ℝ) - (∫ x : ℝ, x ∂muS)| ≤
        (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (((N + Dr : ℕ) : ℝ)) := by
      calc
        |(G + B) / (((N + Dr : ℕ) : ℝ)) - (∫ x : ℝ, x ∂muS)|
            = |(G + B) / (n : ℝ) - (∫ x : ℝ, x ∂muS)| := by
                dsimp [n]
        _ ≤ (N : ℝ) / (n : ℝ) * ((4 * bSerre + qRateC) / (N : ℝ)) +
            (Dr : ℝ) / (n : ℝ) * bSerre := hmain
        _ ≤ (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (n : ℝ) := hcoll
        _ = (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (((N + Dr : ℕ) : ℝ)) := by
            dsimp [n]
    calc
      |(((∑ k : Fin N, alpha (N + 2) (k.val + 2)) + (∑ l : Fin Dr, β l)) /
          ((N + Dr : ℕ) : ℝ)) - (∫ x : ℝ, x ∂muS)|
          = |(G + B) / ((N + Dr : ℕ) : ℝ) - (∫ x : ℝ, x ∂muS)| := by
              dsimp [G, B]
      _ ≤ (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (((N + Dr : ℕ) : ℝ)) := hfin


/-- A union mean bound phrased on `Fin n`: if the `α`-values are exactly the
union of the `N` pruned quantiles and the `Dr` bounded `β`-values, then
`|mean(α) − μ₁| ≤ (4·bSerre + qRateC + bSerre·Dr)/n`. -/
lemma union_mean_close {N Dr n : ℕ} {α : Fin n → ℝ} {β : Fin Dr → ℝ}
    (hN1 : 1 ≤ N) (hsum : N + Dr = n)
    (hαunion : (∑ i : Fin n, α i) =
      (∑ k : Fin N, alpha (N + 2) (k.val + 2)) + (∑ l : Fin Dr, β l))
    (hβ : ∀ l, 0 ≤ β l ∧ β l ≤ bSerre) :
    |((∑ i : Fin n, α i) / (n : ℝ)) - (∫ x : ℝ, x ∂muS)|
      ≤ (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (n : ℝ) := by
  have hsc := split_avg_close (N := N) (Dr := Dr) (β := β) hN1 hβ
  rw [hsum] at hsc
  rw [← hαunion] at hsc
  simpa using hsc

end Submission.QuantileMeanBound
