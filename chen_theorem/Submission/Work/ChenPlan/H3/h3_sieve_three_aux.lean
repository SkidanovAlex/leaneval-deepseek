import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.H3.Defs
import Submission.Work.ChenPlan.H3.RemBound
import Submission.Work.ChenPlan.H3.triv_bound_bRem
import Submission.Work.ChenPlan.H3.isLinear_bSieve
import Submission.Work.ChenPlan.H3.isLinearRange_bSieve
import Submission.Work.ChenPlan.H3.isLinear_bSieve_all
import Submission.Work.NumberTheory.Chen.BTermCount.SharpReduction
import Submission.Work.NumberTheory.Chen.BTermCount.bTripleCount_le_tenth
import Submission.Work.NumberTheory.Chen.BTermCount.Bounds
import Submission.Work.NumberTheory.Chen.VsieveOdd_mul_log_le
import Submission.Work.NumberTheory.Chen.ApSumTenth.twoExpGamma_le_sharp

/-!
# Chen's `h3` from the upper linear sieve (2026-09-24 v6 interface, auxiliary development)

REPAIR of `Submission.Work.ChenPlan.H3.h3_of_sieve_two` after the project lead added
`IsLinearMertens s z K` (Richert's `Ω₁ + Ω₂(1,L)`) to `LinearSieveUpper`.  The proof of
`h3_of_sieve_two` is copied verbatim with

* `isLinear_bSieve_all` (three conditions) combined with `IsLinearMertens` for the `h3` sieve
  at a single constant `max K₁ K₂` (`isLinear_bSieve_all_v6_of_interval`);
* the interval Mertens estimate for the odd primes, `OddPrimeIntervalEstimate`, kept as an
  explicit hypothesis here and discharged in `Submission.Work.ChenPlan.H3.h3_of_sieve_three`
  by the delegated lemma `Work.ChenPlan.H3.oddPrime_interval_logDiv`.

The switched `B`-term count of Chen's theorem:
`bTermCount x (chenSiftLimitTenth x) (chenWindowTop x) · (log x)² ≤ (27/10)·x` eventually.

With `M = ⌊x^{1/10}⌋ + 1`, `Y = ⌊x^{1/3}⌋ + 2` and `D = √x/(log x)^B`:

* `bTermCount ≤ survivorCount` (`bTermCount_le_survivorCount`);
* the upper linear sieve applied to `bSieve x M Y` (sifting range `z = Y`, level `D`, `s = 3/2 - o(1)`):
  `survivorCount ≤ #B̄ · VsieveOdd Y · (Utab s + η) + remSum`;
* `#B̄ ≤ (1/2)·x/log x` (`bTripleCount_le_tenth`), `VsieveOdd Y·log x ≤ 3·(149/200)`
  (`VsieveOdd_mul_log_le`), `Utab s ≤ (1005/1000)·(2e^γ)/s ≤ 2.4055` (`twoExpGamma_le_sharp`
  and `s ≥ 14999/10000`), and `remSum = o(x/log²x)` (`remSum_bound`).

The limit constant is `(447/400)·(360795/149990 + 1/1000) + 1/10000 = 2.6903 < 27/10`.
-/

open Finset Filter
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H3

/-- `chenWindowTop x = ⌊x^{1/3}⌋ + 2` tends to infinity: `t ≤ chenWindowTop x` eventually.  (This is
the `z₀ ≤ z` hypothesis of the 2026-09-24 interface, for the real `z₀` returned by the sieve.) -/
private lemma eventually_le_chenWindowTop (t : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, t ≤ (Submission.chenWindowTop x : ℝ) := by
  have h1 : ∀ᶠ x : ℕ in Filter.atTop, t ≤ Real.rpow (x : ℝ) (1 / 3) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop |>.eventually (Filter.eventually_ge_atTop t)
  filter_upwards [h1] with x hx
  have h2 : Real.rpow (x : ℝ) (1 / 3) ≤ (Submission.chenWindowTop x : ℝ) := by
    rw [Submission.chenWindowTop]
    push_cast
    have h3 := Nat.lt_floor_add_one (Real.rpow (x : ℝ) (1 / 3))
    linarith
  linarith

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight
open Work.NumberTheory.Chen.BTermCount

/-- The main argument, from the three auxiliary inputs (the last two being the delegated
`triv_bound_bRem` and `isLinear_bSieve_all`, the latter supplying `IsLinear`, `IsLinearRange` and
`IsLinearLower` at one constant). -/
theorem h3_of_sieve_three_aux
    (hU : Submission.ChenPlan.LinearSieveUpper)
    (htriv : ∃ C : ℝ, 0 < C ∧ TrivInputB C)
    (hisLin : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Submission.ChenPlan.IsLinear
        (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
        (Submission.chenWindowTop x : ℝ) K ∧
      Submission.ChenPlan.IsLinearRange
        (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
        (Submission.chenWindowTop x : ℝ) K ∧
      Submission.ChenPlan.IsLinearLower
        (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
        (Submission.chenWindowTop x : ℝ) K ∧
      Submission.ChenPlan.IsLinearMertens
        (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
        (Submission.chenWindowTop x : ℝ) K) :
    Submission.ChenPlan.H3Statement := by
  obtain ⟨C, hCpos, htriv'⟩ := htriv
  obtain ⟨Bc, hBpos, hrem⟩ := remSum_bound C hCpos htriv' 3 (by norm_num)
  obtain ⟨K, hKnn, hIsLin⟩ := hisLin
  obtain ⟨z₀, hz₀⟩ := Work.NumberTheory.Chen.VsieveOdd_mul_log_le
  obtain ⟨D₀, Z₀, hD₀⟩ := hU K hKnn (1 / 1000) (by norm_num)
  -- ## eventual facts
  have hlog1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hx8 : ∀ᶠ x : ℕ in Filter.atTop, 8 ≤ x := eventually_ge_atTop 8
  have hDbig : ∀ᶠ x : ℕ in Filter.atTop,
      max 4 (D₀ + 1) * (Real.log (x : ℝ)) ^ Bc ≤ Real.sqrt (x : ℝ) := by
    have h := eventually_nat_log_pow_mul_le_rpow Bc (1 / 2) hBpos (by norm_num)
      (max 1 (max 4 (D₀ + 1)))
    filter_upwards [h] with x hx
    rw [Real.sqrt_eq_rpow]
    refine le_trans ?_ hx
    have h1 : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ Bc := Real.rpow_nonneg (by positivity) _
    have h2 : max 4 (D₀ + 1) ≤ max 1 (max 4 (D₀ + 1)) := le_max_right _ _
    exact mul_le_mul_of_nonneg_right h2 h1
  have hYbig : ∀ᶠ x : ℕ in Filter.atTop, max z₀ 4 ≤ Submission.chenWindowTop x := by
    filter_upwards [eventually_ge_atTop (max (z₀ ^ 3) 8)] with x hx
    have hxz : z₀ ^ 3 ≤ x := le_trans (le_max_left _ _) hx
    have hx8' : 8 ≤ x := le_trans (le_max_right _ _) hx
    have h1 : ((z₀ : ℝ)) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      have h2 : ((z₀ : ℝ)) ^ (3 : ℕ) ≤ (x : ℝ) := by
        have h2' : (z₀ : ℕ) ^ 3 ≤ x := hxz
        exact_mod_cast h2'
      calc ((z₀ : ℝ)) = (((z₀ : ℝ)) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_natCast ((z₀ : ℝ)) 3, ← Real.rpow_mul (by positivity)]
            norm_num
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    have h3 : (z₀ : ℕ) ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := Nat.le_floor h1
    have h4 : 4 ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 2 := by
      have h5 : (2 : ℕ) ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
        apply Nat.le_floor
        push_cast
        calc (2 : ℝ) = (8 : ℝ) ^ ((1 : ℝ) / 3) := by
              rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) from by norm_num,
                ← Real.rpow_natCast (2 : ℝ) 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
              norm_num
          _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
              Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx8') (by norm_num)
      omega
    rw [Submission.chenWindowTop, show Real.rpow (x : ℝ) ((1 : ℝ) / 3) = (x : ℝ) ^ ((1 : ℝ) / 3) from rfl]
    exact max_le (by omega) h4
  have hloglog : ∀ᶠ x : ℕ in Filter.atTop,
      Bc * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) / 60000 := by
    have hlittle : (fun x : ℕ => Real.log (Real.log (x : ℝ))) =o[Filter.atTop]
        (fun x : ℕ => Real.log (x : ℝ)) := by
      have h := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).comp_tendsto
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      have h' : (fun x : ℕ => Real.log (Real.log (x : ℝ))) =o[Filter.atTop]
          (fun x : ℕ => (Real.log (x : ℝ)) ^ (1 : ℝ)) := h
      simpa [Real.rpow_one] using h'
    have hc : (0 : ℝ) < 1 / (60000 * (Bc + 1)) := by positivity
    filter_upwards [(Asymptotics.isLittleO_iff.mp hlittle hc), hlog1] with x hx hlog1x
    have hlogxnn : (0 : ℝ) ≤ Real.log (x : ℝ) := le_trans zero_le_one hlog1x
    rw [Real.norm_of_nonneg (Real.log_nonneg hlog1x), Real.norm_of_nonneg hlogxnn] at hx
    have hB : Bc * (1 / (60000 * (Bc + 1))) ≤ 1 / 60000 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 60000 * (Bc + 1))]
      nlinarith [hBpos]
    calc Bc * Real.log (Real.log (x : ℝ))
        ≤ Bc * ((1 / (60000 * (Bc + 1))) * Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_left hx hBpos.le
      _ = (Bc * (1 / (60000 * (Bc + 1)))) * Real.log (x : ℝ) := by ring
      _ ≤ (1 / 60000) * Real.log (x : ℝ) := mul_le_mul_of_nonneg_right hB hlogxnn
      _ = Real.log (x : ℝ) / 60000 := by ring
  have hlogbig : ∀ᶠ x : ℕ in Filter.atTop, 100000 ≤ Real.log (x : ℝ) :=
    eventually_const_le_nat_log 100000
  filter_upwards [hDbig, hYbig, eventually_le_chenWindowTop Z₀, hloglog, hlogbig, hlog1, hx8,
    hrem, hIsLin, bTripleCount_le_tenth]
    with x hDbigx hYbigx hZ₀evx hloglogx hlogbigx hlog1x hx8x hremx hIsLinx htriplex
  set M : ℕ := Submission.chenSiftLimitTenth x with hM
  set Y : ℕ := Submission.chenWindowTop x with hY
  set L : ℝ := Real.log (x : ℝ) with hL
  set D : ℝ := Real.sqrt (x : ℝ) / L ^ Bc with hD
  have hx1 : 1 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hLpos : 0 < L := by rw [hL]; linarith
  have hL1 : 1 ≤ L := by rw [hL]; exact hlog1x
  have hY4 : 4 ≤ Y := le_trans (le_max_right _ _) hYbigx
  have hz0Y : z₀ ≤ Y := le_trans (le_max_left _ _) hYbigx
  have hY2 : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (by omega : 2 ≤ Y)
  have hYlog_pos : 0 < Real.log (Y : ℝ) := Real.log_pos (by linarith [hY2])
  have hYge : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (Y : ℝ) := by
    rw [hY, Submission.chenWindowTop]
    have hlt := Nat.lt_floor_add_one (Real.rpow (x : ℝ) ((1 : ℝ) / 3))
    have : Real.rpow (x : ℝ) ((1 : ℝ) / 3)
        ≤ ((⌊Real.rpow (x : ℝ) ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) + 2 := by linarith
    simpa using this
  have hYle : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [hY]; exact chenWindowTop_le_two_rpow x hx8x
  have hDle_sum : D ≤ Real.sqrt (x : ℝ) := by
    rw [hD, div_le_iff₀ (Real.rpow_pos_of_pos hLpos Bc)]
    have h1 : (1 : ℝ) ≤ L ^ Bc := Real.one_le_rpow hL1 hBpos.le
    calc Real.sqrt (x : ℝ) ≤ Real.sqrt (x : ℝ) * 1 := by rw [mul_one]
      _ ≤ Real.sqrt (x : ℝ) * L ^ Bc := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
  have hDge4 : 4 ≤ D := by
    rw [hD, le_div_iff₀ (Real.rpow_pos_of_pos hLpos Bc), hL]
    have h1 : (4 : ℝ) * (Real.log (x : ℝ)) ^ Bc
        ≤ max 4 (D₀ + 1) * (Real.log (x : ℝ)) ^ Bc :=
      mul_le_mul_of_nonneg_right (le_max_left (4 : ℝ) (D₀ + 1)) (Real.rpow_nonneg (by positivity) _)
    linarith [h1, hDbigx]
  have hDleD₀ : D₀ ≤ D := by
    rw [hD, le_div_iff₀ (Real.rpow_pos_of_pos hLpos Bc), hL]
    have h2 : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ Bc := Real.rpow_nonneg (by positivity) _
    have h1 : D₀ * (Real.log (x : ℝ)) ^ Bc
        ≤ max 4 (D₀ + 1) * (Real.log (x : ℝ)) ^ Bc := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right (4 : ℝ) (D₀ + 1)) h2)
      exact mul_le_mul_of_nonneg_right (by linarith) h2
    linarith [h1, hDbigx]
  -- ## the logarithm estimates
  have hlogY : Real.log (Y : ℝ) ≤ Real.log 2 + L / 3 := by
    have h2 : Real.log (Y : ℝ) ≤ Real.log (2 * (x : ℝ) ^ ((1 : ℝ) / 3)) :=
      Real.log_le_log (by positivity) hYle
    have h3 : Real.log (2 * (x : ℝ) ^ ((1 : ℝ) / 3)) = Real.log 2 + L / 3 := by
      rw [Real.log_mul (by norm_num) (by positivity : (x : ℝ) ^ ((1 : ℝ) / 3) ≠ 0),
        Real.log_rpow hxpos, hL]
      ring
    rw [h3] at h2
    exact h2
  have hlogD : Real.log D = L / 2 - Bc * Real.log L := by
    rw [hD, Real.log_div (ne_of_gt (Real.sqrt_pos.mpr hxpos)) (by positivity),
      Real.log_sqrt (le_of_lt hxpos), Real.log_rpow hLpos, hL]
  have hlogLnn : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hs_lt : Real.log D / Real.log (Y : ℝ) < 3 / 2 := by
    rw [div_lt_iff₀ hYlog_pos, hlogD]
    have hLY : L / 3 ≤ Real.log (Y : ℝ) := by
      have h2 : Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤ Real.log (Y : ℝ) :=
        Real.log_le_log (by positivity) hYge
      rw [Real.log_rpow hxpos] at h2
      linarith [h2]
    have hpos : 0 < Bc * Real.log L :=
      mul_pos hBpos (Real.log_pos (by linarith [hlogbigx]))
    nlinarith [hLY, hpos]
  have hs_ge : (14999 / 10000 : ℝ) ≤ Real.log D / Real.log (Y : ℝ) := by
    rw [le_div_iff₀ hYlog_pos, hlogD]
    have hll : Bc * Real.log L ≤ L / 60000 := hloglogx
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have h1 : (14999 / 10000 : ℝ) * Real.log (Y : ℝ)
        ≤ (14999 / 10000 : ℝ) * (Real.log 2 + L / 3) :=
      mul_le_mul_of_nonneg_left hlogY (by norm_num)
    have h2 : (14999 / 10000 : ℝ) * (Real.log 2 + L / 3)
        = (14999 / 10000 : ℝ) * Real.log 2 + (14999 / 30000 : ℝ) * L := by ring
    have h3 : (14999 / 10000 : ℝ) * Real.log 2 ≤ 14999 / 10000 :=
      mul_le_of_le_one_right (by norm_num) hlog2
    linarith [h1, h2, h3, hll, hlogbigx]
  have hs_pos : 0 < Real.log D / Real.log (Y : ℝ) :=
    div_pos (Real.log_pos (by linarith [hDge4])) hYlog_pos
  have hs1 : 1 ≤ Real.log D / Real.log (Y : ℝ) := le_trans (by norm_num) hs_ge
  -- ## `Utab` at this `s`
  have hUtab_le : Submission.ChenPlan.Utab (Real.log D / Real.log (Y : ℝ)) ≤ (360795 : ℝ) / 149990 := by
    rw [Submission.ChenPlan.Utab, if_pos hs_lt]
    have h2e : 2 * Real.exp Real.eulerMascheroniConstant ≤ (359 : ℝ) / 100 := by
      simpa [Work.NumberTheory.Chen.ApSumTenth.twoExpGamma] using
        Work.NumberTheory.Chen.ApSumTenth.twoExpGamma_le_sharp
    have hnum : (1005 / 1000 : ℝ) * (2 * Real.exp Real.eulerMascheroniConstant)
        ≤ (1005 / 1000 : ℝ) * (359 / 100) :=
      mul_le_mul_of_nonneg_left h2e (by norm_num)
    have hnum2 : (0 : ℝ) ≤ (1005 / 1000 : ℝ) * (359 / 100) := by norm_num
    calc (1005 / 1000 : ℝ) * (2 * Real.exp Real.eulerMascheroniConstant)
          / (Real.log D / Real.log (Y : ℝ))
        ≤ (1005 / 1000 : ℝ) * (359 / 100) / (Real.log D / Real.log (Y : ℝ)) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hs_pos)
      _ ≤ (1005 / 1000 : ℝ) * (359 / 100) / (14999 / 10000 : ℝ) :=
          div_le_div_of_nonneg_left hnum2 (by norm_num) hs_ge
      _ = 360795 / 149990 := by norm_num
  -- ## the sieve inequality
  have hIsLinY : Submission.ChenPlan.IsLinear (bSieve x M Y) (Y : ℝ) K := by
    rw [hM, hY]; exact hIsLinx.1
  have hIsLinRY : Submission.ChenPlan.IsLinearRange (bSieve x M Y) (Y : ℝ) K := by
    rw [hM, hY]; exact hIsLinx.2.1
  have hIsLinLowerY : Submission.ChenPlan.IsLinearLower (bSieve x M Y) (Y : ℝ) K := by
    rw [hM, hY]; exact hIsLinx.2.2.1
  have hIsLinMertensY : Submission.ChenPlan.IsLinearMertens (bSieve x M Y) (Y : ℝ) K := by
    rw [hM, hY]; exact hIsLinx.2.2.2
  have hZ₀Y : Z₀ ≤ (Y : ℝ) := by rw [hY]; exact hZ₀evx
  have hsieve := hD₀ (bSieve x M Y) (Y : ℝ) D hDleD₀ hZ₀Y hY2 hIsLinY hIsLinRY hIsLinLowerY
    hIsLinMertensY (Nat.cast_nonneg _) hs1
  rw [bSieve_siftedSum, bSieve_sieveV,
    show (bSieve x M Y).totalMass = ((bProdSet x M Y).card : ℝ) from rfl] at hsieve
  -- ## bounds on the factors
  have hE : (((bProdSet x M Y).card : ℝ)) ≤ (1 / 2 : ℝ) * (x : ℝ) / L := by
    have h1 : (bProdCount x M Y : ℝ) ≤ (bTripleCount x M Y : ℝ) := by
      exact_mod_cast bProdCount_le_bTripleCount x M Y
    have h2 : (bTripleCount x M Y : ℝ) ≤ (1 / 2 : ℝ) * (x : ℝ) / L := by
      have h3 := htriplex M Y (by rw [hM]; exact rpow_tenth_le_chenSiftLimitTenth x) hYge hYle
      simpa [hL] using h3
    rw [show (bProdSet x M Y).card = bProdCount x M Y from rfl]
    exact le_trans h1 h2
  have hV : VsieveOdd Y * L ≤ (447 : ℝ) / 200 := by
    have h1 : VsieveOdd Y * Real.log (Y : ℝ) ≤ (149 : ℝ) / 200 := hz₀ Y hz0Y
    have h2 : L ≤ 3 * Real.log (Y : ℝ) := by
      have h4 : (x : ℝ) ≤ (Y : ℝ) ^ (3 : ℕ) := by
        calc (x : ℝ) ≤ ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
              rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (le_of_lt hxpos)]
              norm_num
          _ ≤ (Y : ℝ) ^ (3 : ℕ) :=
              pow_le_pow_left₀ (Real.rpow_nonneg (le_of_lt hxpos) _) hYge 3
      have h5 : Real.log (x : ℝ) ≤ Real.log ((Y : ℝ) ^ (3 : ℕ)) :=
        Real.log_le_log (by positivity) h4
      rw [Real.log_pow] at h5
      push_cast at h5
      rw [hL]
      linarith [h5]
    calc VsieveOdd Y * L = (VsieveOdd Y * Real.log (Y : ℝ)) * (L / Real.log (Y : ℝ)) := by
          field_simp
      _ ≤ ((149 : ℝ) / 200) * 3 := by
          refine mul_le_mul h1 ?_ (by positivity) (by norm_num)
          rw [div_le_iff₀ hYlog_pos]
          linarith [h2]
      _ = 447 / 200 := by norm_num
  have hremx' : Submission.ChenPlan.remSum (bSieve x M Y) D ≤ (x : ℝ) / L ^ (3 : ℝ) := by
    have h := hremx
    rw [hD, hL] at h
    exact h
  -- ## assembly
  have hmain : (survivorCount x M Y : ℝ) * L ^ (2 : ℝ)
      ≤ ((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) * (x : ℝ) + (x : ℝ) / L := by
    have hstep : (survivorCount x M Y : ℝ)
        ≤ ((bProdSet x M Y).card : ℝ) * VsieveOdd Y * ((360795 : ℝ) / 149990 + 1 / 1000)
          + (x : ℝ) / L ^ (3 : ℝ) := by
      refine le_trans hsieve ?_
      have hfac : (0 : ℝ) ≤ ((bProdSet x M Y).card : ℝ) * VsieveOdd Y :=
        mul_nonneg (Nat.cast_nonneg _) (VsieveOdd_nonneg Y)
      have h1 : ((bProdSet x M Y).card : ℝ) * VsieveOdd Y
            * (Submission.ChenPlan.Utab (Real.log D / Real.log (Y : ℝ)) + 1 / 1000)
          ≤ ((bProdSet x M Y).card : ℝ) * VsieveOdd Y
            * ((360795 : ℝ) / 149990 + 1 / 1000) :=
        mul_le_mul_of_nonneg_left (by linarith [hUtab_le]) hfac
      linarith [h1, hremx']
    have hL2 : (0 : ℝ) ≤ L ^ (2 : ℝ) := Real.rpow_nonneg hLpos.le _
    have hstep2 : ((bProdSet x M Y).card : ℝ) * VsieveOdd Y
          * ((360795 : ℝ) / 149990 + 1 / 1000) * L ^ (2 : ℝ)
        ≤ ((1 / 2 : ℝ) * (x : ℝ) / L * ((447 : ℝ) / 200 / L)
            * ((360795 : ℝ) / 149990 + 1 / 1000)) * L ^ (2 : ℝ) := by
      have hV' : VsieveOdd Y ≤ (447 : ℝ) / 200 / L := by
        rw [le_div_iff₀ hLpos]
        exact hV
      have hnn : (0 : ℝ) ≤ VsieveOdd Y := VsieveOdd_nonneg Y
      have h2 : ((bProdSet x M Y).card : ℝ) * VsieveOdd Y
          ≤ ((1 / 2 : ℝ) * (x : ℝ) / L) * ((447 : ℝ) / 200 / L) :=
        mul_le_mul hE hV' hnn (div_nonneg (by positivity) hLpos.le)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by norm_num)) hL2
    have hsimp : ((1 / 2 : ℝ) * (x : ℝ) / L * ((447 : ℝ) / 200 / L)
          * ((360795 : ℝ) / 149990 + 1 / 1000)) * L ^ (2 : ℝ)
        = ((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) * (x : ℝ) := by
      have hLsq : L ^ (2 : ℝ) = L * L := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]; ring
      rw [hLsq]
      field_simp
      ring
    have h3 : (x : ℝ) / L ^ (3 : ℝ) * L ^ (2 : ℝ) = (x : ℝ) / L := by
      have h3' : L ^ (3 : ℝ) = L ^ (2 : ℝ) * L := by
        rw [show (3 : ℝ) = 2 + 1 from by norm_num, Real.rpow_add hLpos, Real.rpow_one]
      rw [h3']
      field_simp
    calc (survivorCount x M Y : ℝ) * L ^ (2 : ℝ)
        ≤ (((bProdSet x M Y).card : ℝ) * VsieveOdd Y
              * ((360795 : ℝ) / 149990 + 1 / 1000) + (x : ℝ) / L ^ (3 : ℝ)) * L ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_right hstep hL2
      _ = ((bProdSet x M Y).card : ℝ) * VsieveOdd Y
              * ((360795 : ℝ) / 149990 + 1 / 1000) * L ^ (2 : ℝ)
            + (x : ℝ) / L ^ (3 : ℝ) * L ^ (2 : ℝ) := by ring
      _ ≤ ((1 / 2 : ℝ) * (x : ℝ) / L * ((447 : ℝ) / 200 / L)
            * ((360795 : ℝ) / 149990 + 1 / 1000)) * L ^ (2 : ℝ) + (x : ℝ) / L :=
          add_le_add hstep2 (le_of_eq h3)
      _ = ((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) * (x : ℝ) + (x : ℝ) / L := by
          rw [hsimp]
  -- ## final numerics
  have hnum : ((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) + 1 / 10000 ≤ (27 : ℝ) / 10 := by
    norm_num
  have hLbig : 10000 ≤ L := by rw [hL]; linarith [hlogbigx]
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hfin : ((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) * (x : ℝ) + (x : ℝ) / L
      ≤ (27 : ℝ) / 10 * (x : ℝ) := by
    have h1 : (x : ℝ) / L ≤ (1 / 10000 : ℝ) * (x : ℝ) := by
      rw [div_le_iff₀ hLpos]
      nlinarith [hLbig, hxnn]
    calc ((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) * (x : ℝ) + (x : ℝ) / L
        ≤ ((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) * (x : ℝ)
            + (1 / 10000 : ℝ) * (x : ℝ) := by linarith [h1]
      _ = (((447 : ℝ) / 400) * (360795 / 149990 + 1 / 1000) + 1 / 10000) * (x : ℝ) := by ring
      _ ≤ (27 : ℝ) / 10 * (x : ℝ) := mul_le_mul_of_nonneg_right hnum hxnn
  have hsurv : (survivorCount x M Y : ℝ) * L ^ (2 : ℝ) ≤ (27 : ℝ) / 10 * (x : ℝ) :=
    le_trans hmain hfin
  have hbt : (Submission.bTermCount x M Y : ℝ) ≤ (survivorCount x M Y : ℝ) := by
    have h := bTermCount_le_survivorCount x M Y
      (by rw [hM]; exact Work.NumberTheory.Chen.one_le_chenSiftLimitTenth x) (by omega)
    exact_mod_cast h
  have hLsq' : L ^ (2 : ℝ) = Real.log (x : ℝ) * Real.log (x : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, pow_two, hL]
  have hsurv' : (survivorCount x M Y : ℝ) * (Real.log (x : ℝ) * Real.log (x : ℝ))
      ≤ (27 : ℝ) / 10 * (x : ℝ) := by
    rw [← hLsq']; exact hsurv
  have hlogxnn : (0 : ℝ) ≤ Real.log (x : ℝ) := le_trans zero_le_one hlog1x
  calc (Submission.bTermCount x M Y : ℝ) * Real.log (x : ℝ) * Real.log (x : ℝ)
      = (Submission.bTermCount x M Y : ℝ) * (Real.log (x : ℝ) * Real.log (x : ℝ)) := by ring
    _ ≤ (survivorCount x M Y : ℝ) * (Real.log (x : ℝ) * Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hbt (by positivity)
    _ ≤ (27 : ℝ) / 10 * (x : ℝ) := hsurv'


/-- The interval Mertens estimate for the odd-prime density `ν p = 1/(p-1)`:
`|Σ_{w ≤ p < z'} log p/(p-1) − log (z'/w)| ≤ K` uniformly in `2 ≤ w < z'`. -/
def OddPrimeIntervalEstimate : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : ℕ) (w z' : ℝ), 2 ≤ w → w < z' → z' ≤ (Y : ℝ) →
    |(∑ p ∈ (Commons.NumberTheory.Chen.ChenEight.oddLt Y).filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
        Real.log (p : ℝ) / ((p : ℝ) - 1)) - Real.log (z' / w)| ≤ K

/-! ## Monotonicity of the four sieve conditions in the constant `K` -/

private lemma isLinear_mono_v6 {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinear s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinear s z K' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun w hw2 hwz => ?_⟩
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  refine le_trans (h2 w hw2 hwz) ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz.le hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

private lemma isLinearRange_mono_v6 {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearRange s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinearRange s z K' := by
  intro w z' hw2 hwz hz'z
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  refine le_trans (h w z' hw2 hwz hz'z) ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz'.le hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

private lemma isLinearLower_mono_v6 {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearLower s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinearLower s z K' := by
  intro w z' hw2 hwz hz'z
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 ≤ Real.log z' := Real.log_nonneg (by linarith)
  refine le_trans ?_ (h w z' hw2 hwz hz'z)
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz' hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

private lemma isLinearMertens_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearMertens s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinearMertens s z K' :=
  ⟨h.1, fun w z' hw hwz hz'z => le_trans (h.2 w z' hw hwz hz'z) hKK⟩

/-! ## `IsLinearMertens` for the sieve problem of Chen's `h3` -/

theorem isLinearMertens_bSieve_of_interval (hint : OddPrimeIntervalEstimate) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x M Y : ℕ),
      Submission.ChenPlan.IsLinearMertens (bSieve x M Y) (Y : ℝ) K := by
  obtain ⟨K, hK, h⟩ := hint
  refine ⟨K, hK, fun x M Y => ⟨?_, ?_⟩⟩
  · intro p hp
    rw [show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl,
      Work.NumberTheory.Chen.BTermCount.primeFactors_oddPrimLt] at hp
    obtain ⟨hpp, hp3, -⟩ := Submission.mem_oddLt.mp hp
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    rw [show (bSieve x M Y).nu = invTotient from rfl, invTotient_apply, Nat.totient_prime hpp,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (show (0 : ℝ) < (p : ℝ) - 1 by linarith) (by norm_num : (0 : ℝ) < 2)]
    linarith
  · intro w z' hw hwz hzY
    rw [show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl,
      Work.NumberTheory.Chen.BTermCount.primeFactors_oddPrimLt]
    have hsum : (∑ p ∈ (oddLt Y).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
        (bSieve x M Y).nu p * Real.log (p : ℝ))
        = ∑ p ∈ (oddLt Y).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
            Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      obtain ⟨hpp, hp3, -⟩ := Submission.mem_oddLt.mp (Finset.mem_filter.mp hp).1
      rw [show (bSieve x M Y).nu = invTotient from rfl, invTotient_apply, Nat.totient_prime hpp,
        Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      rw [inv_mul_eq_div]
    rw [hsum]
    exact h Y w z' hw hwz hzY

theorem isLinear_bSieve_all_v6_of_interval (hint : OddPrimeIntervalEstimate) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Submission.ChenPlan.IsLinear
          (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Submission.chenWindowTop x : ℝ) K ∧
        Submission.ChenPlan.IsLinearRange
          (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Submission.chenWindowTop x : ℝ) K ∧
        Submission.ChenPlan.IsLinearLower
          (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Submission.chenWindowTop x : ℝ) K ∧
        Submission.ChenPlan.IsLinearMertens
          (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Submission.chenWindowTop x : ℝ) K := by
  obtain ⟨K1, hK1, h1⟩ := isLinear_bSieve_all
  obtain ⟨K2, hK2, h2⟩ := isLinearMertens_bSieve_of_interval hint
  refine ⟨max K1 K2, le_trans hK1 (le_max_left _ _), ?_⟩
  filter_upwards [h1] with x hx
  refine ⟨isLinear_mono_v6 hx.1 (le_max_left _ _),
          isLinearRange_mono_v6 hx.2.1 (le_max_left _ _),
          isLinearLower_mono_v6 hx.2.2 (le_max_left _ _), ?_⟩
  exact isLinearMertens_mono (h2 x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
    (le_max_right _ _)

/-- **Chen's `h3` from the upper linear sieve**, from the four v6 sieve hypotheses at one
constant (the last one being the interval Mertens estimate for the odd primes) and the trivial
remainder input. -/
theorem h3_of_sieve_three_of_interval (hU : Submission.ChenPlan.LinearSieveUpper)
    (hint : OddPrimeIntervalEstimate) : Submission.ChenPlan.H3Statement := by
  obtain ⟨C, hCpos, hW⟩ := triv_bound_bRem
  obtain ⟨K, hKnn, hIsLin⟩ := isLinear_bSieve_all_v6_of_interval hint
  refine h3_of_sieve_three_aux hU ⟨C, hCpos, ?_⟩ ⟨K, hKnn, hIsLin⟩
  filter_upwards [hW] with x hx
  intro M Y D h1 h2 h3 h4
  have h := hx M Y D h1 h2 h3 h4
  rw [← Real.rpow_natCast] at h
  exact h

end

end Work.ChenPlan.H3
