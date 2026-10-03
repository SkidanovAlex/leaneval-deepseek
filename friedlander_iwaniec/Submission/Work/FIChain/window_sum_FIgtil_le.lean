import Mathlib
import Submission.Work.FIChain.Defs

namespace Work.FIChain

open Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary estimates

`(1.9)` for the density `g̃ = FIgtil` reads, for `y ≥ 2`,
`∑_{p ≤ y} g̃(p) = log log y + c + O((log y)^{-10} + 1/y)`
(`Submission.ASP.FIgtil_sum_19_nat`).  Below we collect the three real-variable
estimates that the window comparison needs:

* `err_le_errB` : the error term is bounded by the absolute constant
  `errB = (log 2)^{-10} + 1/2` as soon as `y ≥ 2`;
* `log_log_floor_le` : `log log ⌊z⌋ ≤ log log z` for `z ≥ 2`;
* `log_log_sub_two_le` : `log log w - 2 ≤ log log (⌊w⌋ - 1)` for `w ≥ 3`
  (the cost of replacing `w` by `⌊w⌋ - 1`).
-/

/-- The absolute constant dominating the `(1.9)` error term for `y ≥ 2`. -/
private def errB : ℝ := (Real.log 2) ^ (-(10 : ℝ)) + 1 / 2

private lemma errB_nonneg : 0 ≤ errB := by
  rw [errB]
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 0 ≤ (Real.log 2) ^ (-(10 : ℝ)) := Real.rpow_nonneg h.le _
  linarith

/-- `(log y)^{-10} + 1/y ≤ (log 2)^{-10} + 1/2` for `y ≥ 2`. -/
private lemma err_le_errB (y : ℕ) (hy : 2 ≤ y) :
    (Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ) ≤ errB := by
  rw [errB]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlog : Real.log 2 ≤ Real.log (y : ℝ) := Real.log_le_log (by norm_num) hy2
  have h1 : (Real.log (y : ℝ)) ^ (-(10 : ℝ)) ≤ (Real.log 2) ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos h2 hlog (by norm_num)
  have h3 : 1 / (y : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hy2
  linarith

/-- `log log ⌊z⌋ ≤ log log z` for `z ≥ 2`. -/
private lemma log_log_floor_le (z : ℝ) (hz : 2 ≤ z) :
    Real.log (Real.log ((Nat.floor z : ℕ) : ℝ)) ≤ Real.log (Real.log z) := by
  have hN2 : 2 ≤ Nat.floor z := Nat.le_floor hz
  have hNpos : (0 : ℝ) < (Nat.floor z : ℝ) := by
    have : (1 : ℝ) < (Nat.floor z : ℝ) := by exact_mod_cast (by omega : 1 < Nat.floor z)
    linarith
  have hle : ((Nat.floor z : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  refine Real.log_le_log ?_ (Real.log_le_log hNpos hle)
  have : (1 : ℝ) < (Nat.floor z : ℝ) := by exact_mod_cast (by omega : 1 < Nat.floor z)
  exact Real.log_pos this

/-- For `w ≥ 3`, `log log w - 2 ≤ log log (⌊w⌋ - 1)`. -/
private lemma log_log_sub_two_le (w : ℝ) (hw : 3 ≤ w) :
    Real.log (Real.log w) - 2 ≤ Real.log (Real.log ((Nat.floor w - 1 : ℕ) : ℝ)) := by
  have hwr : (3 : ℝ) ≤ w := hw
  have hm3 : 3 ≤ Nat.floor w := Nat.le_floor hwr
  have hm3r : (3 : ℝ) ≤ ((Nat.floor w : ℕ) : ℝ) := by exact_mod_cast hm3
  have hm_le : ((Nat.floor w : ℕ) : ℝ) ≤ w := Nat.floor_le (by linarith)
  have hw_lt : w < ((Nat.floor w : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one w
  have hm1cast : ((Nat.floor w - 1 : ℕ) : ℝ) = ((Nat.floor w : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.floor w)]
    norm_num
  -- `⌊w⌋ - 1 ≥ w/2`
  have hhalf : w / 2 ≤ ((Nat.floor w - 1 : ℕ) : ℝ) := by
    rw [hm1cast]
    linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hstep1 : Real.log w - Real.log 2 ≤ Real.log ((Nat.floor w - 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < w / 2) hhalf
    rwa [Real.log_div (by linarith : w ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h
  -- `log 2 ≤ (3/4) log w`
  have hlog2 : Real.log 2 ≤ (3 / 4) * Real.log w := by
    have h16 := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by norm_num : (16 : ℝ) ≤ 27)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, show (27 : ℝ) = 3 ^ 3 by norm_num,
      Real.log_pow, Real.log_pow] at h16
    push_cast at h16
    have h3 : Real.log 3 ≤ Real.log w := Real.log_le_log (by norm_num) hwr
    linarith
  -- `1/(e·e) ≤ 1/4`
  have hexp2 : (4 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    nlinarith [Real.exp_pos 1]
  have hquarter : Real.log w / (Real.exp 1 * Real.exp 1) ≤ (1 / 4) * Real.log w := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.exp 1 * Real.exp 1)]
    nlinarith [hexp2, hlogw.le]
  have hmain : Real.log w / (Real.exp 1 * Real.exp 1) ≤ Real.log ((Nat.floor w - 1 : ℕ) : ℝ) := by
    have : (1 / 4) * Real.log w ≤ Real.log ((Nat.floor w - 1 : ℕ) : ℝ) := by linarith
    linarith
  have hpos : 0 < Real.log w / (Real.exp 1 * Real.exp 1) := by positivity
  calc Real.log (Real.log w) - 2
      = Real.log (Real.log w / (Real.exp 1 * Real.exp 1)) := by
        rw [Real.log_div (ne_of_gt hlogw) (by positivity),
          Real.log_mul (Real.exp_ne_zero 1) (Real.exp_ne_zero 1), Real.log_exp]
        ring
    _ ≤ Real.log (Real.log ((Nat.floor w - 1 : ℕ) : ℝ)) := Real.log_le_log hpos hmain

/-- For `2 ≤ w < 3`, `log log w ≤ 1`. -/
private lemma log_log_le_one (w : ℝ) (hw2 : 2 ≤ w) (hw3 : w < 3) :
    Real.log (Real.log w) ≤ 1 := by
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlog3w : Real.log w ≤ Real.log 3 := Real.log_le_log (by linarith) (le_of_lt hw3)
  have h1 : Real.log (Real.log w) ≤ Real.log (Real.log 3) :=
    Real.log_le_log (x := Real.log w) (y := Real.log 3) hlogw hlog3w
  have hlog3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    have hexp : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    linarith
  have h2 : Real.log (Real.log 3) ≤ Real.log 2 :=
    Real.log_le_log (Real.log_pos (by norm_num : (1 : ℝ) < 3)) hlog3
  have h3 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    exact le_of_lt Real.exp_one_gt_two
  linarith

/-! ## The window bound -/

/-- **Second-Mertens bound for the FI density over a window.**
There is an absolute constant `C ≥ 0` with, for all `Δ : ℕ` and all reals `2 ≤ w < z' ≤ Δ`,

    ∑_{p < Δ prime, w ≤ p < z'} g̃(p) ≤ log log z' − log log w + C.

Input: (1.9) for `g̃`, i.e. `Submission.ASP.FIgtil_sum_19_nat`:
`∑_{p ≤ y} g̃(p) = log log y + c + O((log y)^{-10} + 1/y)` for `y : ℕ`, `y ≥ 2`.
With `m = ⌊w⌋₊` and `N = ⌊z'⌋₊ ≥ 2` the window is contained in
`(primesBelow (N+1)) \ (primesBelow m)`, so the sum is at most `A(N+1) − A(m)` where
`A(k) = ∑_{p < k} g̃(p)`.  Bound `A(N+1)` above by (1.9) at `y = N` (using `log log N ≤ log log z'`)
and `A(m)` below by (1.9) at `y = m − 1` when `w ≥ 3`, resp. by `0` when `2 ≤ w < 3`
(then `log log w ≤ log log 3`), using `log log (m−1) ≥ log log w − 1`
(which follows from `m − 1 ≥ w/2`), and `(log y)^{-10} + 1/y ≤ (log 2)^{-10} + 1/2` for `y ≥ 2`. -/
theorem window_sum_FIgtil_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Δ : ℕ) (w z' : ℝ), 2 ≤ w → w < z' → z' ≤ (Δ : ℝ) →
      (∑ p ∈ (Nat.primesBelow Δ).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
          Submission.ASP.FIgtil p)
        ≤ Real.log (Real.log z') - Real.log (Real.log w) + C := by
  obtain ⟨c, C0, h19₀⟩ := Submission.ASP.FIgtil_sum_19_nat
  set C1 : ℝ := max C0 0 with hC1
  have hC1nn : 0 ≤ C1 := by rw [hC1]; exact le_max_right _ _
  have h19 : ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, Submission.ASP.FIgtil p)
        - Real.log (Real.log (y : ℝ)) - c|
        ≤ C1 * ((Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ)) := by
    intro y hy
    have herr : 0 ≤ (Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ) := by
      have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
      have hlog : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by linarith)
      have h1 : 0 ≤ (Real.log (y : ℝ)) ^ (-(10 : ℝ)) := Real.rpow_nonneg hlog _
      have h2 : 0 ≤ 1 / (y : ℝ) := by positivity
      linarith
    have hC0C1 : C0 ≤ C1 := by rw [hC1]; exact le_max_left _ _
    exact le_trans (h19₀ y hy) (mul_le_mul_of_nonneg_right hC0C1 herr)
  refine ⟨max (c + C1 * errB + 1) (2 + 2 * (C1 * errB)), ?_, ?_⟩
  · -- nonnegativity of the constant
    have h : 0 ≤ 2 + 2 * (C1 * errB) := by
      have := errB_nonneg
      nlinarith
    exact le_trans h (le_max_right _ _)
  · intro Δ w z' hw hwz hzΔ
    have hw2 : (2 : ℝ) ≤ w := hw
    have hz'2 : (2 : ℝ) ≤ z' := by linarith
    -- the two window endpoints `⌊w⌋`, `⌊z'⌋`
    have hm_le_w : ((Nat.floor w : ℕ) : ℝ) ≤ w := Nat.floor_le (by linarith)
    have hw_lt_m : w < ((Nat.floor w : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one w
    have hN_le_z : ((Nat.floor z' : ℕ) : ℝ) ≤ z' := Nat.floor_le (by linarith)
    have hz_lt_N : z' < ((Nat.floor z' : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one z'
    have hN2 : 2 ≤ Nat.floor z' := Nat.le_floor hz'2
    -- the inclusion of the window in `primesBelow (⌊z'⌋+1) \ primesBelow ⌊w⌋`
    have hWsub : ((Nat.primesBelow Δ).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'))
        ⊆ Nat.primesBelow (Nat.floor z' + 1) \ Nat.primesBelow (Nat.floor w) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      obtain ⟨⟨hpΔ, hpprime⟩, hwp, hpz⟩ := hp
      rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow]
      refine ⟨⟨?_, hpprime⟩, ?_⟩
      · have hpN : p ≤ Nat.floor z' := Nat.le_floor (le_of_lt hpz)
        omega
      · intro hpm
        have hpm' : (p : ℝ) < ((Nat.floor w : ℕ) : ℝ) := by exact_mod_cast hpm.1
        linarith
    have hS_le : (∑ p ∈ (Nat.primesBelow Δ).filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), Submission.ASP.FIgtil p)
        ≤ ∑ p ∈ Nat.primesBelow (Nat.floor z' + 1) \ Nat.primesBelow (Nat.floor w),
            Submission.ASP.FIgtil p :=
      Finset.sum_le_sum_of_subset_of_nonneg hWsub
        (fun i _ _ => Submission.ASP.FIgtil_nonneg i)
    have hsub' : Nat.primesBelow (Nat.floor w) ⊆ Nat.primesBelow (Nat.floor z' + 1) := by
      apply Nat.primesBelow_mono
      have h1 : ((Nat.floor w : ℕ) : ℝ) < ((Nat.floor z' : ℕ) : ℝ) + 1 :=
        lt_of_le_of_lt hm_le_w (lt_trans hwz hz_lt_N)
      have h2 : ((Nat.floor w : ℕ) : ℝ) < ((Nat.floor z' + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact le_of_lt (by exact_mod_cast h2)
    have hsdiff : (∑ p ∈ Nat.primesBelow (Nat.floor z' + 1) \ Nat.primesBelow (Nat.floor w),
            Submission.ASP.FIgtil p)
        = (∑ p ∈ Nat.primesBelow (Nat.floor z' + 1), Submission.ASP.FIgtil p)
          - ∑ p ∈ Nat.primesBelow (Nat.floor w), Submission.ASP.FIgtil p := by
      have h := Finset.sum_sdiff hsub' (f := fun p => Submission.ASP.FIgtil p)
      linarith
    -- (1.9) at `y = ⌊z'⌋`
    have hAN : (∑ p ∈ Nat.primesBelow (Nat.floor z' + 1), Submission.ASP.FIgtil p)
        ≤ Real.log (Real.log z') + c + C1 * errB := by
      have hfin : (Finset.Icc 1 (Nat.floor z')).filter Nat.Prime
          = Nat.primesBelow (Nat.floor z' + 1) := by
        rw [← Nat.primesLE_eq_filter_Icc_one]
        rfl
      have h := h19 (Nat.floor z') hN2
      rw [hfin] at h
      have hupper := (abs_le.mp h).2
      have hll := log_log_floor_le z' hz'2
      have herr := err_le_errB (Nat.floor z') hN2
      have hCB : C1 * ((Real.log ((Nat.floor z' : ℕ) : ℝ)) ^ (-(10 : ℝ))
            + 1 / ((Nat.floor z' : ℕ) : ℝ)) ≤ C1 * errB :=
        mul_le_mul_of_nonneg_left herr hC1nn
      linarith
    by_cases hw3 : (3 : ℝ) ≤ w
    · -- Case `w ≥ 3`: use (1.9) at `y = ⌊w⌋ - 1` for the lower bound of `A(⌊w⌋)`
      have hm3 : 3 ≤ Nat.floor w := Nat.le_floor hw3
      have hmm1 : 2 ≤ Nat.floor w - 1 := by omega
      have hAm : Real.log (Real.log ((Nat.floor w - 1 : ℕ) : ℝ)) + c - C1 * errB
          ≤ ∑ p ∈ Nat.primesBelow (Nat.floor w), Submission.ASP.FIgtil p := by
        have hfin : (Finset.Icc 1 (Nat.floor w - 1)).filter Nat.Prime
            = Nat.primesBelow (Nat.floor w) := by
          rw [← Nat.primesLE_eq_filter_Icc_one, ← Nat.primesBelow_eq_primesLE_sub_one]
        have h := h19 (Nat.floor w - 1) hmm1
        rw [hfin] at h
        have hlow := (abs_le.mp h).1
        have herr := err_le_errB (Nat.floor w - 1) hmm1
        have hCB : C1 * ((Real.log ((Nat.floor w - 1 : ℕ) : ℝ)) ^ (-(10 : ℝ))
              + 1 / ((Nat.floor w - 1 : ℕ) : ℝ)) ≤ C1 * errB :=
          mul_le_mul_of_nonneg_left herr hC1nn
        linarith
      have hll' := log_log_sub_two_le w hw3
      have hfin : Real.log (Real.log z') - Real.log (Real.log w) + (2 + 2 * (C1 * errB))
          ≤ Real.log (Real.log z') - Real.log (Real.log w)
            + max (c + C1 * errB + 1) (2 + 2 * (C1 * errB)) := by
        linarith [le_max_right (c + C1 * errB + 1) (2 + 2 * (C1 * errB))]
      calc (∑ p ∈ (Nat.primesBelow Δ).filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), Submission.ASP.FIgtil p)
          ≤ (∑ p ∈ Nat.primesBelow (Nat.floor z' + 1), Submission.ASP.FIgtil p)
            - ∑ p ∈ Nat.primesBelow (Nat.floor w), Submission.ASP.FIgtil p := by
            rw [hsdiff] at hS_le; exact hS_le
        _ ≤ Real.log (Real.log z') - Real.log (Real.log w) + (2 + 2 * (C1 * errB)) := by
            linarith
        _ ≤ Real.log (Real.log z') - Real.log (Real.log w)
              + max (c + C1 * errB + 1) (2 + 2 * (C1 * errB)) := hfin
    · -- Case `2 ≤ w < 3`: `A(⌊w⌋) ≥ 0`, and `log log w ≤ 1`
      have hw3' : w < 3 := not_le.mp hw3
      have hAm : 0 ≤ ∑ p ∈ Nat.primesBelow (Nat.floor w), Submission.ASP.FIgtil p :=
        Finset.sum_nonneg (fun p _ => Submission.ASP.FIgtil_nonneg p)
      have hlw := log_log_le_one w hw hw3'
      have hfin : Real.log (Real.log z') + c + C1 * errB
          ≤ Real.log (Real.log z') - Real.log (Real.log w)
            + max (c + C1 * errB + 1) (2 + 2 * (C1 * errB)) := by
        have h1 : c + C1 * errB + 1 ≤ max (c + C1 * errB + 1) (2 + 2 * (C1 * errB)) :=
          le_max_left _ _
        linarith
      calc (∑ p ∈ (Nat.primesBelow Δ).filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), Submission.ASP.FIgtil p)
          ≤ (∑ p ∈ Nat.primesBelow (Nat.floor z' + 1), Submission.ASP.FIgtil p)
            - ∑ p ∈ Nat.primesBelow (Nat.floor w), Submission.ASP.FIgtil p := by
            rw [hsdiff] at hS_le; exact hS_le
        _ ≤ Real.log (Real.log z') + c + C1 * errB := by linarith
        _ ≤ Real.log (Real.log z') - Real.log (Real.log w)
              + max (c + C1 * errB + 1) (2 + 2 * (C1 * errB)) := by linarith

end

end Work.FIChain
