import Submission.Contracts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Asymptotic lemma for the final assembly (Smith's proof of Thm main, adjust.tex)

The assembly needs, for every fixed `C0 > 0` and `C1 > 3`, all sufficiently
large integers `n` to satisfy the "main inequalities":

    n > C1,   2 ≤ n − m,   m ≤ n,   4·n^{C0 + C0√n} < n^{−C1}·κ^{m}

with `m = ⌊B·√n·log n⌋`, `B = 2·C0/log κ`,  κ = (bSerre − aSerre)/4 > 1.
(Paper eq:main_n_ass, with m = ⌊B√n log n⌋.)
-/

noncomputable section

open Filter
open scoped Real Topology

namespace Submission.Asymptotics

open Submission.Contracts

/-- `Real.log (n : ℝ)` tends to `+∞` along the naturals. -/
lemma tendsto_log_nat_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `Real.sqrt (n : ℝ)` tends to `+∞` along the naturals. -/
lemma tendsto_sqrt_nat_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- For every fixed real `c`, all sufficiently large naturals satisfy `c < n`. -/
lemma eventually_gt_nat_of_real (c : ℝ) : ∀ᶠ n : ℕ in atTop, (c : ℝ) < (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt c
  rw [eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn
  exact lt_of_lt_of_le hN (by exact_mod_cast hn)

/-- For every fixed real `b`, eventually `b ≤ Real.log (n : ℝ)`. -/
lemma eventually_log_ge (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ Real.log (n : ℝ) := by
  have h := tendsto_log_nat_atTop.eventually_gt_atTop b
  filter_upwards [h] with n hn
  exact le_of_lt hn

/-- For every fixed real `b`, eventually `b ≤ Real.sqrt (n : ℝ)`. -/
lemma eventually_sqrt_ge (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ Real.sqrt (n : ℝ) := by
  have h := tendsto_sqrt_nat_atTop.eventually_gt_atTop b
  filter_upwards [h] with n hn
  exact le_of_lt hn

/-- `log n` grows slower than any fixed positive multiple of `√n`. -/
lemma eventually_log_le_sqrt_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * Real.sqrt (n : ℝ) := by
  have hlittle : Real.log =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)
  have hc2 : 0 < c / 2 := div_pos hc (by norm_num)
  have hb : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (c / 2) * ‖x ^ (1 / 2 : ℝ)‖ :=
    Asymptotics.IsLittleO.bound hlittle hc2
  have hx1 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop (1 : ℝ)
  have hre : ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * Real.sqrt x := by
    filter_upwards [hb, hx1] with x hnorm hx1'
    have hx0 : 0 ≤ x := by linarith
    have hxpow : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
    calc
      Real.log x ≤ ‖Real.log x‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ (c / 2) * ‖x ^ (1 / 2 : ℝ)‖ := hnorm
      _ = (c / 2) * x ^ (1 / 2 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hxpow]
      _ ≤ c * x ^ (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by linarith : c / 2 ≤ c) hxpow
      _ = c * Real.sqrt x := by rw [Real.sqrt_eq_rpow]
  exact tendsto_natCast_atTop_atTop.eventually hre

/-- The floor `mFloor B n` is eventually bounded by `n - 2`. -/
lemma eventually_mFloor_le_sub_two (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, mFloor B n ≤ n - 2 := by
  have hlog := eventually_log_le_sqrt_mul (c := 1 / (2 * B)) (by positivity)
  have h4 : ∀ᶠ n : ℕ in atTop, (4 : ℕ) ≤ n := eventually_ge_atTop (4 : ℕ)
  filter_upwards [hlog, h4] with n hlb hn4
  have h2n : 2 ≤ n := by exact le_trans (by norm_num : (2 : ℕ) ≤ (4 : ℕ)) hn4
  have hx4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hx0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    calc Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (Real.sqrt (n : ℝ)) ^ 2 := by ring
    _ = (n : ℝ) := Real.sq_sqrt hx0
  have hBB : B * (1 / (2 * B)) = 1 / 2 := by
    field_simp [hB.ne']
  have hu : B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) / 2 := by
    calc
      B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
          ≤ B * Real.sqrt (n : ℝ) * ((1 / (2 * B)) * Real.sqrt (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hlb (mul_nonneg hB.le (Real.sqrt_nonneg (n : ℝ)))
      _ = (1 / 2) * (n : ℝ) := by
        calc B * Real.sqrt (n : ℝ) * ((1 / (2 * B)) * Real.sqrt (n : ℝ))
            = (B * (1 / (2 * B))) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = (1 / 2) * (n : ℝ) := by rw [hBB, hsq]
      _ = (n : ℝ) / 2 := by ring
  have hu2 : (n : ℝ) / 2 ≤ (n : ℝ) - 2 := by linarith
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub h2n]
    norm_num
  have hub : B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by
    rw [hcast]
    exact le_trans hu hu2
  simpa [mFloor] using (Nat.floor_le_of_le hub)

/-- For `B > 0` the floor `mFloor B n` is eventually at least 1. -/
lemma eventually_mFloor_ge_one (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ mFloor B n := by
  have hsqrt : ∀ᶠ n : ℕ in atTop, (1 / B) ≤ Real.sqrt (n : ℝ) := eventually_sqrt_ge (1 / B)
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) := eventually_log_ge 1
  filter_upwards [hsqrt, hlog] with n hsq hlg
  have hx : (1 : ℝ) ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (1 : ℝ) = B * (1 / B) := by field_simp [hB.ne']
      _ ≤ B * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hsq (le_of_lt hB)
      _ ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
        have hpos : 0 ≤ B * Real.sqrt (n : ℝ) := mul_nonneg (le_of_lt hB) (Real.sqrt_nonneg _)
        simpa using (mul_le_mul_of_nonneg_left hlg hpos)
  unfold mFloor
  exact Nat.le_floor (a := B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) (by simpa using hx)

/-- The core asymptotic inequality used by the main estimate: for every
`0 < C0` and `C1`, eventually
`log 4 + (C0 + C0·√n + C1)·log n + log κ < 2·C0·√n·log n`. -/
lemma eventually_core (C0 C1 : ℝ) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      Real.log 4 + (C0 + C0 * Real.sqrt (n : ℝ) + C1) * Real.log (n : ℝ) +
          Real.log kappa <
        2 * C0 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  let K : ℝ := Real.log 4 + Real.log kappa + 1
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < (4 : ℝ))
  have hκ1 : 1 < kappa := kappa_gt_one
  have hlogk : 0 < Real.log kappa := Real.log_pos hκ1
  have hKpos : 0 < K := by
    dsimp [K]
    linarith
  let A : ℝ := max (2 * (C0 + C1) / C0) (2 * K / C0)
  have hsA := eventually_sqrt_ge A
  have hl1 := eventually_log_ge 1
  filter_upwards [hsA, hl1] with n hsA' hl1'
  let s := Real.sqrt (n : ℝ)
  let l := Real.log (n : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg (n : ℝ)
  have h1 : 2 * (C0 + C1) / C0 ≤ s := by
    dsimp [A] at hsA'
    exact le_trans (le_max_left (2 * (C0 + C1) / C0) (2 * K / C0)) hsA'
  have h2 : 2 * K / C0 ≤ s := by
    dsimp [A] at hsA'
    exact le_trans (le_max_right (2 * (C0 + C1) / C0) (2 * K / C0)) hsA'
  have hfoo : 2 * (C0 + C1) = C0 * (2 * (C0 + C1) / C0) := by
    field_simp [hC0.ne']
  have hc1 : C0 * s ≥ 2 * (C0 + C1) := by
    calc 2 * (C0 + C1) = C0 * (2 * (C0 + C1) / C0) := hfoo
    _ ≤ C0 * s := mul_le_mul_of_nonneg_left h1 hC0.le
  have hc2 : (C0 / 2) * s ≥ K := by
    have hmul : C0 * (2 * K / C0) ≤ C0 * s := mul_le_mul_of_nonneg_left h2 hC0.le
    have hc0 : C0 * (2 * K / C0) = 2 * K := by
      field_simp [hC0.ne']
    nlinarith
  have hstuff : C0 * s - C0 - C1 ≥ (C0 / 2) * s := by
    nlinarith [hc1]
  have hs2 : 0 ≤ (C0 / 2) * s := by
    exact mul_nonneg (by linarith : (0 : ℝ) ≤ C0 / 2) hs0
  have hstuff0 : 0 ≤ C0 * s - C0 - C1 := by linarith
  have hmain : (C0 * s - C0 - C1) * l ≥ K := by
    have hmul1 : 1 * (C0 * s - C0 - C1) ≤ l * (C0 * s - C0 - C1) :=
      mul_le_mul_of_nonneg_right hl1' hstuff0
    nlinarith [hmul1, hstuff, hc2, hKpos]
  have hK' : Real.log 4 + Real.log kappa < K := by
    dsimp [K]
    linarith
  have hgt : Real.log 4 + Real.log kappa < (C0 * s - C0 - C1) * l :=
    lt_of_lt_of_le hK' hmain
  change Real.log 4 + (C0 + C0 * s + C1) * l + Real.log kappa < 2 * C0 * s * l
  nlinarith

/-- The main estimate: eventually
`4·n^{C0 + C0√n} < n^{−C1}·κ^{⌊B√n log n⌋}`, with `B = 2C0/log κ`. -/
lemma eventually_main_inequality (C0 C1 B : ℝ) (hC0 : 0 < C0)
    (hBdef : B = (2 * C0) / Real.log kappa) :
    ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) <
        (n : ℝ) ^ (-C1) * kappa ^ mFloor B n := by
  have hκ1 : 1 < kappa := kappa_gt_one
  have hκpos : 0 < kappa := lt_trans zero_lt_one hκ1
  have hlogk : 0 < Real.log kappa := Real.log_pos hκ1
  have hBmul : B * Real.log kappa = 2 * C0 := by
    rw [hBdef]
    field_simp [hlogk.ne']
  have hcore := eventually_core C0 C1 hC0
  have hx2 : ∀ᶠ n : ℕ in atTop, (2 : ℕ) ≤ n := eventually_ge_atTop (2 : ℕ)
  filter_upwards [hcore, hx2] with n hc hn2
  have h2x : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxpos : (0 : ℝ) < (n : ℝ) := by linarith
  let m := mFloor B n
  have hfl : B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) < (m : ℝ) + 1 := by
    dsimp [m]
    simpa [mFloor] using (Nat.lt_floor_add_one (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)))
  have heq : (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) * Real.log kappa
      = 2 * C0 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) * Real.log kappa
          = (B * Real.log kappa) * (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) := by ring
      _ = (2 * C0) * (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) := by rw [hBmul]
      _ = 2 * C0 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by ring
  have hc1 : Real.log 4 + (C0 + C0 * Real.sqrt (n : ℝ) + C1) * Real.log (n : ℝ) + Real.log kappa
      < (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) * Real.log kappa := by
    rw [← heq] at hc
    exact hc
  have hu_le : (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) * Real.log kappa
      ≤ ((m : ℝ) + 1) * Real.log kappa := by
    exact mul_le_mul_of_nonneg_right (le_of_lt hfl) hlogk.le
  have hlt : Real.log 4 + (C0 + C0 * Real.sqrt (n : ℝ) + C1) * Real.log (n : ℝ) + Real.log kappa
      < ((m : ℝ) + 1) * Real.log kappa := lt_of_lt_of_le hc1 hu_le
  have harg : Real.log 4 + (C0 + C0 * Real.sqrt (n : ℝ)) * Real.log (n : ℝ) <
      (-C1) * Real.log (n : ℝ) + (m : ℝ) * Real.log kappa := by
    nlinarith
  have hposL : 0 < 4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) := by
    exact mul_pos (by norm_num : (0 : ℝ) < 4) (Real.rpow_pos_of_pos hxpos _)
  have hposR : 0 < (n : ℝ) ^ (-C1) * kappa ^ m := by
    exact mul_pos (Real.rpow_pos_of_pos hxpos _) (pow_pos hκpos m)
  refine (Real.log_lt_log_iff hposL hposR).1 ?_
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt (Real.rpow_pos_of_pos hxpos _)),
    Real.log_rpow hxpos]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (pow_ne_zero m hκpos.ne'),
    Real.log_rpow hxpos, Real.log_pow]
  exact harg

/-- For every `0 < C0` and `3 < C1` there is `N0 ≥ 1` such that the main
inequalities of the final assembly hold for every `n ≥ N0`. -/
theorem exists_good_n {C0 C1 : ℝ} (hC0 : 0 < C0) (hC1 : 3 < C1) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ n : ℕ, N0 ≤ n →
        let m := mFloor ((2 * C0) / Real.log kappa) n
        2 ≤ n - m ∧ m ≤ n ∧
        (C1 : ℝ) < n ∧
        4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) <
          (n : ℝ) ^ (-C1) * kappa ^ m ∧ 1 ≤ mFloor ((2 * C0) / Real.log kappa) n := by
  let B : ℝ := (2 * C0) / Real.log kappa
  have hκ1 : 1 < kappa := kappa_gt_one
  have hlogk : 0 < Real.log kappa := Real.log_pos hκ1
  have hB : 0 < B := by
    dsimp [B]
    exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hC0) hlogk
  have evsmall : ∀ᶠ n : ℕ in atTop, mFloor B n ≤ n - 2 :=
    eventually_mFloor_le_sub_two B hB
  have evgt : ∀ᶠ n : ℕ in atTop, (C1 : ℝ) < (n : ℝ) := eventually_gt_nat_of_real C1
  have evmain : ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) <
        (n : ℝ) ^ (-C1) * kappa ^ mFloor B n :=
    eventually_main_inequality C0 C1 B hC0 (by dsimp [B])
  have h4n : ∀ᶠ n : ℕ in atTop, (4 : ℕ) ≤ n := eventually_ge_atTop (4 : ℕ)
  have evgeOne : ∀ᶠ n : ℕ in atTop, 1 ≤ mFloor B n := eventually_mFloor_ge_one B hB
  have evall : ∀ᶠ n : ℕ in atTop,
      let m := mFloor B n
      2 ≤ n - m ∧ m ≤ n ∧ (C1 : ℝ) < n ∧
        4 * (n : ℝ) ^ (C0 + C0 * Real.sqrt (n : ℝ)) <
          (n : ℝ) ^ (-C1) * kappa ^ m ∧ 1 ≤ mFloor B n := by
    filter_upwards [evsmall, evgt, evmain, h4n, evgeOne] with n hmsmall hgt hmain hn4 hge1
    have hmle : mFloor B n ≤ n := by
      exact le_trans hmsmall (Nat.sub_le n 2)
    have h2n : 2 ≤ n := le_trans (by norm_num : (2 : ℕ) ≤ (4 : ℕ)) hn4
    have hsum : mFloor B n + (n - mFloor B n) = n := Nat.add_sub_of_le hmle
    have hmle2 : mFloor B n + 2 ≤ n := by
      calc mFloor B n + 2 ≤ (n - 2) + 2 := Nat.add_le_add_right hmsmall 2
      _ = n := Nat.sub_add_cancel h2n
    have hleft : 2 ≤ n - mFloor B n := by
      have hleft' : mFloor B n + 2 ≤ mFloor B n + (n - mFloor B n) := by
        simpa [hsum] using hmle2
      exact (add_le_add_iff_left (mFloor B n)).1 hleft'
    exact ⟨hleft, hmle, hgt, hmain, hge1⟩
  rcases (eventually_atTop.mp evall) with ⟨N, hN⟩
  refine ⟨max N 1, le_max_right N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  simpa [B] using (hN n hnN)

end Submission.Asymptotics
