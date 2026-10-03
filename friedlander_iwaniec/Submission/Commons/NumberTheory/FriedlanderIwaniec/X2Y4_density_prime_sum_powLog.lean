import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_primeRecips_sub_const_powLog
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset Filter

namespace Commons.NumberTheory.FriedlanderIwaniec

noncomputable section

/-- The real-valued character `χ₄` written through `chi4Fun`. -/
private def c4r (n : ℕ) : ℝ := (Commons.NumberTheory.DirichletCharacter.chi4Fun ((n : ℕ) : ZMod 4)).re

/-- `c4r` agrees with the target's `((ZMod.χ₄ ... : ℤ) : ℝ)`. -/
private lemma c4r_eq (n : ℕ) : c4r n = ((ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) : ℝ) := by
  rw [c4r, Commons.NumberTheory.DirichletCharacter.chi4Fun_eq_zmod]
  simp

/-- `|c4r n| ≤ 1`. -/
private lemma abs_c4r_le_one (n : ℕ) : |c4r n| ≤ 1 := by
  rw [c4r]
  rcases Commons.NumberTheory.DirichletCharacter.zmod_four_eq ((n : ℕ) : ZMod 4) with h | h | h | h <;>
    rw [h] <;> simp [Commons.NumberTheory.DirichletCharacter.chi4Fun_zero,
      Commons.NumberTheory.DirichletCharacter.chi4Fun_one,
      Commons.NumberTheory.DirichletCharacter.chi4Fun_two,
      Commons.NumberTheory.DirichletCharacter.chi4Fun_three]

/-- `primesLE` as a filtered range. -/
private lemma primesLE_eq (n : ℕ) : n.primesLE = (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  simp [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_range]

/-- **Log-power domination of `1/y`.**  For every `A > 0` there is `C > 0` with
`1/y ≤ C / (log y)^A` for all `y ≥ 2`. -/
private lemma inv_le_const_div_log_rpow (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y → 1 / y ≤ C / (Real.log y) ^ A := by
  set φ : ℝ → ℝ := fun y => (Real.log y) ^ A / y with hφdef
  have htend : Tendsto (fun y : ℝ => (Real.log y) ^ A / y) atTop (nhds 0) := by
    have h1 : Tendsto (fun u : ℝ => u ^ A * Real.exp (-(1 : ℝ) * u)) atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A 1 zero_lt_one
    have h2 : Tendsto (fun y : ℝ => (Real.log y) ^ A * Real.exp (-(1 : ℝ) * Real.log y))
        atTop (nhds 0) := h1.comp Real.tendsto_log_atTop
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [neg_mul, one_mul, Real.exp_neg, Real.exp_log hy, div_eq_mul_inv]
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (htend.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  set Y : ℝ := max Y₀ 2 with hYdef
  have hY2 : (2 : ℝ) ≤ Y := le_max_right _ _
  have hY₀Y : Y₀ ≤ Y := le_max_left _ _
  have hcont : ContinuousOn φ (Set.Icc 2 Y) := by
    rw [hφdef]
    apply ContinuousOn.div
    · refine ContinuousOn.rpow_const ?_ ?_
      · refine Real.continuousOn_log.mono ?_
        intro y hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (by linarith [hy.1])
      · intro y hy
        left
        exact ne_of_gt (Real.log_pos (by linarith [hy.1]))
    · exact continuousOn_id
    · intro y hy
      exact ne_of_gt (by linarith [hy.1])
  obtain ⟨b, hb⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max b 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro y hy
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogpowpos : 0 < (Real.log y) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hφb : φ y ≤ max b 1 := by
    by_cases hyY : y ≤ Y
    · have hmem : y ∈ Set.Icc 2 Y := ⟨hy, hyY⟩
      have : φ y ∈ φ '' Set.Icc 2 Y := ⟨y, hmem, rfl⟩
      exact le_trans (hb this) (le_max_left _ _)
    · have hYy : Y ≤ y := le_of_lt (not_le.mp hyY)
      have h1 : (Real.log y) ^ A / y ≤ 1 := hY₀ y (le_trans hY₀Y hYy)
      rw [hφdef]
      exact le_trans h1 (le_max_right _ _)
  rw [hφdef] at hφb
  have hypos : 0 < y := by linarith
  rw [div_le_iff₀ hypos] at hφb
  rw [div_le_iff₀ hypos, div_mul_eq_mul_div, le_div_iff₀ hlogpowpos]
  simpa using hφb

/-- **Tail of `∑ 1/n²`.**  `∑_{k≥0} 1/(k+M)² ≤ 2/M` for `M ≥ 1`. -/
private lemma tsum_inv_sq_nat_add_le (M : ℕ) (hM : 1 ≤ M) :
    (∑' k : ℕ, (1 : ℝ) / ((k + M : ℕ) : ℝ) ^ 2) ≤ 2 / (M : ℝ) := by
  have hg : Summable (fun k : ℕ => (1 : ℝ) / ((k + M : ℕ) : ℝ) ^ 2) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    exact (summable_nat_add_iff M).mpr hbase
  refine le_of_tendsto_of_tendsto' hg.hasSum.tendsto_sum_nat tendsto_const_nhds ?_
  intro n
  have hre : (∑ k ∈ Finset.range n, (1 : ℝ) / ((k + M : ℕ) : ℝ) ^ 2)
      = ∑ i ∈ Finset.Ico M (M + n), (1 : ℝ) / ((i : ℕ) : ℝ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm]
  rw [hre]
  have hsub : Finset.Ico M (M + n) ⊆ Finset.Ioo (M - 1) (M + n) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_Ioo]
    omega
  have hle : (∑ i ∈ Finset.Ico M (M + n), (1 : ℝ) / ((i : ℕ) : ℝ) ^ 2)
      ≤ ∑ i ∈ Finset.Ioo (M - 1) (M + n), (1 : ℝ) / ((i : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    positivity
  refine le_trans hle ?_
  have h2 := sum_Ioo_inv_sq_le (α := ℝ) (M - 1) (M + n)
  have hcast : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
    norm_cast
    omega
  rw [hcast] at h2
  refine le_trans ?_ h2
  apply Finset.sum_le_sum
  intro i _
  rw [one_div]

/-- **Fixed limit from `A`-dependent limits.** -/
private lemma exists_fixed_limit_of_powLog_rate {F : ℝ → ℝ} {Y : ℝ} (hY : 1 < Y)
    (hrate : ∀ A : ℝ, 0 < A → ∃ L C : ℝ, 0 < C ∧ ∀ y : ℝ, Y ≤ y → |F y - L| ≤ C / (Real.log y) ^ A) :
    ∃ L : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, Y ≤ y → |F y - L| ≤ C / (Real.log y) ^ A := by
  obtain ⟨L₀, C₀, hC₀pos, hC₀⟩ := hrate 1 one_pos
  refine ⟨L₀, fun A hA => ?_⟩
  obtain ⟨LA, CA, hCApos, hCA⟩ := hrate A hA
  have hLAeq : LA = L₀ := by
    have hev : ∀ᶠ y : ℝ in atTop, |LA - L₀| ≤ CA / (Real.log y) ^ A + C₀ / Real.log y := by
      filter_upwards [eventually_ge_atTop Y] with y hy
      have h1 := hCA y hy
      have h2' : |F y - L₀| ≤ C₀ / Real.log y := by simpa using hC₀ y hy
      calc |LA - L₀| ≤ |LA - F y| + |F y - L₀| := by
            rw [show LA - L₀ = (LA - F y) + (F y - L₀) by ring]
            exact abs_add_le _ _
        _ = |F y - LA| + |F y - L₀| := by rw [abs_sub_comm LA (F y)]
        _ ≤ CA / (Real.log y) ^ A + C₀ / Real.log y := add_le_add h1 h2'
    have hg : Tendsto (fun y : ℝ => CA / (Real.log y) ^ A + C₀ / Real.log y) atTop (nhds 0) := by
      have h1 : Tendsto (fun y : ℝ => (Real.log y) ^ A) atTop atTop :=
        (tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop
      have h2 : Tendsto (fun y : ℝ => CA / (Real.log y) ^ A) atTop (nhds 0) :=
        Tendsto.const_div_atTop h1 CA
      have h3 : Tendsto (fun y : ℝ => C₀ / Real.log y) atTop (nhds 0) :=
        Tendsto.const_div_atTop Real.tendsto_log_atTop C₀
      simpa using h2.add h3
    have hle : |LA - L₀| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hg hev
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
  refine ⟨CA, hCApos, fun y hy => ?_⟩
  rw [hLAeq] at hCA
  exact hCA y hy

/-- **Extend the prime-reciprocal power-log rate to `x ≥ 2`.** -/
private lemma primeRecips_rate_ge_two :
    ∀ A : ℝ, 0 < A → ∃ L C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x) - L| ≤
        C / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨L, C₁, hC₁pos, hC₁⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog A hA
  have hRnn : ∀ x : ℝ, 0 ≤ (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) := by
    intro x
    apply Finset.sum_nonneg
    intro p hp
    positivity
  have hRle : ∀ x : ℝ, x < 12 → (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) ≤ 12 := by
    intro x hx12
    have hcard : ((⌊x⌋₊).primesLE).card ≤ 12 := by
      have hsub : (⌊x⌋₊).primesLE ⊆ Finset.range (⌊x⌋₊ + 1) := by
        intro p hp
        rw [primesLE_eq] at hp
        exact (Finset.mem_filter.mp hp).1
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_range] at h1
      have h2 : ⌊x⌋₊ < 12 := (Nat.floor_lt' (by norm_num : (12 : ℕ) ≠ 0)).mpr hx12
      omega
    calc (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [primesLE_eq] at hp
          have hpp : p.Prime := (Finset.mem_filter.mp hp).2
          rw [div_le_one (by exact_mod_cast hpp.pos)]
          exact_mod_cast hpp.one_le
      _ = (((⌊x⌋₊).primesLE).card : ℝ) := by simp
      _ ≤ 12 := by exact_mod_cast hcard
  have hloglog : ∀ x : ℝ, 2 ≤ x → x ≤ 11 → |Real.log (Real.log x)| ≤ 9 := by
    intro x hx2 hx11
    have hxpos : 0 < x := by linarith
    have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogxle : Real.log x ≤ 10 := by
      have := Real.log_le_sub_one_of_pos hxpos
      linarith
    have hlogxge : (1 : ℝ) / 2 ≤ Real.log x := by
      have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
      linarith [Real.log_two_gt_d9]
    have hupper : Real.log (Real.log x) ≤ 9 := by
      have h : Real.log (Real.log x) ≤ Real.log 10 := Real.log_le_log hlogxpos hlogxle
      have h10 : Real.log 10 ≤ 9 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
        linarith
      linarith
    have hlower : -9 ≤ Real.log (Real.log x) := by
      have h : Real.log ((1 : ℝ) / 2) ≤ Real.log (Real.log x) :=
        Real.log_le_log (by norm_num) hlogxge
      have h12 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      have hlog2le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      rw [h12] at h
      linarith
    rw [abs_le]
    exact ⟨hlower, hupper⟩
  have hpow11 : (1 : ℝ) ≤ (Real.log 11) ^ A := by
    refine Real.one_le_rpow ?_ (le_of_lt hA)
    have hexp : Real.exp 1 < 11 := lt_trans Real.exp_one_lt_three (by norm_num)
    exact le_of_lt ((Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 11)).mpr hexp)
  have hS11 : |(∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11)| ≤ 21 := by
    have h1 : |(∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ))| ≤ 12 := by
      rw [abs_of_nonneg (hRnn 11)]
      exact hRle 11 (by norm_num)
    have h2 : |Real.log (Real.log (11 : ℝ))| ≤ 9 := hloglog 11 (by norm_num) (by norm_num)
    have h := abs_sub_le ((∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ))) 0
      (Real.log (Real.log (11 : ℝ)))
    rw [sub_zero, zero_sub, abs_neg] at h
    linarith
  have hLbound : |L| ≤ 21 + C₁ := by
    have h11 := hC₁ 11 (by norm_num)
    have h11' : |(∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11) - L|
        ≤ C₁ := by
      refine le_trans h11 ?_
      rw [div_le_iff₀ (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) A)]
      have : C₁ * 1 ≤ C₁ * (Real.log 11) ^ A :=
        mul_le_mul_of_nonneg_left hpow11 hC₁pos.le
      linarith
    have htri : |L| ≤
        |(∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11)|
          + |(∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11) - L| := by
      have h := abs_sub_le ((∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11)) 0
        ((∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11) - L)
      rw [sub_zero, zero_sub, abs_neg] at h
      have hsub : (∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11)
          - ((∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log 11) - L) = L := by
        ring
      rwa [hsub] at h
    linarith
  refine ⟨L, max C₁ ((42 + C₁) * (Real.log 11) ^ A), ?_, ?_⟩
  · exact lt_of_lt_of_le hC₁pos (le_max_left _ _)
  · intro x hx2
    by_cases hx11 : 11 ≤ x
    · have h := hC₁ x hx11
      refine le_trans h ?_
      refine div_le_div_of_nonneg_right (le_max_left _ _) ?_
      exact le_of_lt (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A)
    · have hxlt : x < 11 := not_le.mp hx11
      have hcrude : |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x) - L|
          ≤ 42 + C₁ := by
        have h1 : |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ))| ≤ 12 := by
          rw [abs_of_nonneg (hRnn x)]
          exact hRle x (by linarith)
        have h2 : |Real.log (Real.log x)| ≤ 9 := hloglog x hx2 (le_of_lt hxlt)
        have h3 : |((∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ))) - Real.log (Real.log x)| ≤ 21 := by
          have h := abs_sub_le ((∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ))) 0 (Real.log (Real.log x))
          rw [sub_zero, zero_sub, abs_neg] at h
          linarith
        have h4 : |((∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ))) - Real.log (Real.log x) - L| ≤ 21 + |L| := by
          have h := abs_sub_le (((∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ))) - Real.log (Real.log x)) 0 L
          rw [sub_zero, zero_sub, abs_neg] at h
          linarith
        linarith [h4, hLbound]
      refine le_trans hcrude ?_
      have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hpowxpos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogxpos A
      have hpowle : (Real.log x) ^ A ≤ (Real.log 11) ^ A :=
        Real.rpow_le_rpow (le_of_lt hlogxpos) (Real.log_le_log (by linarith) (le_of_lt hxlt)) (le_of_lt hA)
      rw [le_div_iff₀ hpowxpos]
      calc (42 + C₁) * (Real.log x) ^ A ≤ (42 + C₁) * (Real.log 11) ^ A :=
            mul_le_mul_of_nonneg_left hpowle (by linarith)
        _ ≤ max C₁ ((42 + C₁) * (Real.log 11) ^ A) := le_max_right _ _

/-- The summand equivalence for the target: `(1+χ)/p - χ/p² = 1/p + χ/p - χ/p²`. -/
private lemma target_sum_eq (y : ℝ) :
    (∑ p ∈ (⌊y⌋₊).primesLE,
        ((1 + ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ)) / (p : ℝ)
          - ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) ^ 2))
      = (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
        + (∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ))
        - (∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ) ^ 2) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [c4r_eq p]
  ring

/-! ### The `χ(p)/p²` contribution -/

private def fZ (n : ℕ) : ℝ := if n.Prime then c4r n / (n : ℝ) ^ 2 else 0

private lemma fZ_abs_le (n : ℕ) : ‖fZ n‖ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
  rw [Real.norm_eq_abs, fZ]
  split_ifs with hp
  · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    exact div_le_div_of_nonneg_right (abs_c4r_le_one n) (by positivity)
  · rw [abs_zero]; positivity

private lemma fZ_summable : Summable fZ :=
  Summable.of_norm_bounded ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)) fZ_abs_le

private def LZ : ℝ := ∑' n : ℕ, fZ n

private lemma Zc_eq_range (y : ℝ) :
    (∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ) ^ 2)
      = ∑ n ∈ Finset.range (⌊y⌋₊ + 1), fZ n := by
  rw [primesLE_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime <;> simp [fZ, hp]

private lemma Zc_rate :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ) ^ 2) - LZ| ≤ C / (Real.log y) ^ A := by
  intro A hA
  obtain ⟨C₂, hC₂pos, hC₂⟩ := inv_le_const_div_log_rpow A hA
  refine ⟨4 * C₂, by positivity, ?_⟩
  intro y hy
  rw [Zc_eq_range y]
  set N : ℕ := ⌊y⌋₊ with hNdef
  have hN2 : 2 ≤ N := Nat.le_floor hy
  have hM1 : 1 ≤ N + 1 := by omega
  have hsplit : (∑ n ∈ Finset.range (N + 1), fZ n) - LZ = -∑' k : ℕ, fZ (k + (N + 1)) := by
    have h := Summable.sum_add_tsum_nat_add (N + 1) fZ_summable
    rw [show LZ = ∑' n : ℕ, fZ n from rfl]
    linarith
  rw [hsplit, abs_neg]
  have hnorm : |∑' k : ℕ, fZ (k + (N + 1))| ≤ ∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2 := by
    have hsumm : Summable (fun k : ℕ => fZ (k + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr fZ_summable
    have hsumm2 : Summable (fun k : ℕ => ‖fZ (k + (N + 1))‖) := hsumm.norm
    have hsumm3 : Summable (fun k : ℕ => (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff (N + 1)).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
    calc |∑' k : ℕ, fZ (k + (N + 1))| = ‖∑' k : ℕ, fZ (k + (N + 1))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' k : ℕ, ‖fZ (k + (N + 1))‖ := norm_tsum_le_tsum_norm hsumm2
      _ ≤ ∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2 :=
          Summable.tsum_le_tsum (fun k => fZ_abs_le (k + (N + 1))) hsumm2 hsumm3
  refine le_trans hnorm ?_
  have hb1 : (∑' k : ℕ, (1 : ℝ) / ((k + (N + 1) : ℕ) : ℝ) ^ 2) ≤ 2 / ((N + 1 : ℕ) : ℝ) :=
    tsum_inv_sq_nat_add_le (N + 1) hM1
  have hb2 : 2 / ((N + 1 : ℕ) : ℝ) ≤ 2 / (N : ℝ) := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    apply div_le_div_of_nonneg_left (by norm_num) hNpos
    exact_mod_cast (by omega : N ≤ N + 1)
  have hhalf : (y / 2 : ℝ) ≤ (N : ℝ) := by
    have hlt : y < (N : ℝ) + 1 := Nat.lt_floor_add_one y
    have hy2 : (2 : ℝ) ≤ y := hy
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hypos : 0 < y := by linarith
  have hb3 : 2 / (N : ℝ) ≤ 4 / y := by
    rw [div_le_div_iff₀ hNpos hypos]
    linarith [hhalf]
  have hb4 : 4 / y ≤ 4 * C₂ / (Real.log y) ^ A := by
    have h := hC₂ y hy
    have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
    have hpowpos : 0 < (Real.log y) ^ A := Real.rpow_pos_of_pos hlogpos A
    rw [div_le_div_iff₀ hypos hpowpos] at h
    rw [div_le_div_iff₀ hypos hpowpos]
    nlinarith [h]
  exact le_trans hb1 (le_trans hb2 (le_trans hb3 hb4))

/-- Auxiliary form of the main theorem, stated with an explicit parenthesis around the
summand (so that it parses under the standard big-operator notation). -/
private theorem X2Y4_density_prep :
    ∃ c : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE,
          ((1 + ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ)) / (p : ℝ)
            - ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) ^ 2))
        - (Real.log (Real.log y) + c)| ≤ C / (Real.log y) ^ A := by
  have hXrate : ∀ A : ℝ, 0 < A → ∃ L C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ (⌊x⌋₊).primesLE, c4r p / (p : ℝ)) - L| ≤ C / (Real.log x) ^ A := by
    intro A hA
    obtain ⟨C₀, C, hC, h⟩ :=
      Commons.NumberTheory.DirichletCharacter.chi4_primeRecips_sub_const_powLog A hA
    refine ⟨C₀, C, hC, fun x hx => ?_⟩
    simp only [c4r]
    exact h x hx
  obtain ⟨LR, hLR⟩ := exists_fixed_limit_of_powLog_rate
    (F := fun x : ℝ => (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x))
    (Y := 2) (by norm_num) primeRecips_rate_ge_two
  obtain ⟨LX, hLX⟩ := exists_fixed_limit_of_powLog_rate
    (F := fun x : ℝ => ∑ p ∈ (⌊x⌋₊).primesLE, c4r p / (p : ℝ)) (Y := 2) (by norm_num) hXrate
  refine ⟨LR + LX - LZ, ?_⟩
  intro A hA
  obtain ⟨CR, hCRpos, hCR⟩ := hLR A hA
  obtain ⟨CX, hCXpos, hCX⟩ := hLX A hA
  obtain ⟨CZ, hCZpos, hCZ⟩ := Zc_rate A hA
  refine ⟨CR + CX + CZ, by positivity, ?_⟩
  intro y hy
  rw [target_sum_eq y]
  have h1 := hCR y hy
  have h2 := hCX y hy
  have h3 := hCZ y hy
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  have hpowpos : 0 < (Real.log y) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hkey : (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
        + (∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ))
        - (∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ) ^ 2)
        - (Real.log (Real.log y) + (LR + LX - LZ))
      = ((∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log y) - LR)
        + ((∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ)) - LX)
        - ((∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ) ^ 2) - LZ) := by ring
  rw [hkey]
  set r1 : ℝ := (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log y) - LR with hr1
  set r2 : ℝ := (∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ)) - LX with hr2
  set r3 : ℝ := (∑ p ∈ (⌊y⌋₊).primesLE, c4r p / (p : ℝ) ^ 2) - LZ with hr3
  have h1' : |r1| ≤ CR / (Real.log y) ^ A := by rw [hr1]; exact h1
  have h2' : |r2| ≤ CX / (Real.log y) ^ A := by rw [hr2]; exact h2
  have h3' : |r3| ≤ CZ / (Real.log y) ^ A := by rw [hr3]; exact h3
  have htri : |r1 + r2 - r3| ≤ |r1| + |r2| + |r3| := by
    calc |r1 + r2 - r3| = |(r1 + r2) + -r3| := by rw [sub_eq_add_neg]
      _ ≤ |r1 + r2| + |-r3| := abs_add_le _ _
      _ = |r1 + r2| + |r3| := by rw [abs_neg]
      _ ≤ (|r1| + |r2|) + |r3| := add_le_add (abs_add_le r1 r2) le_rfl
      _ = |r1| + |r2| + |r3| := by ring
  calc |r1 + r2 - r3| ≤ |r1| + |r2| + |r3| := htri
    _ ≤ CR / (Real.log y) ^ A + CX / (Real.log y) ^ A + CZ / (Real.log y) ^ A := by
        linarith [h1', h2', h3']
    _ = (CR + CX + CZ) / (Real.log y) ^ A := by ring

end

section

local syntax (name := bigsum65) "∑ " ident " ∈ " term:65 ", " term:65 : term
local macro_rules
  | `(bigsum65| ∑ $p ∈ $s, $body) => `(Finset.sum $s (fun $p => $body))

theorem X2Y4_density_prime_sum_powLog :
    ∃ c : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE,
          (1 + ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ)) / (p : ℝ)
            - ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) ^ 2)
        - (Real.log (Real.log y) + c)| ≤ C / (Real.log y) ^ A := by
  exact X2Y4_density_prep

end

end Commons.NumberTheory.FriedlanderIwaniec
