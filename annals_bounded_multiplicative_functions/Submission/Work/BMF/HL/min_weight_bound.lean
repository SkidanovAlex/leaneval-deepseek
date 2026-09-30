import Mathlib
import Submission.Work.BMF.HL.minwt_region_one
import Submission.Work.BMF.HL.minwt_tail_term
import Submission.Work.BMF.HL.minwt_factor_large

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- For `2 ≤ y < 11` the tail factor is a bounded multiple: `2/δ(y) ≤ 2 log 11` where
`δ(y) = min 1 (1/log y)`. -/
theorem minwt_factor_small {y : ℝ} (hy : 2 ≤ y) (hy11 : y < 11) :
    2 / min 1 (1 / Real.log y) ≤ 2 * Real.log 11 := by
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog11 : 0 < Real.log 11 := Real.log_pos (by norm_num)
  have hlog11ge1 : 1 ≤ Real.log 11 := by
    have hexp : Real.exp 1 ≤ 11 := by linarith [Real.exp_one_lt_three]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 11 := Real.log_le_log (Real.exp_pos 1) hexp
  have hle : Real.log y ≤ Real.log 11 := Real.log_le_log (by linarith) (le_of_lt hy11)
  have hmin : 1 / Real.log 11 ≤ min 1 (1 / Real.log y) := by
    refine le_min ?_ ?_
    · exact (div_le_one hlog11).mpr hlog11ge1
    · exact one_div_le_one_div_of_le hlogy hle
  have hMpos : 0 < min 1 (1 / Real.log y) := lt_min one_pos (one_div_pos.mpr hlogy)
  rw [div_le_iff₀ hMpos]
  have h2 : (2 * Real.log 11) * (1 / Real.log 11)
      ≤ (2 * Real.log 11) * min 1 (1 / Real.log y) :=
    mul_le_mul_of_nonneg_left hmin (by linarith)
  have heq : (2 * Real.log 11) * (1 / Real.log 11) = 2 := by field_simp
  linarith

/-- Crude absolute bound for the reciprocal-prime sum up to `121`. -/
theorem minwt_finite_start :
    (∑ p ∈ (121 : ℕ).primesLE, (1 : ℝ) / p) ≤ 61 := by
  have hsub : (121 : ℕ).primesLE ⊆ Finset.range 122 := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    simp only [Finset.mem_range]
    omega
  have hcard : ((121 : ℕ).primesLE).card ≤ 122 := by
    simpa using Finset.card_le_card hsub
  calc (∑ p ∈ (121 : ℕ).primesLE, (1 : ℝ) / p)
      ≤ ∑ p ∈ (121 : ℕ).primesLE, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE hp
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        exact one_div_le_one_div_of_le (by norm_num) h2
    _ = ((121 : ℕ).primesLE).card * (1 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 122 * (1 / 2) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        exact_mod_cast hcard
    _ = 61 := by norm_num

/-- Weighted tail mass.  Write `δ(y) := min 1 (1/log y)`.  Given the two-sided Mertens split
`Σ_{y<p≤x} 1/p ≤ log(log x/log y) + CM` for `11 ≤ y ≤ x` and the sharp block estimate
`Σ_{a<p≤b} 1/(p log p) ≤ CI/log a` for `11 ≤ a ≤ b`, the weighted mass
`Σ_{y<p≤x} min(1, 2/(δ(y) log p))/p` is bounded by an absolute constant for all `2 ≤ y ≤ x`.

Route: split the range of primes at `y²` (where `δ(y)·log p` crosses `2`).  On `p ≤ y²` the
minimum is `1`, and the mass there is `≤ log 2 + CM` via the first hypothesis when `y ≥ 11`, and
bounded by a crude constant when `y < 11`.  On `p > y²` use `min(1,z) ≤ z` together with the second
hypothesis at `a = y²` (valid when `y² ≥ 11`, so `y ≥ 4`), giving
`(2/δ)·CI/log(y²) = CI/(δ log y) = CI/min(1, log y) ≤ CI`; for `2 ≤ y < 11` the whole range has
`δ^{-1} = max(1, log y) < log 11`, and the reciprocal mass beyond `11` is `≤ CI/log 11`, so again an
absolute bound. -/
theorem min_weight_bound {CM CI : ℝ} (hCM : 0 < CM) (hCI : 0 < CI)
    (hsplit : ∀ x y : ℝ, 11 ≤ y → y ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p) ≤
        Real.log (Real.log x / Real.log y) + CM)
    (hinv : ∀ a b : ℝ, 11 ≤ a → a ≤ b →
      (∑ p ∈ (⌊b⌋₊).primesLE \ (⌊a⌋₊).primesLE, 1 / ((p : ℝ) * Real.log p))
        ≤ CI / Real.log a) :
    ∃ K : ℝ, 0 < K ∧ ∀ y x : ℝ, 2 ≤ y → y ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
          min 1 (2 / (min 1 (1 / Real.log y) * Real.log p)) / (p : ℝ)) ≤ K := by
  refine ⟨max (Real.log 2 + CM + CI) (61 + 2 * CI), ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (le_max_right (Real.log 2 + CM + CI) (61 + 2 * CI))
    linarith
  · intro y x hy hyx
    set S : Finset ℕ := (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE with hS
    set g : ℕ → ℝ := fun p => min 1 (2 / (min 1 (1 / Real.log y) * Real.log p)) / (p : ℝ) with hg
    have hdec : ∀ Cut : ℕ, ∑ p ∈ S, g p
        = ∑ p ∈ S.filter (fun p => p ≤ Cut), g p
          + ∑ p ∈ S.filter (fun p => ¬ p ≤ Cut), g p := by
      intro Cut
      exact (Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ Cut) g).symm
    have hy1 : (1 : ℝ) < y := by linarith
    have hlogy : 0 < Real.log y := Real.log_pos hy1
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hdeltapos : 0 < min 1 (1 / Real.log y) := lt_min one_pos (one_div_pos.mpr hlogy)
    have hdeltann : 0 ≤ 2 / min 1 (1 / Real.log y) := by positivity
    rcases le_or_gt 11 y with hy11 | hy11
    · -- Large `y`: split at `⌊y²⌋₊`.
      have hy_le_y2 : y ≤ y ^ 2 := by nlinarith [hy]
      have h11y2 : (11 : ℝ) ≤ y ^ 2 := by nlinarith [hy11]
      have hlogdiv : Real.log (y ^ 2) / Real.log y = 2 := by
        rw [Real.log_pow]
        field_simp
        norm_num
      rw [hdec ⌊y ^ 2⌋₊]
      have hA : ∑ p ∈ S.filter (fun p => p ≤ ⌊y ^ 2⌋₊), g p ≤ Real.log 2 + CM := by
        have hsub : S.filter (fun p => p ≤ ⌊y ^ 2⌋₊)
            ⊆ (⌊y ^ 2⌋₊).primesLE \ (⌊y⌋₊).primesLE := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, hple⟩ := hp
          rw [hS, Finset.mem_sdiff] at hpS
          rw [Finset.mem_sdiff]
          exact ⟨Nat.mem_primesLE.mpr ⟨hple, Nat.prime_of_mem_primesLE hpS.1⟩, hpS.2⟩
        have heq : ∑ p ∈ S.filter (fun p => p ≤ ⌊y ^ 2⌋₊), g p
            = ∑ p ∈ S.filter (fun p => p ≤ ⌊y ^ 2⌋₊), (1 : ℝ) / (p : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, hple⟩ := hp
          have hpprime : Nat.Prime p := by
            rw [hS, Finset.mem_sdiff] at hpS
            exact Nat.prime_of_mem_primesLE hpS.1
          have hpR : (p : ℝ) ≤ y ^ 2 := by
            have h1 : (p : ℝ) ≤ (⌊y ^ 2⌋₊ : ℝ) := by exact_mod_cast hple
            have h2 : (⌊y ^ 2⌋₊ : ℝ) ≤ y ^ 2 := Nat.floor_le (by positivity)
            linarith
          simp only [hg]
          rw [minwt_region_one hy hpprime hpR]
        rw [heq]
        calc ∑ p ∈ S.filter (fun p => p ≤ ⌊y ^ 2⌋₊), (1 : ℝ) / (p : ℝ)
            ≤ ∑ p ∈ (⌊y ^ 2⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro p hpT _
              have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hpT).1
              have hp0 : (0 : ℝ) < (p : ℝ) := by
                have : 0 < p := hpp.pos
                exact_mod_cast this
              exact div_nonneg zero_le_one (le_of_lt hp0)
          _ ≤ Real.log (Real.log (y ^ 2) / Real.log y) + CM := hsplit (y ^ 2) y hy11 hy_le_y2
          _ = Real.log 2 + CM := by rw [hlogdiv]
      have hB : ∑ p ∈ S.filter (fun p => ¬ p ≤ ⌊y ^ 2⌋₊), g p ≤ CI := by
        have hterm : ∀ p ∈ S.filter (fun p => ¬ p ≤ ⌊y ^ 2⌋₊),
            g p ≤ (2 / min 1 (1 / Real.log y)) * (1 / ((p : ℝ) * Real.log p)) := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, _⟩ := hp
          have hpprime : Nat.Prime p := by
            rw [hS, Finset.mem_sdiff] at hpS
            exact Nat.prime_of_mem_primesLE hpS.1
          simp only [hg]
          exact minwt_tail_term hy hpprime
        have hsub : S.filter (fun p => ¬ p ≤ ⌊y ^ 2⌋₊)
            ⊆ (⌊max x (y ^ 2)⌋₊).primesLE \ (⌊y ^ 2⌋₊).primesLE := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, hpgt⟩ := hp
          rw [hS, Finset.mem_sdiff] at hpS
          have hpx : p ≤ ⌊x⌋₊ := (Nat.mem_primesLE.mp hpS.1).1
          rw [Finset.mem_sdiff]
          refine ⟨Nat.mem_primesLE.mpr ⟨?_, Nat.prime_of_mem_primesLE hpS.1⟩, ?_⟩
          · apply Nat.le_floor
            have h1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hpx
            have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
            have h3 : x ≤ max x (y ^ 2) := le_max_left _ _
            linarith
          · intro hcon
            exact hpgt (Nat.mem_primesLE.mp hcon).1
        calc ∑ p ∈ S.filter (fun p => ¬ p ≤ ⌊y ^ 2⌋₊), g p
            ≤ ∑ p ∈ S.filter (fun p => ¬ p ≤ ⌊y ^ 2⌋₊),
                (2 / min 1 (1 / Real.log y)) * (1 / ((p : ℝ) * Real.log p)) :=
              Finset.sum_le_sum hterm
          _ = (2 / min 1 (1 / Real.log y))
                * ∑ p ∈ S.filter (fun p => ¬ p ≤ ⌊y ^ 2⌋₊),
                    1 / ((p : ℝ) * Real.log p) := by rw [Finset.mul_sum]
          _ ≤ (2 / min 1 (1 / Real.log y))
                * ∑ p ∈ (⌊max x (y ^ 2)⌋₊).primesLE \ (⌊y ^ 2⌋₊).primesLE,
                    1 / ((p : ℝ) * Real.log p) := by
              apply mul_le_mul_of_nonneg_left _ hdeltann
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro p hpT _
              have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hpT).1
              have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
              have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
              have hlp : 0 < Real.log p := Real.log_pos (by linarith)
              exact div_nonneg zero_le_one (le_of_lt (mul_pos hp0 hlp))
          _ ≤ (2 / min 1 (1 / Real.log y)) * (CI / Real.log (y ^ 2)) := by
              apply mul_le_mul_of_nonneg_left _ hdeltann
              exact hinv (y ^ 2) (max x (y ^ 2)) h11y2 (le_max_right _ _)
          _ = (2 / min 1 (1 / Real.log y)) * CI / Real.log (y ^ 2) := by ring
          _ ≤ CI := minwt_factor_large hCI hy11
      have : ∑ p ∈ S.filter (fun p => p ≤ ⌊y ^ 2⌋₊), g p
            + ∑ p ∈ S.filter (fun p => ¬ p ≤ ⌊y ^ 2⌋₊), g p ≤ Real.log 2 + CM + CI := by
        linarith
      exact le_trans this (le_max_left _ _)
    · -- Small `y`: split at `121`.
      rw [hdec 121]
      have hA : ∑ p ∈ S.filter (fun p => p ≤ 121), g p ≤ 61 := by
        have hsub : S.filter (fun p => p ≤ 121) ⊆ (121 : ℕ).primesLE := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, hple⟩ := hp
          rw [hS, Finset.mem_sdiff] at hpS
          exact Nat.mem_primesLE.mpr ⟨hple, Nat.prime_of_mem_primesLE hpS.1⟩
        have hterm : ∀ p ∈ S.filter (fun p => p ≤ 121), g p ≤ (1 : ℝ) / (p : ℝ) := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, _⟩ := hp
          have hpprime : Nat.Prime p := by
            rw [hS, Finset.mem_sdiff] at hpS
            exact Nat.prime_of_mem_primesLE hpS.1
          have hp0 : (0 : ℝ) < (p : ℝ) := by
            have : 0 < p := hpprime.pos
            exact_mod_cast this
          simp only [hg]
          exact div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hp0)
        calc ∑ p ∈ S.filter (fun p => p ≤ 121), g p
            ≤ ∑ p ∈ S.filter (fun p => p ≤ 121), (1 : ℝ) / (p : ℝ) := Finset.sum_le_sum hterm
          _ ≤ ∑ p ∈ (121 : ℕ).primesLE, (1 : ℝ) / (p : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro p hpT _
              have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE hpT
              have hp0 : (0 : ℝ) < (p : ℝ) := by
                have : 0 < p := hpp.pos
                exact_mod_cast this
              exact div_nonneg zero_le_one (le_of_lt hp0)
          _ ≤ 61 := minwt_finite_start
      have hB : ∑ p ∈ S.filter (fun p => ¬ p ≤ 121), g p ≤ 2 * CI := by
        have hterm : ∀ p ∈ S.filter (fun p => ¬ p ≤ 121),
            g p ≤ (2 / min 1 (1 / Real.log y)) * (1 / ((p : ℝ) * Real.log p)) := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, _⟩ := hp
          have hpprime : Nat.Prime p := by
            rw [hS, Finset.mem_sdiff] at hpS
            exact Nat.prime_of_mem_primesLE hpS.1
          simp only [hg]
          exact minwt_tail_term hy hpprime
        have hsub : S.filter (fun p => ¬ p ≤ 121)
            ⊆ (⌊max x 11⌋₊).primesLE \ (⌊(11 : ℝ)⌋₊).primesLE := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hpS, hpgt⟩ := hp
          rw [hS, Finset.mem_sdiff] at hpS
          have hpx : p ≤ ⌊x⌋₊ := (Nat.mem_primesLE.mp hpS.1).1
          rw [Finset.mem_sdiff]
          refine ⟨Nat.mem_primesLE.mpr ⟨?_, Nat.prime_of_mem_primesLE hpS.1⟩, ?_⟩
          · apply Nat.le_floor
            have h1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hpx
            have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
            have h3 : x ≤ max x 11 := le_max_left _ _
            linarith
          · intro hcon
            have hple : p ≤ ⌊(11 : ℝ)⌋₊ := (Nat.mem_primesLE.mp hcon).1
            have h11 : ⌊(11 : ℝ)⌋₊ = 11 := by norm_num
            rw [h11] at hple
            omega
        have hfac : 2 / min 1 (1 / Real.log y) ≤ 2 * Real.log 11 := minwt_factor_small hy hy11
        have hlog11 : 0 < Real.log 11 := Real.log_pos (by norm_num)
        calc ∑ p ∈ S.filter (fun p => ¬ p ≤ 121), g p
            ≤ ∑ p ∈ S.filter (fun p => ¬ p ≤ 121),
                (2 / min 1 (1 / Real.log y)) * (1 / ((p : ℝ) * Real.log p)) :=
              Finset.sum_le_sum hterm
          _ = (2 / min 1 (1 / Real.log y))
                * ∑ p ∈ S.filter (fun p => ¬ p ≤ 121),
                    1 / ((p : ℝ) * Real.log p) := by rw [Finset.mul_sum]
          _ ≤ (2 / min 1 (1 / Real.log y))
                * ∑ p ∈ (⌊max x 11⌋₊).primesLE \ (⌊(11 : ℝ)⌋₊).primesLE,
                    1 / ((p : ℝ) * Real.log p) := by
              apply mul_le_mul_of_nonneg_left _ hdeltann
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro p hpT _
              have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hpT).1
              have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
              have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
              have hlp : 0 < Real.log p := Real.log_pos (by linarith)
              exact div_nonneg zero_le_one (le_of_lt (mul_pos hp0 hlp))
          _ ≤ (2 / min 1 (1 / Real.log y)) * (CI / Real.log 11) := by
              apply mul_le_mul_of_nonneg_left _ hdeltann
              exact hinv 11 (max x 11) le_rfl (le_max_right _ _)
          _ = (2 / min 1 (1 / Real.log y)) * CI / Real.log 11 := by ring
          _ ≤ 2 * CI := by
              have h1 : (2 / min 1 (1 / Real.log y)) * CI / Real.log 11
                  ≤ (2 * Real.log 11) * CI / Real.log 11 := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hlog11)
                exact mul_le_mul_of_nonneg_right hfac (le_of_lt hCI)
              have h2 : (2 * Real.log 11) * CI / Real.log 11 = 2 * CI := by
                field_simp
              linarith
      have : ∑ p ∈ S.filter (fun p => p ≤ 121), g p
            + ∑ p ∈ S.filter (fun p => ¬ p ≤ 121), g p ≤ 61 + 2 * CI := by
        linarith
      exact le_trans this (le_max_right _ _)

end Work.BMF.HL
