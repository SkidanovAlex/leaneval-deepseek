import Mathlib
import Submission.Commons.NumberTheory.DuffinSchaeffer.exists_coprime_in_Ico_of_lt
import Submission.Commons.NumberTheory.DuffinSchaeffer.eventually_four_pow_primeFactors_card_lt_mul_nat

namespace Commons.NumberTheory.DuffinSchaeffer

open Filter Set
open scoped Topology

theorem eventually_reduced_fractions_near_Ico_nat {x : ℝ} (hx : x ∈ Set.Ico 0 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ m : ℕ, m < n ∧ m.gcd n = 1 ∧ |x - (m : ℝ) / n| < ε := by
  have hx0 : 0 ≤ x := (Set.mem_Ico.mp hx).1
  have hx1 : x < 1 := (Set.mem_Ico.mp hx).2
  by_cases hxsmall : x < ε / 2
  · -- If `x` is close to `0`, the reduced fraction `1 / n` works for all large `n`.
    have h_inv : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / n < ε / 2 := by
      let N : ℕ := ⌈2 / ε⌉₊ + 1
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hceil : (2 : ℝ) / ε ≤ ⌈2 / ε⌉₊ := Nat.le_ceil (2 / ε)
      have hN : (2 : ℝ) / ε < N := by
        have : (⌈2 / ε⌉₊ : ℝ) < N := by exact_mod_cast (Nat.lt_succ_self _)
        linarith
      have hn2 : (2 : ℝ) / ε < n := by linarith
      have hNpos : 0 < N := by dsimp [N]; omega
      have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le hNpos hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
      have : (1 : ℝ) / n < ε / 2 := by
        have hn2' : 2 < ε * n := (div_lt_iff₀' hε).1 hn2
        rw [div_lt_iff₀' hnpos]
        nlinarith
      exact this
    filter_upwards [h_inv, Filter.eventually_gt_atTop 1] with n hninv hn1
    refine ⟨1, hn1, ?_, ?_⟩
    · simp
    · have h1pos : 0 ≤ (1 : ℝ) / n := by positivity
      rw [abs_lt]
      constructor
      · have : -ε < -((1 : ℝ) / n) := by nlinarith [hninv]
        nlinarith
      · nlinarith [hxsmall, h1pos, hε]
  · -- Now `x` is bounded away from `0`.  We find a reduced residue in a short interval
    -- immediately to the left of `⌊n * x⌋₊`.
    let δ : ℝ := ε / 8
    have hδ : 0 < δ := by positivity
    have h4 : ∀ᶠ n : ℕ in Filter.atTop,
        (4 : ℝ) ^ n.primeFactors.card < δ * n :=
      eventually_four_pow_primeFactors_card_lt_mul_nat δ hδ
    have hδpos3 : 0 < 3 * δ := by positivity
    have hge1 : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ 3 * δ * n := by
      have ht := (tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / (3 * δ)) :
        ∀ᶠ n : ℕ in Filter.atTop, (1 / (3 * δ) : ℝ) ≤ n)
      filter_upwards [ht] with n hn
      have h := mul_le_mul_of_nonneg_left hn (le_of_lt hδpos3)
      have hdiv : 3 * δ * (1 / (3 * δ)) = 1 := by field_simp [ne_of_gt hδpos3]
      rw [← hdiv]
      exact h
    have hεδ : 0 < ε - δ := by
      dsimp [δ]
      linarith
    have hlt2 : ∀ᶠ n : ℕ in Filter.atTop, δ * n + 2 < ε * n := by
      have ht := (tendsto_natCast_atTop_atTop.eventually_gt_atTop (2 / (ε - δ)) :
        ∀ᶠ n : ℕ in Filter.atTop, (2 / (ε - δ) : ℝ) < n)
      filter_upwards [ht] with n hn
      have h := mul_lt_mul_of_pos_left hn hεδ
      have h2 : 2 < (ε - δ) * n := by
        simpa [mul_div_cancel₀ 2 (ne_of_gt hεδ)] using h
      nlinarith
    filter_upwards [h4, hge1, hlt2, Filter.eventually_gt_atTop 0] with n h4n h1n h2n hn0
    let L : ℕ := ⌊δ * n⌋₊ + 1
    let c : ℕ := ⌊(n : ℝ) * x⌋₊
    have hL_gt : δ * n < L := by
      dsimp [L]
      simpa using (Nat.lt_floor_add_one (δ * n) : δ * n < ↑⌊δ * n⌋₊ + 1)
    have hL_le : (L : ℝ) ≤ δ * n + 1 := by
      dsimp [L]
      have hf : (⌊δ * n⌋₊ : ℝ) ≤ δ * n := Nat.floor_le (by positivity : 0 ≤ δ * n)
      have h : (⌊δ * n⌋₊ : ℝ) + 1 ≤ δ * n + 1 := by linarith
      simpa [Nat.cast_add] using h
    have h4L_nat : 4 ^ n.primeFactors.card < L := by
      have h4L_real : ((4 ^ n.primeFactors.card : ℕ) : ℝ) < (L : ℝ) := by
        calc
          ((4 ^ n.primeFactors.card : ℕ) : ℝ) = (4 : ℝ) ^ n.primeFactors.card := by
            norm_num [Nat.cast_pow]
          _ < δ * n := h4n
          _ < (L : ℝ) := hL_gt
      exact Nat.cast_lt.mp h4L_real
    have hxε : ε / 2 ≤ x := le_of_not_gt hxsmall
    have hc_ge : (L : ℝ) ≤ c := by
      have h1 : δ * n + 1 ≤ 4 * δ * n := by nlinarith [h1n]
      have h2 : 4 * δ * n ≤ (n : ℝ) * x := by
        calc
          4 * δ * n = (n : ℝ) * (4 * δ) := by ring
          _ ≤ (n : ℝ) * (ε / 2) := by
            gcongr
            dsimp [δ]
            nlinarith
          _ ≤ (n : ℝ) * x := by gcongr
      have hfloor_le : ⌊δ * n + 1⌋₊ ≤ c := by
        exact Nat.floor_mono (h1.trans h2)
      have hfloor_add : ⌊δ * n + 1⌋₊ = ⌊δ * n⌋₊ + 1 := by
        exact Nat.floor_add_one (by positivity : 0 ≤ δ * n)
      dsimp [L, c]
      rw [← hfloor_add]
      exact_mod_cast hfloor_le
    have hcL : L ≤ c := by
      exact_mod_cast hc_ge
    let a : ℕ := c - L
    have hc_le_nx : (c : ℝ) ≤ (n : ℝ) * x :=
      Nat.floor_le (by positivity : 0 ≤ (n : ℝ) * x)
    have hnx_lt_c1 : (n : ℝ) * x < (c : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one ((n : ℝ) * x) :
        (n : ℝ) * x < ↑⌊(n : ℝ) * x⌋₊ + 1)
    have hc_lt_n : c < n := by
      have : (c : ℝ) < (n : ℝ) := by
        calc
          (c : ℝ) ≤ (n : ℝ) * x := hc_le_nx
          _ < (n : ℝ) * 1 := by
            gcongr
          _ = n := by norm_num
      exact_mod_cast this
    have hex : ∃ m ∈ Finset.Ico a (a + L), m.gcd n = 1 :=
      exists_coprime_in_Ico_of_lt hn0 h4L_nat
    obtain ⟨m, hmIco, hmgcd⟩ := hex
    have hmaL : a + L = c := by
      dsimp [a]
      exact Nat.sub_add_cancel hcL
    have hm_lt_c : m < c := by
      have hm' := (Finset.mem_Ico.mp hmIco).2
      simpa [hmaL] using hm'
    have hm_lt_n : m < n := hm_lt_c.trans hc_lt_n
    have hm_ge : (c : ℝ) - L ≤ m := by
      have hm' : a ≤ m := (Finset.mem_Ico.mp hmIco).1
      have hm_sub : c - L ≤ m := by
        simpa [a] using hm'
      have hsub_real : ((c - L : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_sub
      simpa [Nat.cast_sub hcL] using hsub_real
    have hdist : |x - (m : ℝ) / n| < ε := by
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
      have hm_lt_nx : (m : ℝ) < (n : ℝ) * x := by
        exact lt_of_lt_of_le (by exact_mod_cast hm_lt_c) hc_le_nx
      have hsub_nonneg : 0 ≤ x - (m : ℝ) / n := by
        rw [sub_nonneg]
        exact (div_le_iff₀' hnpos).2 (le_of_lt hm_lt_nx)
      have hnx_m : (n : ℝ) * x - m < ε * n := by
        calc
          (n : ℝ) * x - m ≤ (n : ℝ) * x - ((c : ℝ) - L) := by linarith [hm_ge]
          _ = (n : ℝ) * x - (c : ℝ) + L := by ring
          _ < 1 + L := by linarith [hnx_lt_c1]
          _ = L + 1 := by ring
          _ ≤ δ * n + 2 := by linarith [hL_le]
          _ < ε * n := h2n
      have hdiv : x - (m : ℝ) / n = ((n : ℝ) * x - m) / n := by
        field_simp [hnpos.ne']
      rw [abs_of_nonneg hsub_nonneg, hdiv]
      have hnx_m' : (n : ℝ) * x - m < n * ε := by simpa [mul_comm] using hnx_m
      exact (div_lt_iff₀' hnpos).2 hnx_m'
    exact ⟨m, hm_lt_n, hmgcd, hdist⟩

end Commons.NumberTheory.DuffinSchaeffer
