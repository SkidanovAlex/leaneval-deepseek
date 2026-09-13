import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_mul_prod
import Submission.Commons.Combinatorics.QBinomial.alt_sum_eq_one
import Submission.Commons.Combinatorics.QBinomial.gb_le_four_mul_two_pow

namespace Commons.Combinatorics.QBinomial

open Finset

/-- The function `s ↦ 2^s / (2^s - 1)` is antitone on `s ≥ 1`. -/
private lemma pow_div_pow_sub_one_antitone {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (2:ℚ)^b / ((2:ℚ)^b - 1) ≤ (2:ℚ)^a / ((2:ℚ)^a - 1) := by
  have hda : (0:ℚ) < (2:ℚ)^a - 1 := by
    have h1 : (2:ℚ)^1 ≤ (2:ℚ)^a := pow_le_pow_right₀ (by norm_num) ha
    simp only [pow_one] at h1; linarith
  have hdb : (0:ℚ) < (2:ℚ)^b - 1 := by
    have h1 : (2:ℚ)^1 ≤ (2:ℚ)^b := pow_le_pow_right₀ (by norm_num) (le_trans ha hab)
    simp only [pow_one] at h1; linarith
  rw [div_le_div_iff₀ hdb hda]
  have hp : (2:ℚ)^a ≤ (2:ℚ)^b := pow_le_pow_right₀ (by norm_num) hab
  nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) a, pow_pos (show (0:ℚ) < 2 by norm_num) b]

/-- Shifting the exponents of `∏ 2^s / (2^s - 1)` from `c - i` down to `m - i` does not
decrease the product, when `m ≤ c`. -/
private lemma prod_pow_div_pow_sub_one_le_of_le {c m : ℕ} (hm : m ≤ c) :
    (∏ i ∈ Finset.range m, (2:ℚ)^(c-i) / ((2:ℚ)^(c-i) - 1)) ≤
      ∏ i ∈ Finset.range m, (2:ℚ)^(m-i) / ((2:ℚ)^(m-i) - 1) := by
  apply Finset.prod_le_prod
  · intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hci : 1 ≤ c - i := by omega
    have hpos : (0:ℚ) < (2:ℚ)^(c-i) - 1 := by
      have h1 : (2:ℚ)^1 ≤ (2:ℚ)^(c-i) := pow_le_pow_right₀ (by norm_num) hci
      simp only [pow_one] at h1; linarith
    exact div_nonneg (by positivity) (le_of_lt hpos)
  · intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    exact pow_div_pow_sub_one_antitone (by omega) (by omega)

/-- Product form of the Gaussian-binomial ratio bound: for `m + d ≤ n`,
`∏_{i<m} (2^n - 2^i) ≤ 4 · 2^{m·d} · ∏_{i<m} (2^{n-d} - 2^i)` (all in `ℚ`). -/
private lemma prod_two_pow_sub_le (n m d : ℕ) (h : m + d ≤ n) :
    (∏ i ∈ Finset.range m, ((2:ℚ)^n - (2:ℚ)^i)) ≤
      4 * (2:ℚ)^(m*d) * ∏ i ∈ Finset.range m, ((2:ℚ)^(n-d) - (2:ℚ)^i) := by
  have hmd : m ≤ n - d := by omega
  have hden_pos : ∀ i ∈ Finset.range m, (0:ℚ) < (2:ℚ)^(n-d) - (2:ℚ)^i := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have : (2:ℚ)^i < (2:ℚ)^(n-d) := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  have hterm : ∀ i ∈ Finset.range m,
      ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^(n-d) - (2:ℚ)^i)
        ≤ (2:ℚ)^d * ((2:ℚ)^(n-d-i) / ((2:ℚ)^(n-d-i) - 1)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hin : i < n := by omega
    have hndi : i < n - d := by omega
    have hnum_eq : (2:ℚ)^n - (2:ℚ)^i = (2:ℚ)^i * ((2:ℚ)^(n-i) - 1) := by
      have h1 : (2:ℚ)^n = (2:ℚ)^i * (2:ℚ)^(n-i) := by
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hin)]
      rw [h1]; ring
    have hden_eq : (2:ℚ)^(n-d) - (2:ℚ)^i = (2:ℚ)^i * ((2:ℚ)^(n-d-i) - 1) := by
      have h1 : (2:ℚ)^(n-d) = (2:ℚ)^i * (2:ℚ)^(n-d-i) := by
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hndi)]
      rw [h1]; ring
    rw [hnum_eq, hden_eq, mul_div_mul_left _ _ (by positivity : (2:ℚ)^i ≠ 0)]
    have hde : (0:ℚ) < (2:ℚ)^(n-d-i) - 1 := by
      have h1 : (2:ℚ)^1 ≤ (2:ℚ)^(n-d-i) := pow_le_pow_right₀ (by norm_num) (by omega)
      simp only [pow_one] at h1; linarith
    have hle_num : (2:ℚ)^(n-i) - 1 ≤ (2:ℚ)^(n-i) :=
      by linarith [pow_pos (show (0:ℚ) < 2 by norm_num) (n-i)]
    calc ((2:ℚ)^(n-i) - 1) / ((2:ℚ)^(n-d-i) - 1)
        ≤ (2:ℚ)^(n-i) / ((2:ℚ)^(n-d-i) - 1) :=
          div_le_div_of_nonneg_right hle_num (le_of_lt hde)
      _ = (2:ℚ)^d * ((2:ℚ)^(n-d-i) / ((2:ℚ)^(n-d-i) - 1)) := by
          have hexp : (2:ℚ)^(n-i) = (2:ℚ)^d * (2:ℚ)^(n-d-i) := by
            have he : d + (n - d - i) = n - i := by omega
            rw [← he, pow_add]
          rw [hexp]; ring
  have hratio : (∏ i ∈ Finset.range m,
        ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^(n-d) - (2:ℚ)^i)) ≤ 4 * (2:ℚ)^(m*d) := by
    calc (∏ i ∈ Finset.range m, ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^(n-d) - (2:ℚ)^i))
        ≤ ∏ i ∈ Finset.range m,
            ((2:ℚ)^d * ((2:ℚ)^(n-d-i) / ((2:ℚ)^(n-d-i) - 1))) := by
          apply Finset.prod_le_prod
          · intro i hi
            have hden := hden_pos i hi
            have hin : (2:ℚ)^i ≤ (2:ℚ)^n :=
              pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)
            exact div_nonneg (by linarith) (le_of_lt hden)
          · exact hterm
      _ = (2:ℚ)^(d*m) *
            (∏ i ∈ Finset.range m, ((2:ℚ)^(n-d-i) / ((2:ℚ)^(n-d-i) - 1))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
      _ ≤ (2:ℚ)^(d*m) * 4 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (∏ i ∈ Finset.range m, ((2:ℚ)^(n-d-i) / ((2:ℚ)^(n-d-i) - 1)))
              ≤ (∏ i ∈ Finset.range m, ((2:ℚ)^(m-i) / ((2:ℚ)^(m-i) - 1))) :=
                prod_pow_div_pow_sub_one_le_of_le hmd
            _ ≤ 4 := prod_pow_div_pow_sub_one_le_four m
      _ = 4 * (2:ℚ)^(m*d) := by rw [Nat.mul_comm d m]; ring
  have hDpos : (0:ℚ) < ∏ i ∈ Finset.range m, ((2:ℚ)^(n-d) - (2:ℚ)^i) :=
    Finset.prod_pos hden_pos
  rw [Finset.prod_div_distrib, div_le_iff₀ hDpos] at hratio
  exact hratio

/-- The Gaussian binomial satisfies `gb n m ≤ 4 · 2^{m·d} · gb (n-d) m` whenever `m + d ≤ n`. `Commons.Combinatorics.QBinomial.gb n m` is the number of `m`-dimensional subspaces of `𝔽₂ⁿ`, available from `Submission.Commons.Combinatorics.QBinomial.alt_sum_eq_one`; the key identity `gb n m * ∏_{i<m}(2^m - 2^i) = ∏_{i<m}(2^n - 2^i)` is `Commons.LinearAlgebra.Submodule.card_submodule_finrank_mul_prod`. -/
theorem gb_le_four_mul_pow_mul_gb_sub (n m d : ℕ) (h : m + d ≤ n) :
    Commons.Combinatorics.QBinomial.gb n m ≤ 4 * 2 ^ (m * d) * Commons.Combinatorics.QBinomial.gb (n - d) m := by
  have hmd : m ≤ n - d := by omega
  have hid1 : gb n m * (∏ i ∈ Finset.range m, (2^m - 2^i))
      = ∏ i ∈ Finset.range m, (2^n - 2^i) :=
    Commons.LinearAlgebra.Submodule.card_submodule_finrank_mul_prod n m
  have hid2 : gb (n - d) m * (∏ i ∈ Finset.range m, (2^m - 2^i))
      = ∏ i ∈ Finset.range m, (2^(n-d) - 2^i) :=
    Commons.LinearAlgebra.Submodule.card_submodule_finrank_mul_prod (n - d) m
  have hAcast : ((∏ i ∈ Finset.range m, (2^m - 2^i) : ℕ) : ℚ)
      = ∏ i ∈ Finset.range m, ((2:ℚ)^m - (2:ℚ)^i) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hle : (2:ℕ)^i ≤ 2^m := Nat.pow_le_pow_right (by norm_num) (le_of_lt him)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hBcast : ((∏ i ∈ Finset.range m, (2^n - 2^i) : ℕ) : ℚ)
      = ∏ i ∈ Finset.range m, ((2:ℚ)^n - (2:ℚ)^i) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hle : (2:ℕ)^i ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hCcast : ((∏ i ∈ Finset.range m, (2^(n-d) - 2^i) : ℕ) : ℚ)
      = ∏ i ∈ Finset.range m, ((2:ℚ)^(n-d) - (2:ℚ)^i) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hle : (2:ℕ)^i ≤ 2^(n-d) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hApos : (0:ℚ) < ∏ i ∈ Finset.range m, ((2:ℚ)^m - (2:ℚ)^i) :=
    Finset.prod_pos (fun i hi => by
      have h : (2:ℚ)^i < (2:ℚ)^m :=
        pow_lt_pow_right₀ (by norm_num) (Finset.mem_range.mp hi)
      linarith)
  have hq1 : (gb n m : ℚ) * (∏ i ∈ Finset.range m, ((2:ℚ)^m - (2:ℚ)^i))
      = ∏ i ∈ Finset.range m, ((2:ℚ)^n - (2:ℚ)^i) := by
    rw [← hAcast, ← hBcast, ← Nat.cast_mul, hid1]
  have hq2 : (gb (n - d) m : ℚ) * (∏ i ∈ Finset.range m, ((2:ℚ)^m - (2:ℚ)^i))
      = ∏ i ∈ Finset.range m, ((2:ℚ)^(n-d) - (2:ℚ)^i) := by
    rw [← hAcast, ← hCcast, ← Nat.cast_mul, hid2]
  have hprod := prod_two_pow_sub_le n m d h
  have hstep : (gb n m : ℚ) * (∏ i ∈ Finset.range m, ((2:ℚ)^m - (2:ℚ)^i))
      ≤ (4 * (2:ℚ)^(m*d) * (gb (n - d) m : ℚ)) *
          (∏ i ∈ Finset.range m, ((2:ℚ)^m - (2:ℚ)^i)) := by
    rw [hq1]
    calc (∏ i ∈ Finset.range m, ((2:ℚ)^n - (2:ℚ)^i))
        ≤ 4 * (2:ℚ)^(m*d) * (∏ i ∈ Finset.range m, ((2:ℚ)^(n-d) - (2:ℚ)^i)) := hprod
      _ = (4 * (2:ℚ)^(m*d) * (gb (n - d) m : ℚ)) *
            (∏ i ∈ Finset.range m, ((2:ℚ)^m - (2:ℚ)^i)) := by
          rw [← hq2]; ring
  have hmain : (gb n m : ℚ) ≤ 4 * (2:ℚ)^(m*d) * (gb (n - d) m : ℚ) :=
    le_of_mul_le_mul_right hstep hApos
  have hfinal : ((gb n m : ℕ) : ℚ)
      ≤ ((4 * 2 ^ (m * d) * Commons.Combinatorics.QBinomial.gb (n - d) m : ℕ) : ℚ) := by
    push_cast
    exact hmain
  exact_mod_cast hfinal

end Commons.Combinatorics.QBinomial
