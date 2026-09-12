import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt

namespace Commons.Analysis.Real

private lemma nat_div_two_add_one_ge (m : ℕ) :
    ((m : ℝ) + 1) / 2 ≤ ((m / 2 + 1 : ℕ) : ℝ) := by
  have hle : m ≤ 2 * (m / 2) + 1 := by omega
  have hm : (m : ℝ) ≤ 2 * (m / 2 : ℕ) + 1 := by
    have h : (m : ℝ) ≤ ((2 * (m / 2) : ℕ) : ℝ) + 1 := by exact_mod_cast hle
    simpa [Nat.cast_mul] using h
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_num [Nat.cast_add, Nat.cast_mul]
  nlinarith [hm]

lemma refine_param_n0 {ε p μ Rt L0 : ℝ} (hε0 : 0 < ε)
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (hμ0 : 0 < μ) (hRt0 : 0 < Rt) (hL00 : 0 ≤ L0) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n → ∀ (N : ℕ) (hN1 : 1 ≤ N),
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ (L : ℝ) (hLL0 : L ≤ L0),
    L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
      ((1 / 2) * p * (1 - p) * μ ^ 6 * Rt ^ 2 /
        ((N : ℝ) * (n : ℝ))) * (((m / 2 + 1 : ℕ) : ℝ)) := by
  set c : ℝ := (1 / 2) * p * (1 - p) * μ ^ 6 * Rt ^ 2 with hcdef
  have hpm : 0 < 1 - p := by linarith
  have hc0 : 0 < c := by
    rw [hcdef]
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hp0) hpm) (pow_pos hμ0 6))
      (pow_pos hRt0 2)
  have hcε : 0 < c * ε := mul_pos hc0 hε0
  let C : ℝ := 4 * L0 / (c * ε)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hL00) (le_of_lt hcε)
  let n₀ : ℕ := Nat.ceil (C ^ 2) + 1
  refine ⟨n₀, ?_⟩
  intro n hn0n N hN1 m hm L hLL0
  -- lower bound: C ^ 2 < (n : ℝ)
  have hn0C2 : C ^ 2 < (n₀ : ℝ) := by
    dsimp [n₀]
    rw [Nat.cast_add, Nat.cast_one]
    have hge : C ^ 2 ≤ (Nat.ceil (C ^ 2) : ℝ) := Nat.le_ceil (C ^ 2)
    linarith
  have hnC2 : C ^ 2 < (n : ℝ) := lt_of_lt_of_le hn0C2 (by exact_mod_cast hn0n)
  have hCs : C < Real.sqrt (n : ℝ) := (Real.lt_sqrt hC0).2 hnC2
  -- positivity: N, n, sqrt
  have hn1nat : 1 ≤ n := by
    have : 1 ≤ n₀ := by
      dsimp [n₀]
      omega
    exact le_trans this hn0n
  have hnpos : 0 < (n : ℝ) := by
    have h' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1nat
    exact lt_of_lt_of_le (by norm_num) h'
  have hNpos : 0 < (N : ℝ) := by
    have h' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    exact lt_of_lt_of_le (by norm_num) h'
  let s : ℝ := Real.sqrt (n : ℝ)
  have hs0 : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos_of_pos hnpos
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  -- L0 / s < c * ε / 4
  have hCeq : (c * ε / 4) * C = L0 := by
    dsimp [C]
    have hcne : c ≠ 0 := ne_of_gt hc0
    have hεne : ε ≠ 0 := ne_of_gt hε0
    have hcεne : c * ε ≠ 0 := ne_of_gt hcε
    field_simp [hcεne, hcne, hεne]
  have hstep0 : L0 < (c * ε / 4) * s := by
    rw [← hCeq]
    exact mul_lt_mul_of_pos_left hCs (div_pos hcε (by norm_num))
  have hL0s : L0 / s < c * ε / 4 := by
    exact (div_lt_iff₀ hs0).2 hstep0
  have hLs : L / s ≤ L0 / s := div_le_div_of_nonneg_right hLL0 (le_of_lt hs0)
  have hLlt0 : L / s < c * ε / 4 := lt_of_le_of_lt hLs hL0s
  -- floor bound: ε * (n : ℝ) / 4 < a := ((m / 2 + 1 : ℕ) : ℝ)
  have hxpos : 0 < ε * (n : ℝ) / 2 := by positivity
  have hmle0 := Nat.floor_le (a := ε * (n : ℝ) / 2) (le_of_lt hxpos)
  have hm_lt0 := Nat.lt_floor_add_one (a := ε * (n : ℝ) / 2)
  have hm_lt : ε * (n : ℝ) / 2 < (m : ℝ) + 1 := by simpa [hm.symm] using hm_lt0
  have hh := div_lt_div_of_pos_right hm_lt (by norm_num : (0 : ℝ) < 2)
  have hmlt4 : ε * (n : ℝ) / 4 < ((m : ℝ) + 1) / 2 := by
    ring_nf at hh ⊢
    exact hh
  have haBig : ε * (n : ℝ) / 4 < ((m / 2 + 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le hmlt4 (nat_div_two_add_one_ge m)
  -- c * ε / 4 < c * a / (n : ℝ)
  let a : ℝ := ((m / 2 + 1 : ℕ) : ℝ)
  have hRHSb : c * ε / 4 < c * a / (n : ℝ) := by
    have h1 : c * (ε * (n : ℝ) / 4) < c * a := mul_lt_mul_of_pos_left haBig hc0
    have heq : c * (ε * (n : ℝ) / 4) = (c * ε / 4) * (n : ℝ) := by
      field_simp [show (4 : ℝ) ≠ 0 by norm_num]
    rw [lt_div_iff₀ hnpos]
    rwa [← heq]
  have hmain : L / s < c * a / (n : ℝ) := lt_trans hLlt0 hRHSb
  -- divide by N and compare with target
  have hdiv := div_lt_div_of_pos_right hmain hNpos
  have hLHS : (L / s) / (N : ℝ) = L / ((N : ℝ) * s) := by
    field_simp [hsne, hNne]
  have hRHS : (c * a / (n : ℝ)) / (N : ℝ) = (c / ((N : ℝ) * (n : ℝ))) * a := by
    field_simp [hnne, hNne]
  rwa [hLHS, hRHS] at hdiv

end Commons.Analysis.Real