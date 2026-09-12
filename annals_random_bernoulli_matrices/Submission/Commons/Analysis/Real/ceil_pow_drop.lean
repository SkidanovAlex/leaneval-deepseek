import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

private lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsqrt : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx]
    ring
  rw [hsqrt]
  exact mul_le_mul_of_nonneg_left (Real.log_le_self (Real.sqrt_nonneg x)) (by norm_num)

private lemma two_sqrt_le_mul_of_ge {c x : ℝ} (hc : 0 < c) (hx : 4 / c ^ 2 ≤ x) :
    2 * Real.sqrt x ≤ c * x := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hx0 : 0 ≤ x := le_trans (le_of_lt (by positivity : 0 < 4 / c ^ 2)) hx
  have hcx2 : 0 ≤ (c * x) / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hx (le_of_lt hc2)
  have h4 : 4 ≤ x * c ^ 2 := by
    have hcancel : (4 / c ^ 2) * c ^ 2 = 4 := by
      field_simp [ne_of_gt hc2]
    rwa [hcancel] at hmul
  have h4x : 4 * x ≤ (x * c ^ 2) * x := mul_le_mul_of_nonneg_right h4 hx0
  have hsq4 : 4 * x ≤ (c * x) ^ 2 := by
    calc
      4 * x ≤ (x * c ^ 2) * x := h4x
      _ = (c * x) ^ 2 := by ring
  have hpos4 : (0 : ℝ) < 4 := by norm_num
  have hsq : x ≤ ((c * x) / 2) ^ 2 := by
    calc
      x ≤ (c * x) ^ 2 / 4 := (le_div_iff₀ hpos4).2 (by simpa [mul_comm] using hsq4)
      _ = ((c * x) / 2) ^ 2 := by ring
  have hsqrt_le : Real.sqrt x ≤ (c * x) / 2 := (Real.sqrt_le_left hcx2).2 hsq
  have h2s : 2 * Real.sqrt x ≤ c * x := by
    have hm := mul_le_mul_of_nonneg_left hsqrt_le (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  exact h2s

private lemma eventually_log_le_mul {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → Real.log (n : ℝ) ≤ c * (n : ℝ) := by
  let B : ℝ := max (4 / c ^ 2) 1
  let N : ℕ := max 1 (Nat.ceil B)
  refine ⟨N, le_max_left 1 (Nat.ceil B), ?_⟩
  intro n hn
  have hBn : B ≤ (n : ℝ) := by
    have h1 : B ≤ (Nat.ceil B : ℝ) := by
      dsimp [B]
      exact Nat.le_ceil (max (4 / c ^ 2) 1)
    have h3 : (Nat.ceil B : ℝ) ≤ (N : ℝ) := by
      dsimp [N]
      exact_mod_cast (le_max_right 1 (Nat.ceil B) : Nat.ceil B ≤ max 1 (Nat.ceil B))
    have h4 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_trans (le_trans h1 h3) h4
  have hx : 4 / c ^ 2 ≤ (n : ℝ) := by
    have hb : 4 / c ^ 2 ≤ B := le_max_left (4 / c ^ 2) 1
    exact le_trans hb hBn
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by
    have hN : (1 : ℕ) ≤ n := le_trans (le_max_left 1 (Nat.ceil B)) hn
    exact_mod_cast hN
  have hn0 : 0 ≤ (n : ℝ) := le_trans (by norm_num : (0 : ℝ) ≤ 1) h1n
  calc
    Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := log_le_two_sqrt hn0
    _ ≤ c * (n : ℝ) := two_sqrt_le_mul_of_ge hc hx

lemma ceil_pow_drop {a b : ℝ} (hb0 : 0 < b) (hba : b < a) (ha1 : a < 1) :
    ∃ (α : ℝ), 1 / 2 ≤ α ∧ α < 1 ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (b : ℝ) ^ (Nat.ceil (α * (n : ℝ))) ≤ (a : ℝ) ^ n / Real.sqrt (n : ℝ) := by
  have h0a : 0 < a := lt_trans hb0 hba
  have hb1 : b < 1 := lt_trans hba ha1
  let la : ℝ := Real.log a
  let lb : ℝ := Real.log b
  have hlb_ne : lb ≠ 0 := by
    dsimp [lb]
    exact ne_of_lt (Real.log_neg hb0 hb1)
  have hlb_neg : lb < 0 := by
    dsimp [lb]; exact Real.log_neg hb0 hb1
  have hla_neg : la < 0 := by
    dsimp [la]; exact Real.log_neg h0a ha1
  have hlb_lt_la : lb < la := by
    dsimp [la, lb]
    exact Real.log_lt_log hb0 hba
  let α : ℝ := (la + lb) / (2 * lb)
  have hα_ge : 1 / 2 ≤ α := by
    have hd : 0 < la / (2 * lb) := div_pos_of_neg_of_neg hla_neg (by linarith)
    have hcalc : α - 1 / 2 = la / (2 * lb) := by
      dsimp [α]
      field_simp [hlb_ne]
      ring
    linarith
  have hα_lt : α < 1 := by
    have hnum : 0 < la - lb := by linarith
    have hd : (la - lb) / (2 * lb) < 0 := div_neg_of_pos_of_neg hnum (by linarith)
    have hcalc : α - 1 = (la - lb) / (2 * lb) := by
      dsimp [α]
      field_simp [hlb_ne]
      ring
    linarith
  have hα_lb : α * lb = (la + lb) / 2 := by
    dsimp [α]
    field_simp [hlb_ne]
  let c : ℝ := la - lb
  have hc : 0 < c := by dsimp [c]; linarith
  obtain ⟨N, hN1, hlogN⟩ := eventually_log_le_mul hc
  refine ⟨α, hα_ge, hα_lt, N, ?_⟩
  intro n hn
  set m : ℕ := Nat.ceil (α * (n : ℝ)) with hm_def
  have hn1 : (1 : ℕ) ≤ n := le_trans hN1 hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1)
  have hlog : Real.log (n : ℝ) ≤ c * (n : ℝ) := hlogN n hn
  have hα_nonneg : 0 ≤ α := by linarith [hα_ge]
  have hxnonneg : 0 ≤ α * (n : ℝ) := mul_nonneg hα_nonneg (le_of_lt hnpos)
  have hmge : α * (n : ℝ) ≤ (m : ℝ) := by
    rw [hm_def]
    exact Nat.le_ceil (α * (n : ℝ))
  have hmul_le : (m : ℝ) * lb ≤ (α * (n : ℝ)) * lb :=
    mul_le_mul_of_nonpos_right hmge (le_of_lt hlb_neg)
  have hpowb : (b : ℝ) ^ m = Real.exp ((m : ℝ) * lb) := by
    rw [Real.exp_nat_mul lb m]
    dsimp [lb]
    rw [Real.exp_log hb0]
  have hpow_a : (a : ℝ) ^ n = Real.exp ((n : ℝ) * la) := by
    rw [Real.exp_nat_mul la n]
    dsimp [la]
    rw [Real.exp_log h0a]
  have hs_exp : Real.sqrt (n : ℝ) = Real.exp ((1 / 2) * Real.log (n : ℝ)) := by
    have hn0le : 0 ≤ (n : ℝ) := le_of_lt hnpos
    calc
      Real.sqrt (n : ℝ) = Real.exp (Real.log (Real.sqrt (n : ℝ))) :=
        (Real.exp_log (Real.sqrt_pos.mpr hnpos)).symm
      _ = Real.exp ((1 / 2) * Real.log (n : ℝ)) := by
        congr 1
        rw [Real.log_sqrt hn0le]
        ring
  have hhalf : (1 / 2) * Real.log (n : ℝ) ≤ (n : ℝ) * (c / 2) := by
    calc
      (1 / 2) * Real.log (n : ℝ) ≤ (1 / 2) * (c * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ = (n : ℝ) * (c / 2) := by ring
  have heq : (α * (n : ℝ)) * lb + (n : ℝ) * (c / 2) = (n : ℝ) * la := by
    have hswap : (α * (n : ℝ)) * lb = (n : ℝ) * (α * lb) := by ring
    calc
      (α * (n : ℝ)) * lb + (n : ℝ) * (c / 2) = (n : ℝ) * (α * lb) + (n : ℝ) * (c / 2) := by rw [hswap]
      _ = (n : ℝ) * ((la + lb) / 2) + (n : ℝ) * (c / 2) := by rw [hα_lb]
      _ = (n : ℝ) * la := by
        dsimp [c]
        ring
  have hexp : (α * (n : ℝ)) * lb + (1 / 2) * Real.log (n : ℝ) ≤ (n : ℝ) * la := by
    calc
      (α * (n : ℝ)) * lb + (1 / 2) * Real.log (n : ℝ)
          = (1 / 2) * Real.log (n : ℝ) + (α * (n : ℝ)) * lb := by ring
      _ ≤ (n : ℝ) * (c / 2) + (α * (n : ℝ)) * lb :=
        add_le_add_left hhalf ((α * (n : ℝ)) * lb)
      _ = (α * (n : ℝ)) * lb + (n : ℝ) * (c / 2) := by ring
      _ = (n : ℝ) * la := heq
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  rw [le_div_iff₀ hs]
  calc
    (b : ℝ) ^ m * Real.sqrt (n : ℝ)
        = Real.exp ((m : ℝ) * lb) * Real.sqrt (n : ℝ) := by rw [hpowb]
    _ = Real.exp ((m : ℝ) * lb) * Real.exp ((1 / 2) * Real.log (n : ℝ)) := by rw [hs_exp]
    _ = Real.exp ((m : ℝ) * lb + (1 / 2) * Real.log (n : ℝ)) := by rw [Real.exp_add]
    _ ≤ Real.exp ((α * (n : ℝ)) * lb + (1 / 2) * Real.log (n : ℝ)) :=
      Real.exp_le_exp.2 (add_le_add_left hmul_le ((1 / 2) * Real.log (n : ℝ)))
    _ ≤ Real.exp ((n : ℝ) * la) := Real.exp_le_exp.2 hexp
    _ = (a : ℝ) ^ n := hpow_a.symm

end Commons.Analysis.Real