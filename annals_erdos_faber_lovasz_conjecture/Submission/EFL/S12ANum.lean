import Submission.EFL.S12Params

/-!
# §12: the numeric side conditions of the Type A branch

This module fixes the constants of the Type A branch of §12 as
`ρ = σ/2`, `ρ_abs = σ/4`, `ε = σ³/10⁴²`, `κ = 1/2` and `γ = γ₁`, where `σ` and
`γ₁` are the constants produced by `s12_step1` (with `γ₁ ≤ σ¹⁰/10²⁵⁰`), and
collects *all* the numeric facts the assembly of the Type A branch needs into
the structure `S12ANum`, which is available for all sufficiently large `n`.

The constants are chosen so that

* `√γ ≪ ρε` (the bound `(eqn:bound_prev_col)`) -- here `√γ ≤ σ⁵/10¹²⁵` while
  `ρε = σ⁴/(4·10⁴²)`;
* `ε ≪ ρ` and `ε^{1/3} = σ/10¹⁴ ≪ ρ` (the requirement of `cor:optcol`, used in
  the Type A₂ case).

Since all the assertions are comparisons between explicit constants times
powers of `σ ≤ 10⁻²⁴`, they reduce to elementary arithmetic.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical
open Commons.Analysis.Real

noncomputable section

variable {n : ℕ}

/-! ## Elementary bounds on the constants

All the constant-level assertions of the Type A branch compare explicit
constants times powers of `σ`; the three lemmas below reduce them to the
elementary monotonicity `σ ^ k ≤ σ ^ j` (`j ≤ k`, `0 < σ ≤ 1`). -/

/-- `√γ ≤ σ⁵/10¹²⁵` when `γ ≤ σ¹⁰/10²⁵⁰`. -/
private lemma sqrt_gamma_le {γ σ : ℝ} (hσ0 : 0 < σ) (hγ0 : 0 < γ)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) : Real.sqrt γ ≤ σ ^ 5 / 10 ^ 125 := by
  have h2 : γ ≤ (σ ^ 5 / 10 ^ 125) ^ 2 := by
    have h3 : ((σ ^ 5 / 10 ^ 125) ^ 2 : ℝ) = σ ^ 10 / 10 ^ 250 := by ring
    linarith [hγσ, h3.le]
  exact calc Real.sqrt γ ≤ Real.sqrt ((σ ^ 5 / 10 ^ 125) ^ 2) := Real.sqrt_le_sqrt h2
    _ = σ ^ 5 / 10 ^ 125 := Real.sqrt_sq (by positivity)

/-- `γ ≤ σ^k · c` for `k ≤ 10` and `10⁻²⁵⁰ ≤ c`. -/
private lemma gamma_le_pow_mul {γ σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) {k : ℕ} (hk : k ≤ 10) {c : ℝ}
    (hc : (1 : ℝ) / 10 ^ 250 ≤ c) : γ ≤ σ ^ k * c := by
  calc γ ≤ σ ^ 10 / 10 ^ 250 := hγσ
    _ ≤ σ ^ k / 10 ^ 250 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hσ0.le hσ1 hk) (by positivity)
    _ = σ ^ k * ((1 : ℝ) / 10 ^ 250) := by ring
    _ ≤ σ ^ k * c := mul_le_mul_of_nonneg_left hc (by positivity)

/-- `√γ ≤ σ^k · c` for `k ≤ 5` and `10⁻¹²⁵ ≤ c`. -/
private lemma sqrt_le_pow_mul {γ σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hγ0 : 0 < γ)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) {k : ℕ} (hk : k ≤ 5) {c : ℝ}
    (hc : (1 : ℝ) / 10 ^ 125 ≤ c) : Real.sqrt γ ≤ σ ^ k * c := by
  have hs := sqrt_gamma_le hσ0 hγ0 hγσ
  calc Real.sqrt γ ≤ σ ^ 5 / 10 ^ 125 := hs
    _ ≤ σ ^ k / 10 ^ 125 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hσ0.le hσ1 hk) (by positivity)
    _ = σ ^ k * ((1 : ℝ) / 10 ^ 125) := by ring
    _ ≤ σ ^ k * c := mul_le_mul_of_nonneg_left hc (by positivity)

/-- `ξ ≤ σ^k · c` for `k ≤ 11` and `1/(4·10²⁵⁴) ≤ c`. -/
private lemma xi_le_pow_mul {ξ γ σ : ℝ} (hσ0 : 0 < σ) (hγ0 : 0 < γ) (hσ1 : σ ≤ 1)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) (hξle1 : ξ ≤ γ * (σ / 4) / 10 ^ 4) {k : ℕ} (hk : k ≤ 11)
    {c : ℝ} (hc : (1 : ℝ) / (4 * 10 ^ 254) ≤ c) : ξ ≤ σ ^ k * c := by
  have h1 : ξ ≤ σ ^ 11 * ((1 : ℝ) / (4 * 10 ^ 254)) := by
    calc ξ ≤ γ * (σ / 4) / 10 ^ 4 := hξle1
      _ ≤ (σ ^ 10 / 10 ^ 250) * (σ / 4) / 10 ^ 4 := by
          have hz : (0 : ℝ) ≤ (σ / 4) / 10 ^ 4 := by positivity
          have h := mul_le_mul_of_nonneg_right hγσ hz
          linarith only [h]
      _ = σ ^ 11 * ((1 : ℝ) / (4 * 10 ^ 254)) := by ring
  calc ξ ≤ σ ^ 11 * ((1 : ℝ) / (4 * 10 ^ 254)) := h1
    _ ≤ σ ^ k * ((1 : ℝ) / (4 * 10 ^ 254)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hσ0.le hσ1 hk) (by positivity)
    _ ≤ σ ^ k * c := mul_le_mul_of_nonneg_left hc (by positivity)


/-- **The numeric side conditions of the Type A branch of §12.**  All the
inequalities hold for all sufficiently large `n` (the threshold is produced by
`exists_S12ANum`); the constants are `ρ = σ/2`, `ρ_abs = σ/4`,
`ε = σ³/10⁴²`, `κ = 1/2`. -/
structure S12ANum (n : ℕ) (r₁ r₀ : ℕ) (β γ σ ξ ρabs : ℝ) : Prop where
  /-- the full numeric hierarchy of §12 -/
  hm : S12Margins n r₁ r₀ β γ (σ / 2) ρabs ξ (σ ^ 3 / 10 ^ 42) (1 / 2)
  /-- `ξ + 15γ^{1/2} ≤ ρε/2`: `(eqn:bound_prev_col)` / UC1 -/
  h15ρ : 15 * Real.sqrt γ + ξ ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) / 2
  /-- `30γ^{1/2} ≤ ρ`: the size of `C_final` is positive -/
  h30 : 30 * Real.sqrt γ ≤ σ / 2
  /-- `8 ≤ ρε r₀`: the numeric hypotheses `hUCnum2`/`hL1` -/
  h8r₀ : 8 ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (r₀ : ℝ)
  /-- `20ε ≤ ρ²`: the Type A₂ reservoir -/
  h20ε : 20 * (σ ^ 3 / 10 ^ 42) ≤ (σ / 2) ^ 2
  /-- `20ε + ξ ≤ ρ/2` -/
  h20εξ : 20 * (σ ^ 3 / 10 ^ 42) + ξ ≤ (σ / 2) / 2
  /-- `ξ ≤ ρ/2` -/
  hξε : ξ ≤ (σ / 2) / 2
  /-- `15ε ≤ ρ` -/
  h15ε : 15 * (σ ^ 3 / 10 ^ 42) ≤ σ / 2
  /-- `15γ^{1/2} + 20ε ≤ 22ε`: `(eqn:deficit)` -/
  hδle : 15 * Real.sqrt γ + 20 * (σ ^ 3 / 10 ^ 42) ≤ 22 * (σ ^ 3 / 10 ^ 42)
  /-- `24(22ε + ε^{1/3}) ≤ ρ/4`: the hypothesis of Corollary 10.13 -/
  hopt : 24 * (22 * (σ ^ 3 / 10 ^ 42) + σ / 10 ^ 14) ≤ (σ / 2) / 4
  /-- `8ε^{1/3} < ρ/4` -/
  hopt8 : 8 * (σ / 10 ^ 14) < (σ / 2) / 4
  /-- `0 < ε` -/
  hε0' : 0 < σ ^ 3 / 10 ^ 42
  /-- `0 < ε^{1/3}` -/
  hζ0 : 0 < σ / 10 ^ 14
  /-- `0 < 22ε` -/
  h22ε0 : 0 < 22 * (σ ^ 3 / 10 ^ 42)
  /-- `ρ/4 < 1` -/
  hρ4lt : (σ / 2) / 4 < 1
  /-- `10ξ + 1/n ≤ γ/2`: the sharp form of the absorber `R₁` -/
  hξsharp : 10 * ξ + 1 / (n : ℝ) ≤ γ / 2
  /-- `3 ≤ εn`: `s12_step3_typeA` -/
  hεn3 : 3 ≤ (σ ^ 3 / 10 ^ 42) * (n : ℝ)
  /-- `25 ≤ ρn`: the Type A₂ reservoir -/
  hρn25 : 25 ≤ (σ / 2) * (n : ℝ)
  /-- `2 ≤ ξn`: the Type A₂ reservoir -/
  hξn : 2 ≤ ξ * (n : ℝ)
  /-- `4 ≤ ρεn`: the final colour set is non-empty -/
  h4ρεn : 4 ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ)
  /-- `γ^{1/2} ≤ σ⁵/10¹²⁵`: `γ ≪ ρ,ε` -/
  hsqrtγ : Real.sqrt γ ≤ σ ^ 5 / 10 ^ 125
  /-- `ξ ≤ σ⁵/10¹²⁵`: `ξ ≪ γ,ρ,ε` -/
  hξle : ξ ≤ σ ^ 5 / 10 ^ 125
  /-- the C1/C3 numeric hypotheses of the nibble (`NibbleStatement`) -/
  hnum3 : (Dparam n (σ / 2) : ℝ) + (D'param (Dparam n (σ / 2)) γ : ℝ) +
      (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ)
  /-- `|C_large| ≤ D` (T1): `(1-σ)n ≤ D = ⌊(1-ρ)(n-1)⌋` -/
  hDlb : (1 - σ) * (n : ℝ) ≤ (Dparam n (σ / 2) : ℝ)

/-- **The numeric side conditions of the Type A branch hold eventually.**  With
the constant hierarchy of `s12_step1` (`γ ≤ σ¹⁰/10²⁵⁰ ≤ 1`,
`32 ≤ βr₁`, `r₁ < (γ/4)(r₀-1)`) there is `ξ > 0` and a threshold `N` such that
`S12ANum n r₁ r₀ β γ σ ξ` holds for every `n ≥ N`, together with the
constant-level inequalities listed in `S12ANum`. -/
theorem exists_S12ANum {r₁ r₀ : ℕ} {β γ σ ρabs : ℝ}
    (hρab : ρabs = σ / 2 ∨ ρabs = σ / 4)
    (hβ0 : 0 < β) (hγ0 : 0 < γ) (hσ0 : 0 < σ) (hβγ : β ≤ γ) (hβsq : β ≤ γ ^ 2 / 16)
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) (hσ24 : σ ≤ (10 : ℝ) ^ (-24 : ℤ))
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1)) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ, ∀ n ≥ N, S12ANum n r₁ r₀ β γ σ ξ ρabs := by
  have hσ1 : σ ≤ 1 := by norm_num at hσ24 ⊢; linarith
  have hσhalf : σ ≤ 1 / 2 := by norm_num at hσ24 ⊢; linarith
  have hσ4 : 0 < σ ^ 4 := by positivity
  -- ## the parameter `ξ`
  set ξ : ℝ := min (min (min (γ * (σ / 4)) β) (min γ ((σ / 2) * (σ ^ 3 / 10 ^ 42))))
    (min (2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) / 10 ^ 12) ((2 * γ) ^ 2 / 10 ^ 8)) / 10 ^ 4
    with hξdef
  have hξleA : ξ ≤ (min (min (γ * (σ / 4)) β)
      (min γ ((σ / 2) * (σ ^ 3 / 10 ^ 42)))) / 10 ^ 4 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hξle1 : ξ ≤ γ * (σ / 4) / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_left _ _) (min_le_left _ _)) (by norm_num))
  have hξle2 : ξ ≤ β / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num))
  have hξle3 : ξ ≤ γ / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num))
  have hξle4 : ξ ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num))
  have hξle5 : ξ ≤ ((2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42)) / 10 ^ 12) / 10 ^ 4 :=
    le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hξle6 : ξ ≤ ((2 * γ) ^ 2 / 10 ^ 8) / 10 ^ 4 :=
    le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hξε1 : 10 ^ 12 * ξ ≤ 2 * γ * ρabs * (σ ^ 3 / 10 ^ 42) := by
    have h1 : 10 ^ 12 * ξ ≤ 10 ^ 12 *
        (((2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42)) / 10 ^ 12) / 10 ^ 4) :=
      mul_le_mul_of_nonneg_left hξle5 (by norm_num)
    have h2 : 10 ^ 12 * (((2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42)) / 10 ^ 12) / 10 ^ 4) =
        2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) / 10 ^ 4 := by ring
    have hle : σ / 4 ≤ ρabs := by rcases hρab with h | h <;> linarith only [h, hσ0]
    have h3 : 2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) / 10 ^ 4 ≤
        2 * γ * ρabs * (σ ^ 3 / 10 ^ 42) := by
      have hpos : (0 : ℝ) ≤ 2 * γ * (σ ^ 3 / 10 ^ 42) := by positivity
      have hmul : 2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) ≤
          2 * γ * ρabs * (σ ^ 3 / 10 ^ 42) := by nlinarith only [hle, hpos]
      have hpos2 : (0 : ℝ) ≤ 2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) := by positivity
      have hdiv : 2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) / 10 ^ 4 ≤
          2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) := by linarith only [hpos2]
      linarith only [hmul, hdiv]
    linarith only [h1, h2.le, h2.ge, h3]
  have hξε2 : ξ ≤ (2 * γ) ^ 2 / 10 ^ 8 := by
    have h3 : (0 : ℝ) ≤ (2 * γ) ^ 2 / 10 ^ 8 := by positivity
    linarith only [hξle6, h3]
  have hξ0 : 0 < ξ := by
    have h1 : 0 < min (min (γ * (σ / 4)) β) (min γ ((σ / 2) * (σ ^ 3 / 10 ^ 42))) :=
      lt_min (lt_min (mul_pos hγ0 (by positivity)) hβ0) (lt_min hγ0 (by positivity))
    have h2 : 0 < min (2 * γ * (σ / 4) * (σ ^ 3 / 10 ^ 42) / 10 ^ 12)
        ((2 * γ) ^ 2 / 10 ^ 8) := lt_min (by positivity) (by positivity)
    rw [hξdef]
    exact div_pos (lt_min h1 h2) (by norm_num)
  have hξβ : 8 * ξ ≤ β / 2 := by linarith only [hξle2, hβ0]
  have hξγ : 10 * ξ ≤ γ / 2 := by linarith only [hξle3, hγ0]
  have hξγρ : 4000 * ξ ≤ (3 * γ / 2) * ρabs := by
    have h : 4000 * ξ ≤ 4000 * (γ * (σ / 4) / 10 ^ 4) := by linarith only [hξle1]
    have h2 : 4000 * (γ * (σ / 4) / 10 ^ 4) = γ * σ / 10 := by ring
    have h3 : γ * σ / 10 ≤ (3 * γ / 2) * ρabs := by
      rcases hρab with h | h
      · rw [h]; nlinarith only [hγ0, hσ0]
      · rw [h]; nlinarith only [hγ0, hσ0]
    rw [h2] at h
    linarith only [h, h3]
  -- ## `√γ ≤ σ⁵/10¹²⁵` and `ξ ≤ σ⁵/10¹²⁵`
  have hsqγ : Real.sqrt γ ≤ σ ^ 5 / 10 ^ 125 := by
    have h2 : γ ≤ (σ ^ 5 / 10 ^ 125) ^ 2 := by
      have h3 : ((σ ^ 5 / 10 ^ 125) ^ 2 : ℝ) = σ ^ 10 / 10 ^ 250 := by ring
      linarith [hγσ, h3.le]
    exact calc Real.sqrt γ ≤ Real.sqrt ((σ ^ 5 / 10 ^ 125) ^ 2) := Real.sqrt_le_sqrt h2
      _ = σ ^ 5 / 10 ^ 125 := Real.sqrt_sq (by positivity)
  have hξsmall : ξ ≤ σ ^ 5 / 10 ^ 125 := by
    have h1 : γ * (σ / 4) / 10 ^ 4 ≤ σ ^ 5 / 10 ^ 125 := by
      have h2 : γ * (σ / 4) / 10 ^ 4 ≤ (σ ^ 10 / 10 ^ 250) * (σ / 4) / 10 ^ 4 := by
        have hz : (0 : ℝ) < σ / 4 / 10 ^ 4 := by positivity
        nlinarith [hγσ, hz, hσ0]
      have h3 : (σ ^ 10 / 10 ^ 250) * (σ / 4) / 10 ^ 4 ≤ σ ^ 5 / 10 ^ 125 := by
        have he : (σ ^ 10 / 10 ^ 250) * (σ / 4) / 10 ^ 4 = σ ^ 11 / (4 * 10 ^ 254) := by ring
        rw [he, div_le_iff₀ (by norm_num : (0:ℝ) < 4 * 10 ^ 254),
          div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 125)]
        nlinarith [pow_le_pow_of_le_one hσ0.le hσ1 (show 6 ≤ 11 by norm_num), hσ0,
          pow_nonneg hσ0.le 5, pow_nonneg hσ0.le 11]
      linarith
    linarith
  -- ## constant-level inequalities
  have hsqγ : Real.sqrt γ ≤ σ ^ 5 / 10 ^ 125 := by
    have h2 : γ ≤ (σ ^ 5 / 10 ^ 125) ^ 2 := by
      have h3 : ((σ ^ 5 / 10 ^ 125) ^ 2 : ℝ) = σ ^ 10 / 10 ^ 250 := by ring
      linarith [hγσ, h3.le]
    exact calc Real.sqrt γ ≤ Real.sqrt ((σ ^ 5 / 10 ^ 125) ^ 2) := Real.sqrt_le_sqrt h2
      _ = σ ^ 5 / 10 ^ 125 := Real.sqrt_sq (by positivity)
  have hξsmall : ξ ≤ σ ^ 11 / (4 * 10 ^ 254) := by
    calc ξ ≤ γ * (σ / 4) / 10 ^ 4 := hξle1
      _ = γ * ((σ / 4) / 10 ^ 4) := by ring
      _ ≤ (σ ^ 10 / 10 ^ 250) * ((σ / 4) / 10 ^ 4) :=
          mul_le_mul_of_nonneg_right hγσ (by positivity)
      _ = σ ^ 11 / (4 * 10 ^ 254) := by ring
  have h54 : σ ^ 5 ≤ σ ^ 4 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
  have h53 : σ ^ 5 ≤ σ ^ 3 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
  have h51 : σ ^ 5 ≤ σ ^ 1 := by
    simpa using pow_le_pow_of_le_one hσ0.le hσ1 (show 1 ≤ 5 by norm_num)
  have h31 : σ ^ 3 ≤ σ ^ 1 := by
    simpa using pow_le_pow_of_le_one hσ0.le hσ1 (show 1 ≤ 3 by norm_num)
  have h32 : σ ^ 3 ≤ σ ^ 2 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
  have h101 : σ ^ 10 ≤ σ ^ 1 := by
    simpa using pow_le_pow_of_le_one hσ0.le hσ1 (show 1 ≤ 10 by norm_num)
  have h103 : σ ^ 10 ≤ σ ^ 3 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
  have h114 : σ ^ 11 ≤ σ ^ 4 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
  have h111 : σ ^ 11 ≤ σ ^ 1 := by
    simpa using pow_le_pow_of_le_one hσ0.le hσ1 (show 1 ≤ 11 by norm_num)
  have hP3 : (0 : ℝ) ≤ σ ^ 3 := pow_nonneg hσ0.le 3
  have hP4 : (0 : ℝ) ≤ σ ^ 4 := pow_nonneg hσ0.le 4
  have hP5 : (0 : ℝ) ≤ σ ^ 5 := pow_nonneg hσ0.le 5
  have hP1 : (0 : ℝ) ≤ σ ^ 1 := pow_nonneg hσ0.le 1
  have hQ125 : (0 : ℝ) < (1 : ℝ) / 10 ^ 125 := by norm_num
  have hQ42 : (0 : ℝ) < (1 : ℝ) / 10 ^ 42 := by norm_num
  have hQ254 : (0 : ℝ) < (1 : ℝ) / (4 * 10 ^ 254) := by norm_num
  have hQ14 : (0 : ℝ) < (1 : ℝ) / 10 ^ 14 := by norm_num
  have h15ρ : 15 * Real.sqrt γ + ξ ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) / 2 := by
    have hc1 : (15 : ℝ) * (1 / 10 ^ 125) ≤ (1 / 4) * (1 / 10 ^ 42) := by norm_num
    have hc2 : (1 : ℝ) * (1 / (4 * 10 ^ 254)) ≤ (1 / 4) * (1 / 10 ^ 42) := by norm_num
    have he : (σ / 2) * (σ ^ 3 / 10 ^ 42) / 2 = σ ^ 4 * ((1 : ℝ) / (4 * 10 ^ 42)) := by ring
    rw [he]
    nlinarith only [hsqγ, hξsmall, h54, h114, hc1, hc2, hP4, hP5, hQ125, hQ254]
  have h30 : 30 * Real.sqrt γ ≤ σ / 2 := by
    have hc1 : (30 : ℝ) * (1 / 10 ^ 125) ≤ (1 : ℝ) / 2 := by norm_num
    have he : σ / 2 = σ ^ 1 * ((1 : ℝ) / 2) := by ring
    rw [he]
    nlinarith only [hsqγ, h51, hc1, hP5, hQ125]
  have h8r₀ : 8 ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (r₀ : ℝ) := by
    have hr : (8 : ℝ) / γ < (r₀ : ℝ) := by
      have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁2
      have h3 : (8 : ℝ) < γ * ((r₀ : ℝ) - 1) := by nlinarith only [hr₀big, h2]
      rw [div_lt_iff₀ hγ0]
      linarith only [h3, hγ0, Nat.cast_nonneg (α := ℝ) r₀]
    have hcoef : (0 : ℝ) < (σ / 2) * (σ ^ 3 / 10 ^ 42) := by positivity
    have h1 : (σ / 2) * (σ ^ 3 / 10 ^ 42) * (8 / γ) <
        (σ / 2) * (σ ^ 3 / 10 ^ 42) * (r₀ : ℝ) :=
      mul_lt_mul_of_pos_left hr hcoef
    have h2 : 8 ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (8 / γ) := by
      rw [show (σ / 2) * (σ ^ 3 / 10 ^ 42) * (8 / γ) = 4 * σ ^ 4 / (10 ^ 42 * γ) by ring,
        le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 42 * γ)]
      have hc : (8 : ℝ) * (1 / 10 ^ 208) ≤ 4 := by norm_num
      have h4 : (8 : ℝ) * (10 ^ 42 * γ) ≤ 8 * (10 ^ 42 * (σ ^ 10 / 10 ^ 250)) := by
        nlinarith only [hγσ, hγ0]
      have h5 : 8 * (10 ^ 42 * (σ ^ 10 / 10 ^ 250)) ≤ 4 * σ ^ 4 := by
        have h10 : σ ^ 10 ≤ σ ^ 4 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
        have he : (8 : ℝ) * (10 ^ 42 * (σ ^ 10 / 10 ^ 250)) = σ ^ 10 * (8 / 10 ^ 208) := by
          ring
        rw [he]
        nlinarith only [h10, hP4, hc]
      linarith only [h4, h5]
    linarith only [h1, h2]
  have h20ε : 20 * (σ ^ 3 / 10 ^ 42) ≤ (σ / 2) ^ 2 := by
    have hc : (20 : ℝ) * (1 / 10 ^ 42) ≤ (1 / 4) := by norm_num
    have he : (σ / 2) ^ 2 = σ ^ 2 * ((1 : ℝ) / 4) := by ring
    rw [he]
    nlinarith only [h32, hc, hP3]
  have h20εξ : 20 * (σ ^ 3 / 10 ^ 42) + ξ ≤ (σ / 2) / 2 := by
    have hc1 : (20 : ℝ) * (1 / 10 ^ 42) ≤ (1 : ℝ) / 8 := by norm_num
    have hc2 : (1 : ℝ) * (1 / (4 * 10 ^ 254)) ≤ (1 : ℝ) / 8 := by norm_num
    have he : (σ / 2) / 2 = σ ^ 1 * ((1 : ℝ) / 4) := by ring
    rw [he]
    nlinarith only [h31, hξsmall, h111, hc1, hc2, hP3, hQ254]
  have hξε : ξ ≤ (σ / 2) / 2 := by
    have hc2 : (1 : ℝ) * (1 / (4 * 10 ^ 254)) ≤ (1 : ℝ) / 4 := by norm_num
    have he : (σ / 2) / 2 = σ ^ 1 * ((1 : ℝ) / 4) := by ring
    rw [he]
    nlinarith only [hξsmall, h111, hc2, hQ254, hP1]
  have h15ε : 15 * (σ ^ 3 / 10 ^ 42) ≤ σ / 2 := by
    have hc : (15 : ℝ) * (1 / 10 ^ 42) ≤ (1 : ℝ) / 2 := by norm_num
    have he : σ / 2 = σ ^ 1 * ((1 : ℝ) / 2) := by ring
    rw [he]
    nlinarith only [h31, hc, hP3]
  have hδle : 15 * Real.sqrt γ + 20 * (σ ^ 3 / 10 ^ 42) ≤ 22 * (σ ^ 3 / 10 ^ 42) := by
    have hc : (15 : ℝ) * (1 / 10 ^ 125) ≤ 2 * (1 / 10 ^ 42) := by norm_num
    nlinarith only [hsqγ, h53, hc, hP3, hP5, hQ125]
  have hopt : 24 * (22 * (σ ^ 3 / 10 ^ 42) + σ / 10 ^ 14) ≤ (σ / 2) / 4 := by
    have hc1 : 24 * (22 * (1 / 10 ^ 42)) ≤ (1 : ℝ) / 10 ^ 14 := by norm_num
    have hc2 : 24 * ((1 : ℝ) / 10 ^ 14) + (1 : ℝ) / 10 ^ 14 ≤ (1 : ℝ) / 8 := by norm_num
    have he : (σ / 2) / 4 = σ ^ 1 * ((1 : ℝ) / 8) := by ring
    rw [he]
    nlinarith only [h31, hc1, hc2, hP3]
  have hopt8 : 8 * (σ / 10 ^ 14) < (σ / 2) / 4 := by
    have he : (σ / 2) / 4 = σ ^ 1 * ((1 : ℝ) / 8) := by ring
    rw [he]
    nlinarith only [hσ0]
  have hρ4lt : (σ / 2) / 4 < 1 := by nlinarith only [hσ1, hσ0]
  have hε0' : 0 < σ ^ 3 / 10 ^ 42 := by positivity
  have hζ0 : 0 < σ / 10 ^ 14 := by positivity
  have h22ε0 : 0 < 22 * (σ ^ 3 / 10 ^ 42) := by positivity
  have hγ_le1 : γ ≤ 1 := by
    have h1 : σ ^ 10 / 10 ^ 250 ≤ 1 := by
      have h2 : σ ^ 10 ≤ 1 := pow_le_one₀ hσ0.le hσ1 (n := 10)
      linarith only [h2]
    linarith only [hγσ, h1]
  -- ## the corrected-margin constants
  have hγσ2 : γ ≤ σ ^ 2 / 10 ^ 14 := by
    have h := gamma_le_pow_mul hσ0 hσ1 hγσ (k := 2) (c := (1 : ℝ) / 10 ^ 14)
      (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hγρs : 10 ^ 6 * (2 * γ) ≤ ρabs := by
    have hle : σ / 4 ≤ ρabs := by rcases hρab with h | h <;> linarith only [h, hσ0]
    nlinarith only [hγσ2, hle, hσ0, hσ1]
  have hρabs_le : ρabs ≤ σ / 2 := by
    rcases hρab with h | h <;> linarith only [h, hσ0]
  have hε4000 : 4000 * (σ ^ 3 / 10 ^ 42) ≤ 1 := by
    have h3 : σ ^ 3 ≤ 1 := pow_le_one₀ hσ0.le hσ1 (n := 3)
    have hc : (4000 : ℝ) / 10 ^ 42 ≤ 1 := by norm_num
    nlinarith only [h3, hc, hP3]
  -- ## the `n`-large conditions
  have hγ_le1 : γ ≤ 1 := by
    have h1 : σ ^ 10 / 10 ^ 250 ≤ 1 := by
      have h2 : σ ^ 10 ≤ 1 := pow_le_one₀ hσ0.le hσ1 (n := 10)
      linarith only [h2]
    linarith only [hγσ, h1]
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (σ ^ 3 / 10 ^ 42) * (n : ℝ) :=
    eventually_const_le_mul_nat (c := σ ^ 3 / 10 ^ 42) (a := 2) (by positivity)
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, (8 : ℝ) ≤ β * (n : ℝ) :=
    eventually_const_le_mul_nat (c := β) (a := 8) hβ0
  have h3 : ∀ᶠ n : ℕ in Filter.atTop, (24 : ℝ) ≤ (β / 2) * (n : ℝ) :=
    eventually_const_le_mul_nat (c := β / 2) (a := 24) (by positivity)
  have h4 : ∀ᶠ n : ℕ in Filter.atTop, (100 : ℝ) ≤ (σ ^ 3 / 10 ^ 42) * (n : ℝ) :=
    eventually_const_le_mul_nat (c := σ ^ 3 / 10 ^ 42) (a := 100) (by positivity)
  have h5 : ∀ᶠ n : ℕ in Filter.atTop, (8 : ℝ) ≤ (n : ℝ) := by
    simpa using eventually_const_le_mul_nat (c := (1 : ℝ)) (a := 8) (by norm_num)
  have h6 : ∀ᶠ n : ℕ in Filter.atTop, 32 / β ^ 2 ≤ γ * (n : ℝ) / 2 := by
    have h := eventually_const_le_mul_nat (c := γ / 2) (a := 32 / β ^ 2) (by positivity)
    refine h.mono ?_
    intro n hn
    have he : γ / 2 * (n : ℝ) = γ * (n : ℝ) / 2 := by ring
    linarith [hn, he]
  have h7 : ∀ᶠ n : ℕ in Filter.atTop, (r₁ : ℝ) < β * (n : ℝ) / 4 := by
    have h := eventually_const_le_mul_nat (c := β / 4) (a := (r₁ : ℝ) + 1) (by positivity)
    refine h.mono ?_
    intro n hn
    have he : β / 4 * (n : ℝ) = β * (n : ℝ) / 4 := by ring
    linarith [hn, he]
  have h8 : ∀ᶠ n : ℕ in Filter.atTop, (2000 : ℝ) ≤ (3 * γ / 2) * (σ / 4) * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := (3 * γ / 2) * (σ / 4)) (a := 2000)
      (by positivity)
    refine h.mono ?_
    intro n hn
    have he : (3 * γ / 2) * (σ / 4) * (n : ℝ) = ((3 * γ / 2) * (σ / 4)) * (n : ℝ) := by ring
    linarith [hn, he]
  have h9 : ∀ᶠ n : ℕ in Filter.atTop,
      (β / 2) * (n : ℝ) / 2 ≤ (1 - σ / 2) * ((n : ℝ) - 1) := by
    have hc : (0 : ℝ) < 1 - σ / 2 - β / 4 := by nlinarith only [hσ1, hβγ, hγ_le1]
    have h := eventually_const_le_mul_nat (c := 1 - σ / 2 - β / 4) (a := 1 - σ / 2) hc
    refine h.mono ?_
    intro n hn
    nlinarith [hn]
  have h10 : ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ≤ 10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) := by
    have hc : (0 : ℝ) < 1 - σ / 2 := by nlinarith only [hσ1]
    have hs : (0 : ℝ) < Real.sqrt γ := Real.sqrt_pos.2 hγ0
    have hs10 : (0 : ℝ) < 10 * Real.sqrt γ := by linarith
    have hA : ∀ᶠ n : ℕ in Filter.atTop,
        (2 / (10 * Real.sqrt γ) + 1 + (1 - σ / 2)) ≤ (1 - σ / 2) * (n : ℝ) :=
      eventually_const_le_mul_nat (c := 1 - σ / 2) hc
    refine hA.mono ?_
    intro n hn
    have hle : 2 / (10 * Real.sqrt γ) + 1 ≤ (1 - σ / 2) * ((n : ℝ) - 1) := by
      have he : (1 - σ / 2) * ((n : ℝ) - 1) = (1 - σ / 2) * (n : ℝ) - (1 - σ / 2) := by ring
      linarith [hn, he]
    have hlt : 2 / (10 * Real.sqrt γ) < (Nat.floor ((1 - σ / 2) * ((n : ℝ) - 1)) : ℝ) := by
      have hf := Nat.sub_one_lt_floor ((1 - σ / 2) * ((n : ℝ) - 1))
      linarith [hle, hf]
    refine le_of_lt ?_
    calc (2 : ℝ) = 10 * Real.sqrt γ * (2 / (10 * Real.sqrt γ)) := by field_simp
      _ < 10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) := mul_lt_mul_of_pos_left hlt hs10
  have h11 : ∀ᶠ n : ℕ in Filter.atTop, (25 : ℝ) ≤ (σ / 2) * (n : ℝ) :=
    eventually_const_le_mul_nat (c := σ / 2) (a := 25) (by positivity)
  have h12 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ ξ * (n : ℝ) :=
    eventually_const_le_mul_nat (c := ξ) (a := 2) hξ0
  have h13 : ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ (σ / 2) * (n : ℝ) :=
    eventually_const_le_mul_nat (c := σ / 2) (a := 3) (by positivity)
  have h14 : ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ (σ / 2) * (n : ℝ) := h13
  have h16 : ∀ᶠ n : ℕ in Filter.atTop,
      (4 : ℝ) ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := (σ / 2) * (σ ^ 3 / 10 ^ 42)) (a := 4)
      (by positivity)
    refine h.mono ?_
    intro n hn
    have he : (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) =
        ((σ / 2) * (σ ^ 3 / 10 ^ 42)) * (n : ℝ) := by ring
    linarith only [hn, he.le, he.ge]
  -- `10ξ + 1/n ≤ γ/2`
  have h15 : ∀ᶠ n : ℕ in Filter.atTop, 10 * ξ + 1 / (n : ℝ) ≤ γ / 2 := by
    have hc : (0 : ℝ) < γ / 2 - 10 * ξ := by linarith only [hξle3, hγ0]
    have h := eventually_const_le_mul_nat (c := γ / 2 - 10 * ξ) (a := 1) hc
    refine h.mono ?_
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by
        by_contra hcon
        have : n = 0 := by omega
        subst this
        norm_num at hn
      exact_mod_cast this
    have h2 : 1 / (n : ℝ) ≤ γ / 2 - 10 * ξ := by
      rw [div_le_iff₀ hn0]
      linarith [hn]
    linarith
  have hρabs0' : (0 : ℝ) < ρabs := by
    rcases hρab with h | h <;> (rw [h]; positivity)
  have hnsup₁ : ∀ᶠ n : ℕ in Filter.atTop,
      10 ^ 100 ≤ 2 * γ * ρabs * (σ ^ 3 / 10 ^ 42) * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := 2 * γ * ρabs * (σ ^ 3 / 10 ^ 42))
      (a := 10 ^ 100) (by positivity)
    exact h.mono fun n hn => by linarith only [hn]
  have hnsup₂ : ∀ᶠ n : ℕ in Filter.atTop,
      10 ^ 400 * ((ρabs⁻¹) ^ 6 + ((2 * γ)⁻¹) ^ 16
        + (2 * γ * ρabs * (σ ^ 3 / 10 ^ 42))⁻¹
        + ((2 * γ * ρabs * (σ ^ 3 / 10 ^ 42))⁻¹) ^ 2 + (r₁ : ℝ)) ≤ (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := (1 : ℝ)) (a := 10 ^ 400 * ((ρabs⁻¹) ^ 6
      + ((2 * γ)⁻¹) ^ 16 + (2 * γ * ρabs * (σ ^ 3 / 10 ^ 42))⁻¹
      + ((2 * γ * ρabs * (σ ^ 3 / 10 ^ 42))⁻¹) ^ 2 + (r₁ : ℝ))) (by norm_num)
    simpa using h
  have hnum3 : ∀ᶠ n : ℕ in Filter.atTop,
      (Dparam n (σ / 2) : ℝ) + (D'param (Dparam n (σ / 2)) γ : ℝ) +
        (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ) := by
    refine (h6.and h5).mono ?_
    rintro n ⟨hk2, hn8⟩
    have hD : (Dparam n (σ / 2) : ℝ) ≤ (1 - σ / 2) * ((n : ℝ) - 1) := by
      rw [Dparam]
      exact Nat.floor_le (by nlinarith only [hσ1, hn8, Nat.cast_nonneg (α := ℝ) n])
    have hDn : (Dparam n (σ / 2) : ℝ) ≤ (n : ℝ) := by
      nlinarith only [hD, hσ1, hσ0, hn8, Nat.cast_nonneg (α := ℝ) n]
    have hD' : (D'param (Dparam n (σ / 2)) γ : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
      have h1 : (D'param (Dparam n (σ / 2)) γ : ℝ) ≤
          10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) := by
        rw [D'param]
        exact le_trans (Nat.floor_le (by positivity)) le_rfl
      have h2 : 10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hDn (by positivity)
      linarith [h1, h2]
    have hlin : 10 * Real.sqrt γ + 2 * γ + γ / 2 ≤ σ / 2 := by
      have hc1 : (10:ℝ) * (1 / 10 ^ 125) ≤ 1 / 6 := by norm_num
      have h1 : 10 * Real.sqrt γ ≤ σ / 6 := by
        have hs := sqrt_le_pow_mul hσ0 hσ1 hγ0 hγσ (k := 1) (c := (1 : ℝ) / 60)
          (by norm_num) (by norm_num)
        have hs' : Real.sqrt γ ≤ σ * ((1 : ℝ) / 60) := by simpa using hs
        linarith only [hs', hσ0]
      have h4 : γ ≤ σ / 16 := by
        have hg := gamma_le_pow_mul hσ0 hσ1 hγσ (k := 1) (c := (1 : ℝ) / 16)
          (by norm_num) (by norm_num)
        have hg' : γ ≤ σ * ((1 : ℝ) / 16) := by simpa using hg
        linarith only [hg']
      have h2 : 2 * γ + γ / 2 ≤ σ / 4 := by linarith only [h4, hσ0.le]
      linarith only [h1, h2, hσ0.le]
    nlinarith only [hD, hD', hk2, hlin, hσ1, hσ0, hn8, Nat.cast_nonneg (α := ℝ) n]
  have hDlb : ∀ᶠ n : ℕ in Filter.atTop,
      (1 - σ) * (n : ℝ) ≤ (Dparam n (σ / 2) : ℝ) := by
    refine (h13.and h5).mono ?_
    rintro n ⟨hn3, hn8⟩
    have hx : (1 : ℝ) ≤ (1 - σ / 2) * ((n : ℝ) - 1) := by
      have he : (1 - σ / 2) * ((n : ℝ) - 1) = (1 - σ / 2) * (n : ℝ) - (1 - σ / 2) := by ring
      nlinarith only [hn3, he, hσ1, hσ0, Nat.cast_nonneg (α := ℝ) n]
    have hlt := Nat.sub_one_lt_floor ((1 - σ / 2) * ((n : ℝ) - 1))
    have hlt' : (1 - σ / 2) * ((n : ℝ) - 1) - 1 < (Dparam n (σ / 2) : ℝ) := by
      rw [Dparam]; exact hlt
    have he2 : (1 - σ) * (n : ℝ) ≤ (1 - σ / 2) * ((n : ℝ) - 1) - 1 := by
      nlinarith only [hn3, hσ1, Nat.cast_nonneg (α := ℝ) n]
    linarith only [he2, hlt']
  -- ## the remaining constant-level facts
  have hγ2ε : γ ≤ 2 * (σ ^ 3 / 10 ^ 42) := by
    have hg := gamma_le_pow_mul hσ0 hσ1 hγσ (k := 3) (c := (2 : ℝ) / 10 ^ 42)
      (by norm_num) (by norm_num)
    rwa [show 2 * (σ ^ 3 / 10 ^ 42) = σ ^ 3 * ((2 : ℝ) / 10 ^ 42) by ring]
  have hεsmall : 1000 * (σ ^ 3 / 10 ^ 42) ≤ 1 := by
    have hc : (1000 : ℝ) * (1 / 10 ^ 42) ≤ 1 := by norm_num
    have h3 : σ ^ 3 ≤ 1 := pow_le_one₀ hσ0.le hσ1 (n := 3)
    nlinarith only [h3, hσ0, hc, hP3]
  have h8γ : 8 * γ ≤ σ ^ 3 / 10 ^ 42 := by
    have hg := gamma_le_pow_mul hσ0 hσ1 hγσ (k := 3) (c := (1 : ℝ) / (8 * 10 ^ 42))
      (by norm_num) (by norm_num)
    have he : σ ^ 3 / 10 ^ 42 = σ ^ 3 * (8 * ((1 : ℝ) / (8 * 10 ^ 42))) := by ring
    rw [he]
    linarith only [hg]
  have hβsq8 : 8 * β ≤ γ ^ 2 := by nlinarith only [hβsq, hγ0]
  have hρabs0 : 0 < ρabs := by
    rcases hρab with h | h <;> · rw [h]; positivity
  have hρabs1 : ρabs ≤ 1 := by
    rcases hρab with h | h
    · rw [h]; linarith only [hσhalf]
    · rw [h]; linarith only [hσhalf]
  have hγρabs : 1000 * (3 * γ / 2) ≤ ρabs * (σ ^ 3 / 10 ^ 42) := by
    rcases hρab with h | h
    · rw [h]
      have hg := gamma_le_pow_mul hσ0 hσ1 hγσ (k := 4) (c := (1 : ℝ) / (12000 * 10 ^ 42))
        (by norm_num) (by norm_num)
      have hεeq : σ / 2 * (σ ^ 3 / 10 ^ 42) = σ ^ 4 * ((1 : ℝ) / (2 * 10 ^ 42)) := by ring
      have hc : (1500 : ℝ) * ((1 : ℝ) / (12000 * 10 ^ 42)) ≤ 1 / (2 * 10 ^ 42) := by norm_num
      rw [hεeq]
      nlinarith only [hg, hc, pow_nonneg hσ0.le 4]
    · rw [h]
      have hg := gamma_le_pow_mul hσ0 hσ1 hγσ (k := 4) (c := (1 : ℝ) / (6000 * 10 ^ 42))
        (by norm_num) (by norm_num)
      have hεeq : σ / 4 * (σ ^ 3 / 10 ^ 42) = σ ^ 4 * ((1 : ℝ) / (4 * 10 ^ 42)) := by ring
      have hc : (1500 : ℝ) * ((1 : ℝ) / (6000 * 10 ^ 42)) ≤ 1 / (4 * 10 ^ 42) := by norm_num
      rw [hεeq]
      nlinarith only [hg, hc, pow_nonneg hσ0.le 4]
  have hL5in : 10 * Real.sqrt γ < 3 * (σ ^ 3 / 10 ^ 42) := by
    have hs := sqrt_le_pow_mul hσ0 hσ1 hγ0 hγσ (k := 3) (c := (1 : ℝ) / (2 * 10 ^ 43))
      (by norm_num) (by norm_num)
    have he : 10 * (σ ^ 3 * ((1 : ℝ) / (2 * 10 ^ 43))) = σ ^ 3 / (2 * 10 ^ 42) := by ring
    have hlt : σ ^ 3 / (2 * 10 ^ 42) < 3 * (σ ^ 3 / 10 ^ 42) := by
      have h := pow_pos hσ0 3
      nlinarith only [h]
    linarith only [hs, he.le, he.ge, hlt]
  have hr₀big' : 2 * (r₁ : ℝ) ≤ γ * ((r₀ : ℝ) - 1) := by
    have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁2
    nlinarith only [hr₀big, h2, hγ0]
  -- ## conclusion
  have hnξ' : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ ξ * (n : ℝ) :=
    eventually_const_le_mul_nat (c := ξ) (a := 1) hξ0
  have hall : ∀ᶠ n : ℕ in Filter.atTop, S12ANum n r₁ r₀ β γ σ ξ ρabs := by
    filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h15, h16, hnsup₁,
      hnsup₂, hnum3, hDlb, hnξ']
      with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12 hn15 hn16 hn100 hnsup hnnum
        hnDlb hnξ''
    have hnε100 : (100 : ℝ) ≤ (σ ^ 3 / 10 ^ 42) * (n : ℝ) := hn4
    have hnε2 : (2 : ℝ) ≤ (σ ^ 3 / 10 ^ 42) * (n : ℝ) := le_trans (by norm_num) hn4
    have hnε3 : (3 : ℝ) ≤ (σ ^ 3 / 10 ^ 42) * (n : ℝ) := le_trans (by norm_num) hn4
    have hnβn8 : (8 : ℝ) ≤ β * (n : ℝ) := hn2
    have hnβn6 : (6 : ℝ) ≤ β * (n : ℝ) := le_trans (by norm_num) hn2
    have hnbig' : (2000 : ℝ) ≤ (3 * γ / 2) * ρabs * (n : ℝ) := by
      rcases hρab with h | h
      · rw [h]; linarith only [hn8]
      · rw [h]; exact hn8
    exact
      { hm := S12Margins_of (n := n) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ)
          (ρ := σ / 2) (ρ_abs := ρabs) (ε := σ ^ 3 / 10 ^ 42) (ξ := ξ)
          hβ0 hγ0 (by positivity)
          hρabs0 hε0' hr₁2 hr₀2 hr₁r₀ (by linarith only [hσhalf, hσ0]) hγ_le1 hβγ hβsq8
          hβ4 hγρs hρabs_le
          hγ2ε hεsmall hε4000 h8γ hγρabs hρabs1 (by linarith only [hβr1])
          hr₁β₀ hr₀big' hL5in hnε2 hnβn8 hn6 hn7 hnbig' hn3 hn10 hnε100
          (by exact_mod_cast hn5) hnβn6
          (by linarith only [hn9]) hξ0 hξβ hξγ hξγρ hnξ'' hξε1 hξε2 hn100 hnsup
        h15ρ := h15ρ
        h30 := h30
        h8r₀ := h8r₀
        h20ε := h20ε
        h20εξ := h20εξ
        hξε := hξε
        h15ε := h15ε
        hδle := hδle
        hopt := hopt
        hopt8 := hopt8
        hε0' := hε0'
        hζ0 := hζ0
        h22ε0 := h22ε0
        hρ4lt := hρ4lt
        hξsharp := hn15
        hεn3 := hnε3
        hρn25 := hn11
        hξn := hn12
        h4ρεn := hn16
        hsqrtγ := hsqγ
        hξle := by
          have h1 : σ ^ 11 / (4 * 10 ^ 254) ≤ σ ^ 5 / 10 ^ 125 := by
            rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4 * 10 ^ 254),
              div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 125)]
            have h6 : σ ^ 11 ≤ σ ^ 5 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
            nlinarith only [h6, hP5]
          linarith only [hξsmall, h1]
        hnum3 := hnnum
        hDlb := hnDlb }
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  exact ⟨ξ, hξ0, N, fun n hn => hN n hn⟩

/-! ## The numerical margins of the Leftover Lemma for the Type A constants -/

/-- **The `LeftoverMargins` bundle for the Type A constants.**  With
`ρ = σ/2`, `ρ_abs ∈ {σ/2, σ/4}`, `ε = σ³/10⁴²` and the smallness
`γ ≤ σ¹⁰/10²⁵⁰`, `√γ ≤ σ⁵/10¹²⁵`, `10ξ ≤ γ/2`, the margin conditions of the
Leftover Lemma hold for all large `n`. -/
theorem exists_leftoverMargins_A (hK : KahnStatement) {r₁ : ℕ} {σ γ ξ : ℝ}
    (hσ0 : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hγ0 : 0 < γ) (hγσ : γ ≤ σ ^ 10 / 10 ^ 250)
    (hξ0 : 0 < ξ) (hξsharp : 10 * ξ ≤ γ / 2) (hsqrtγ : Real.sqrt γ ≤ σ ^ 5 / 10 ^ 125)
    {ρabs : ℝ} (hρab : ρabs = σ / 2 ∨ ρabs = σ / 4) :
    ∃ N : ℕ, ∀ n ≥ N, LeftoverMargins n r₁ γ (σ / 2) ρabs (σ ^ 3 / 10 ^ 42) ξ := by
  classical
  have hσ1 : σ ≤ 1 := le_trans hσhalf (by norm_num)
  have hγ100 : γ ≤ 1 / 100 := by
    have h2 : σ ^ 10 ≤ 1 := pow_le_one₀ (le_of_lt hσ0) hσ1 (n := 10)
    have h3 : σ ^ 10 / 10 ^ 250 ≤ 1 / 100 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 250)]
      have h4 : (1 / 100 : ℝ) * 10 ^ 250 = 10 ^ 248 := by norm_num
      rw [h4]
      linarith only [h2, show (1 : ℝ) ≤ 10 ^ 248 by norm_num]
    linarith only [hγσ, h3]
  have hξle : 4000 * ξ ≤ 200 * γ := by linarith only [hξsharp]
  have hσ5le : σ ^ 5 ≤ σ ^ 4 := by
    have h6 : σ ^ 5 = σ ^ 4 * σ := by ring
    rw [h6]
    nlinarith only [hσ1, show (0 : ℝ) ≤ σ ^ 4 by positivity]
  have hsmall : 10 ^ 4 * Real.sqrt γ ≤ ρabs * (σ ^ 3 / 10 ^ 42) := by
    have h2 : (10 : ℝ) ^ 4 * (σ ^ 5 / 10 ^ 125) ≤ ρabs * (σ ^ 3 / 10 ^ 42) := by
      rcases hρab with rfl | rfl
      · rw [show (10 : ℝ) ^ 4 * (σ ^ 5 / 10 ^ 125)
              = σ ^ 5 * ((10 : ℝ) ^ 4 / 10 ^ 125) by ring,
            show (σ / 2) * (σ ^ 3 / 10 ^ 42) = σ ^ 4 * (1 / ((2 : ℝ) * 10 ^ 42)) by ring]
        have hc : (10 : ℝ) ^ 4 / 10 ^ 125 ≤ 1 / (2 * 10 ^ 42) := by norm_num
        calc σ ^ 5 * ((10 : ℝ) ^ 4 / 10 ^ 125) ≤ σ ^ 4 * ((10 : ℝ) ^ 4 / 10 ^ 125) :=
              mul_le_mul_of_nonneg_right hσ5le (by norm_num)
          _ ≤ σ ^ 4 * (1 / ((2 : ℝ) * 10 ^ 42)) :=
              mul_le_mul_of_nonneg_left hc (by positivity)
      · rw [show (10 : ℝ) ^ 4 * (σ ^ 5 / 10 ^ 125)
              = σ ^ 5 * ((10 : ℝ) ^ 4 / 10 ^ 125) by ring,
            show (σ / 4) * (σ ^ 3 / 10 ^ 42) = σ ^ 4 * (1 / ((4 : ℝ) * 10 ^ 42)) by ring]
        have hc : (10 : ℝ) ^ 4 / 10 ^ 125 ≤ 1 / (4 * 10 ^ 42) := by norm_num
        calc σ ^ 5 * ((10 : ℝ) ^ 4 / 10 ^ 125) ≤ σ ^ 4 * ((10 : ℝ) ^ 4 / 10 ^ 125) :=
              mul_le_mul_of_nonneg_right hσ5le (by norm_num)
          _ ≤ σ ^ 4 * (1 / ((4 : ℝ) * 10 ^ 42)) :=
              mul_le_mul_of_nonneg_left hc (by positivity)
    linarith only [hsqrtγ, h2]
  have hξsmall : 4000 * ξ ≤ Real.sqrt γ * ρabs := by
    have hsqrt800 : Real.sqrt γ ≤ σ / 800 := by
      have h1 : σ ^ 5 / 10 ^ 125 ≤ σ / 800 := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 125) (by norm_num : (0 : ℝ) < 800)]
        have h3 : σ ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hσ0) hσ1 (n := 4)
        have h5 : σ ^ 5 * 800 = σ * (σ ^ 4 * 800) := by ring
        rw [h5]
        have h6 : σ ^ 4 * 800 ≤ 10 ^ 125 := by
          nlinarith only [h3, show (800 : ℝ) ≤ 10 ^ 125 by norm_num]
        exact mul_le_mul_of_nonneg_left h6 (le_of_lt hσ0)
      linarith only [hsqrtγ, h1]
    have h200 : 200 * Real.sqrt γ ≤ ρabs := by
      have h3 : 200 * Real.sqrt γ ≤ 200 * (σ / 800) :=
        mul_le_mul_of_nonneg_left hsqrt800 (by norm_num)
      have h4 : (200 : ℝ) * (σ / 800) = σ / 4 := by ring
      rcases hρab with rfl | rfl
      · linarith only [h3, h4, hσ0]
      · linarith only [h3, h4]
    have h6 : 200 * γ ≤ Real.sqrt γ * ρabs := by
      have hs : Real.sqrt γ * Real.sqrt γ = γ := by
        have h := Real.sq_sqrt (le_of_lt hγ0)
        nlinarith only [h]
      have h8 := mul_le_mul_of_nonneg_right h200 (Real.sqrt_nonneg γ)
      nlinarith only [h8, hs]
    linarith only [hξle, h6]
  have hρabs0 : 0 < ρabs := by rcases hρab with rfl | rfl <;> positivity
  have hρabs1 : ρabs ≤ 1 := by
    rcases hρab with rfl | rfl
    · linarith only [hσhalf]
    · linarith only [hσhalf]
  refine exists_leftoverMargins hK (r₁ := r₁) (ρ := σ / 2) (ρ_abs := ρabs)
    (ε := σ ^ 3 / 10 ^ 42) hγ0 hγ100 (by positivity)
    (by linarith only [hσhalf]) hρabs0 hρabs1 (by positivity) ?_ hξ0 hsmall hξsmall
  have h3 : σ ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt hσ0) hσ1 (n := 3)
  linarith only [h3]

end

end ErdosFaberLovaszConjecture
