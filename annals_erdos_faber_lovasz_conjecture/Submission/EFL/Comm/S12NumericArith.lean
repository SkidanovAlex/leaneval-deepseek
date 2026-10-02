import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

open Filter

/-!
# §12: the arithmetic lemmas of the parameter hierarchy

Verbatim ports (with narrow imports) of three commons lemmas
(`Commons.Analysis.Real.{one_sub_mul_add_one_le, floor_mul_sub_one_add_le,
le_floor_mul_sub_one}`) which the §12 assembly needs for the numeric discharge of
`S12Margins` and of the Type A/Type B hypotheses:

* `one_sub_mul_add_one_le`: `(1-σ)n + 1 ≤ (1-ρ)(n-1)` when `2ρ ≤ σ` and
  `σn ≥ 4` — the inequality behind `C_large ⊆ C_main` (i.e. (T1)) in Type A,
  using the paper's `ρ ≪ σ`;
* `floor_mul_sub_one_add_le`: the `hS₂num` inequality
  `⌊(1-ρ)(n-1)⌋ + 3γn/2 + 5 + 4εn ≤ (1-ρ)n + 5εn`;
* `le_floor_mul_sub_one`: `n/2 ≤ ⌊(1-ρ)(n-1)⌋` (the `n ≤ 2D` estimate).
-/

set_option autoImplicit false

namespace Commons.Analysis.Real

/-- Ported from `Submission/Commons/Analysis/Real/one_sub_mul_add_one_le.lean`. -/
theorem one_sub_mul_add_one_le {n : ℕ} {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 2 * ρ ≤ σ)
    (hn : 4 ≤ σ * (n : ℝ)) :
    (1 - σ) * (n : ℝ) + 1 ≤ (1 - ρ) * ((n : ℝ) - 1) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [hρ, hσ, hn, hn0]

/-- Ported from `Submission/Commons/Analysis/Real/floor_mul_sub_one_add_le.lean`. -/
theorem floor_mul_sub_one_add_le {n : ℕ} {γ ε ρ : ℝ} (hε0 : 0 < ε) (hγ0 : 0 ≤ γ)
    (hγε : 3 * γ ≤ ε) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) (hn : 100 ≤ ε * (n : ℝ)) :
    (Nat.floor ((1 - ρ) * ((n : ℝ) - 1)) : ℝ) + 3 * γ * (n : ℝ) / 2 + 5 + 4 * ε * (n : ℝ) ≤
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) := by
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn_gt : (0 : ℝ) < (n : ℝ) := by nlinarith [hn, hε0]
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    have : n ≠ 0 := by rintro rfl; simp at hn_gt
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr this)
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have h1ρ : (0 : ℝ) ≤ 1 - ρ := by linarith
  have hprod : (0 : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := mul_nonneg h1ρ hn1
  have hfl : (Nat.floor ((1 - ρ) * ((n : ℝ) - 1)) : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) :=
    Nat.floor_le hprod
  have h3 : 3 * γ * (n : ℝ) / 2 ≤ ε * (n : ℝ) / 2 := by nlinarith [hγε, hn_nonneg]
  nlinarith [hfl, h3, hn, hγ0, hρ0, hρ1]

/-- Ported from `Submission/Commons/Analysis/Real/le_floor_mul_sub_one.lean`. -/
theorem le_floor_mul_sub_one {n : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 4) (hn : 8 ≤ n) :
    (n : ℝ) / 2 ≤ (Nat.floor ((1 - ρ) * ((n : ℝ) - 1)) : ℝ) := by
  have hn7 : (7 : ℝ) ≤ (n : ℝ) := by
    have : (7 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hρ' : (3 : ℝ) / 4 ≤ 1 - ρ := by linarith
  have hmul : (3 : ℝ) / 4 * ((n : ℝ) - 1) ≤ (1 - ρ) * ((n : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hρ' hn1
  have hkey : (n : ℝ) / 2 + 1 ≤ (3 : ℝ) / 4 * ((n : ℝ) - 1) := by linarith
  have hx : (n : ℝ) / 2 + 1 ≤ (1 - ρ) * ((n : ℝ) - 1) := by linarith
  have hfloor := Nat.lt_floor_add_one ((1 - ρ) * ((n : ℝ) - 1))
  linarith

/-- Ported from `Submission/Commons/Analysis/Real/exists_thresholds_hierarchy_rho_eps.lean`:
for a constant hierarchy `β ≤ 1`, `γ ≤ 1`, `ρ ≤ 1/4`, `2ρ ≤ ε/2`, all the
`n`-large conditions of `S12Margins` hold for `n ≥ N`. -/
lemma eventually_const_le_mul_nat {c a : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, a ≤ c * (n : ℝ) := by
  have h : Filter.Tendsto (fun n : ℕ => c * (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  exact h.eventually_ge_atTop a

theorem exists_thresholds_hierarchy_rho_eps {β γ ρ ρ_abs ε : ℝ} (r₁ : ℕ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hρabs0 : 0 < ρ_abs) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hρlt : 2 * ρ ≤ ε / 2) :
    ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ≤ ε * (n : ℝ) ∧ (8 : ℝ) ≤ β * (n : ℝ) ∧ (6 : ℝ) ≤ β * (n : ℝ) ∧
      (24 : ℝ) ≤ (β / 2) * (n : ℝ) ∧ (100 : ℝ) ≤ ε * (n : ℝ) ∧ (8 : ℝ) ≤ (n : ℝ) ∧
      (32 / β ^ 2 ≤ γ * (n : ℝ) / 2) ∧ ((r₁ : ℝ) < β * (n : ℝ) / 4) ∧
      (2000 : ℝ) ≤ (3 * γ / 2) * ρ_abs * (n : ℝ) ∧
      (2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ)) ∧
      ((β / 2) * (n : ℝ) / 2 ≤ (1 - ρ) * ((n : ℝ) - 1)) ∧
      (2 ≤ 10 * Real.sqrt γ * (Nat.floor ((1 - ρ) * ((n : ℝ) - 1)) : ℝ)) := by
  rw [← Filter.eventually_atTop]
  have hA1 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ ε * (n : ℝ) :=
    eventually_const_le_mul_nat hε0
  have hA2 : ∀ᶠ n : ℕ in Filter.atTop, (8 : ℝ) ≤ β * (n : ℝ) :=
    eventually_const_le_mul_nat hβ0
  have hA3 : ∀ᶠ n : ℕ in Filter.atTop, (6 : ℝ) ≤ β * (n : ℝ) :=
    eventually_const_le_mul_nat hβ0
  have hA4 : ∀ᶠ n : ℕ in Filter.atTop, (24 : ℝ) ≤ (β / 2) * (n : ℝ) :=
    eventually_const_le_mul_nat (c := β / 2) (by linarith)
  have hA5 : ∀ᶠ n : ℕ in Filter.atTop, (100 : ℝ) ≤ ε * (n : ℝ) :=
    eventually_const_le_mul_nat hε0
  have hA6 : ∀ᶠ n : ℕ in Filter.atTop, (8 : ℝ) ≤ (n : ℝ) := by
    simpa using eventually_const_le_mul_nat (c := (1 : ℝ)) (a := 8) (by norm_num)
  have hA7 : ∀ᶠ n : ℕ in Filter.atTop, 32 / β ^ 2 ≤ γ * (n : ℝ) / 2 := by
    have h := eventually_const_le_mul_nat (c := γ / 2) (a := 32 / β ^ 2) (by linarith)
    refine h.mono ?_
    intro n hn
    have he : γ / 2 * (n : ℝ) = γ * (n : ℝ) / 2 := by ring
    linarith [hn, he]
  have hA8 : ∀ᶠ n : ℕ in Filter.atTop, (r₁ : ℝ) < β * (n : ℝ) / 4 := by
    have h := eventually_const_le_mul_nat (c := β / 4) (a := (r₁ : ℝ) + 1) (by linarith)
    refine h.mono ?_
    intro n hn
    have he : β / 4 * (n : ℝ) = β * (n : ℝ) / 4 := by ring
    linarith [hn, he]
  have hA9 : ∀ᶠ n : ℕ in Filter.atTop, (2000 : ℝ) ≤ (3 * γ / 2) * ρ_abs * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := (3 * γ / 2) * ρ_abs) (a := 2000)
      (mul_pos (by linarith) hρabs0)
    refine h.mono ?_
    intro n hn
    have he : (3 * γ / 2) * ρ_abs * (n : ℝ) = (3 * γ / 2 * ρ_abs) * (n : ℝ) := by ring
    linarith [hn, he]
  have hA10 : ∀ᶠ n : ℕ in Filter.atTop,
      2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ) := by
    have hc : (0 : ℝ) < ε - 2 * ρ := by linarith
    have h := eventually_const_le_mul_nat (c := ε - 2 * ρ) (a := 1 - 2 * ρ) hc
    refine h.mono ?_
    intro n hn
    nlinarith [hn]
  have hA11 : ∀ᶠ n : ℕ in Filter.atTop,
      (β / 2) * (n : ℝ) / 2 ≤ (1 - ρ) * ((n : ℝ) - 1) := by
    have hc : (0 : ℝ) < 1 - ρ - β / 4 := by linarith
    have h := eventually_const_le_mul_nat (c := 1 - ρ - β / 4) (a := 1 - ρ) hc
    refine h.mono ?_
    intro n hn
    nlinarith [hn]
  have hA12 : ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ 10 * Real.sqrt γ * (Nat.floor ((1 - ρ) * ((n : ℝ) - 1)) : ℝ) := by
    have hc : (0 : ℝ) < 1 - ρ := by linarith
    have hs : (0 : ℝ) < Real.sqrt γ := Real.sqrt_pos.2 hγ0
    have hs10 : (0 : ℝ) < 10 * Real.sqrt γ := by linarith
    have h1 : ∀ᶠ n : ℕ in Filter.atTop,
        (2 / (10 * Real.sqrt γ) + 1 + (1 - ρ)) ≤ (1 - ρ) * (n : ℝ) :=
      eventually_const_le_mul_nat (c := 1 - ρ) hc
    refine h1.mono ?_
    intro n hn
    have hle : 2 / (10 * Real.sqrt γ) + 1 ≤ (1 - ρ) * ((n : ℝ) - 1) := by
      have he : (1 - ρ) * ((n : ℝ) - 1) = (1 - ρ) * (n : ℝ) - (1 - ρ) := by ring
      linarith [hn, he]
    have hlt : 2 / (10 * Real.sqrt γ) < (Nat.floor ((1 - ρ) * ((n : ℝ) - 1)) : ℝ) := by
      have hf := Nat.sub_one_lt_floor ((1 - ρ) * ((n : ℝ) - 1))
      linarith [hle, hf]
    have hkey : (2 : ℝ) = 10 * Real.sqrt γ * (2 / (10 * Real.sqrt γ)) := by
      field_simp
    rw [hkey]
    exact (mul_lt_mul_of_pos_left hlt hs10).le
  filter_upwards [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12]
    with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12
  exact ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12⟩

end Commons.Analysis.Real
