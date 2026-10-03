/-
# `lmax` is bounded in the non-Farey regime

The large-scale analysis of Theorem `varp` (Krause–Mirek–Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Annals of Math. 195 (2022), §8) splits the
admissible scales `N ∈ D` at the threshold `splitCut ρ L = 2^{2^{⌊2^{2ρL}⌋}}` (the "doubly
exponentially many scales" of the paper's `u = ⌊C₂ 2^{2ρl}⌋`).  The quantitative Shannon /
Farey-gap hypothesis of that analysis is

  `2^{k₁} · Q_{≤l₁} · 8 ≤ N`   (`Q_{≤l} = arithQ ρ l = lcm P_{≤l}`),

i.e. the packet band `2^{k₁}/N` sits below the Farey gap `1/Q_{≤l₁}` of the arithmetic frequency
set `(ℚ/ℤ)_{≤l₁}`.

This file proves the elementary arithmetic fact that makes the *complement* of that hypothesis
harmless: with `L = max (max l₁ l₂) (max k₁ k₂)`,

  `splitCut ρ L < N`  and  `N < 8 · 2^{k₁} · arithQ ρ l₁`   force   `L ≤ B(ρ)`,

for a bound `B(ρ)` depending on `ρ` alone.  So the non-Farey regime contains only *boundedly many*
scales `L`; its contribution can be absorbed into a `ρ`-dependent constant.

## Route

* `arithQ_le_rpow` — every element (hence the lcm) of the Ionescu–Wainger denominator set is at
  most `2^{C·2^l}`: this is `Work.Analysis.IonescuWainger.iwQl_le` plus
  `arithQ ρ l = iwQl ρ l`.
* `pow_dominates_linear` — `2^{2ρL}` eventually dominates any linear function.
* `splitCut_dominates` — consequently `splitCut ρ L = 2^{2^{⌊2^{2ρL}⌋}}` eventually dominates
  `8·2^L·2^{C·2^L}`; taking `log₂` this is the statement that `3 + L + C·2^L` is eventually below
  the doubly exponential `2^{⌊2^{2ρL}⌋}`.
* The two hypotheses then give
  `splitCut ρ L < N < 8·2^{k₁}·arithQ ρ l₁ ≤ 8·2^L·2^{C·2^L}`, and for `L > B(ρ)` this contradicts
  `splitCut_dominates`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger
open Filter Topology Work.Analysis.EndVar

/-! ## The Ionescu–Wainger denominator bound -/

/-- The common denominator `arithQ ρ l = max 1 (lcm P_{≤l})` of the Ionescu–Wainger arithmetic
frequency set `(ℚ/ℤ)_{≤l}` is at most `2^{C · 2^l}` for a constant `C = C(ρ)`. -/
theorem arithQ_le_rpow (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l, (arithQ ρ l : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ l) := by
  obtain ⟨C, hCpos, hC⟩ := iwQl_le hρ hρ1
  refine ⟨C, hCpos, fun l => ?_⟩
  have hpos : 0 < iwQl ρ l := iwQl_pos
  have hEq : arithQ ρ l = iwQl ρ l := max_eq_right (Nat.succ_le_of_lt hpos)
  rw [hEq, show (2 : ℝ) ^ l = (2 : ℝ) ^ (l : ℝ) from (Real.rpow_natCast 2 l).symm]
  exact hC l

/-! ## The asymptotic domination of the multiplicative loss by `splitCut` -/

/-- `2^{2ρL}` eventually dominates every linear function: for every `K : ℝ` there is `L₀` with
`L + K ≤ 2^{2ρL}` for all `L ≥ L₀`.  (Valid for every `ρ > 0`; `2ρL` is exponential in `L`.) -/
theorem pow_dominates_linear (ρ : ℝ) (hρ : 0 < ρ) (K : ℝ) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → (L : ℝ) + K ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
  set b : ℝ := (2 : ℝ) ^ (2 * ρ) with hbdef
  have hb1 : 1 < b := by
    rw [hbdef]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  -- `L / b^L → 0`
  have htend : Tendsto (fun L : ℕ => (L : ℝ) / b ^ L) atTop (𝓝 0) := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt 1 hb1
    simpa using h
  have hev : ∀ᶠ L : ℕ in atTop, (L : ℝ) / b ^ L < 1 / 2 :=
    (tendsto_order.1 htend).2 (1 / 2) (by norm_num)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 hev
  refine ⟨max L₁ ⌈K⌉₊, fun L hL => ?_⟩
  have hLL₁ : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hKL : K ≤ (L : ℝ) := by
    have h1 : K ≤ ((⌈K⌉₊ : ℕ) : ℝ) := Nat.le_ceil K
    have h2 : ((⌈K⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hL)
    linarith
  have h2L : 2 * (L : ℝ) < b ^ L := by
    have h := hL₁ L hLL₁
    have hbL : 0 < b ^ L := pow_pos hb0 L
    rw [div_lt_iff₀ hbL] at h
    linarith
  have hbL_eq : b ^ L = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    rw [hbdef, ← Real.rpow_natCast ((2 : ℝ) ^ (2 * ρ)) L,
      ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hbL_eq] at h2L
  linarith

/-- The scale-split threshold `splitCut ρ L = 2^{2^{⌊2^{2ρL}⌋}}` eventually dominates the loss
`8 · 2^L · 2^{C·2^L}`. -/
theorem splitCut_dominates (ρ : ℝ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 < C) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      8 * (2 : ℝ) ^ L * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) < (splitCut ρ L : ℝ) := by
  obtain ⟨L₀, hL₀⟩ := pow_dominates_linear ρ hρ (Real.logb 2 (C + 4) + 1)
  refine ⟨max L₀ 1, fun L hL => ?_⟩
  have hL₀L : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  -- put all powers in `rpow` form
  rw [show (2 : ℝ) ^ L = (2 : ℝ) ^ (L : ℝ) from (Real.rpow_natCast 2 L).symm]
  set y : ℝ := (2 : ℝ) ^ (2 * ρ * (L : ℝ)) with hydef
  have hdom : (L : ℝ) + (Real.logb 2 (C + 4) + 1) ≤ y := hL₀ L hL₀L
  have hC4 : 0 < C + 4 := by linarith
  -- `8 · 2^L ≤ 2^{4·2^L}`
  have hstep1 : 8 * (2 : ℝ) ^ (L : ℝ) ≤ (2 : ℝ) ^ (4 * (2 : ℝ) ^ (L : ℝ)) := by
    have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    have hbern : (1 : ℝ) + (L : ℝ) ≤ (2 : ℝ) ^ L := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) L
      have h2 : (1 : ℝ) + 1 = 2 := by norm_num
      rw [h2] at h
      simpa using h
    have hbern' : (1 : ℝ) + (L : ℝ) ≤ (2 : ℝ) ^ (L : ℝ) := by
      have h := hbern
      rwa [← Real.rpow_natCast (2 : ℝ) L] at h
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    calc 8 * (2 : ℝ) ^ (L : ℝ)
        = (2 : ℝ) ^ (3 : ℝ) * (2 : ℝ) ^ (L : ℝ) := by rw [h8]
      _ = (2 : ℝ) ^ (3 + (L : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (4 * (2 : ℝ) ^ (L : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by nlinarith [hbern', hLnn])
  -- `(C + 4) · 2^L ≤ 2^{y - 1}`
  have hstep3 : (C + 4) * (2 : ℝ) ^ (L : ℝ) ≤ (2 : ℝ) ^ (y - 1) := by
    have hlog : (2 : ℝ) ^ (Real.logb 2 (C + 4)) = C + 4 :=
      Real.rpow_logb (by norm_num) (by norm_num) hC4
    calc (C + 4) * (2 : ℝ) ^ (L : ℝ)
        = (2 : ℝ) ^ (Real.logb 2 (C + 4)) * (2 : ℝ) ^ (L : ℝ) := by rw [hlog]
      _ = (2 : ℝ) ^ (Real.logb 2 (C + 4) + (L : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (y - 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hdom])
  -- `y - 1 < ⌊y⌋₊`
  have hfloor : y - 1 < ((⌊y⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one y
    linarith
  have hstep4 : (2 : ℝ) ^ (y - 1) < (2 : ℝ) ^ (((⌊y⌋₊ : ℕ) : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hfloor
  -- identify `splitCut ρ L` with `2^{2^{⌊y⌋₊}}`
  have hsc' : scaleCount 1 ρ L = ⌊y⌋₊ := by
    rw [hydef]
    simp only [Work.Analysis.EndVar.scaleCount, Int.floor_toNat, Nat.cast_one, one_mul]
  have hsplit : (splitCut ρ L : ℝ) = (2 : ℝ) ^ ((2 : ℝ) ^ (((⌊y⌋₊ : ℕ) : ℝ))) := by
    have h1 : (splitCut ρ L : ℝ) =
        (2 : ℝ) ^ ((2 : ℝ) ^ (((scaleCount 1 ρ L : ℕ)) : ℝ)) := by
      unfold splitCut
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast (2 : ℝ) (2 ^ scaleCount 1 ρ L)]
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (scaleCount 1 ρ L)]
    rw [h1, hsc']
  calc 8 * (2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (C * (2 : ℝ) ^ (L : ℝ))
      ≤ (2 : ℝ) ^ (4 * (2 : ℝ) ^ (L : ℝ)) * (2 : ℝ) ^ (C * (2 : ℝ) ^ (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep1 (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((C + 4) * (2 : ℝ) ^ (L : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have : 4 * (2 : ℝ) ^ (L : ℝ) + C * (2 : ℝ) ^ (L : ℝ)
            = (C + 4) * (2 : ℝ) ^ (L : ℝ) := by ring
        rw [this]
    _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (y - 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hstep3
    _ < (2 : ℝ) ^ ((2 : ℝ) ^ (((⌊y⌋₊ : ℕ) : ℝ))) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hstep4
    _ = (splitCut ρ L : ℝ) := hsplit.symm

/-! ## The non-Farey regime is bounded -/

theorem lmax_le_of_not_farey (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℝ → ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N →
      ¬ ((2 : ℝ) ^ k₁ * (Work.KMTAreas.A7.arithQ ρ l₁ : ℝ) * 8 ≤ (N : ℝ)) →
      max (max l₁ l₂) (max k₁ k₂) ≤ B ρ := by
  obtain ⟨C, hCpos, hC⟩ := arithQ_le_rpow ρ hρ hρ1
  obtain ⟨L₀, hL₀⟩ := splitCut_dominates ρ hρ C hCpos
  refine ⟨fun _ => L₀, ?_⟩
  intro l₁ l₂ k₁ k₂ N hsplit hfarey
  set L : ℕ := max (max l₁ l₂) (max k₁ k₂) with hL
  change L ≤ L₀
  by_contra hcon
  have hBd : L₀ ≤ L := le_of_lt (not_le.mp hcon)
  have hd : 8 * (2 : ℝ) ^ L * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) < (splitCut ρ L : ℝ) :=
    hL₀ L hBd
  have hN1 : (splitCut ρ L : ℝ) < (N : ℝ) := by exact_mod_cast hsplit
  have hN2 : (N : ℝ) < (2 : ℝ) ^ k₁ * (arithQ ρ l₁ : ℝ) * 8 := not_le.mp hfarey
  have hkl : k₁ ≤ L := by
    rw [hL]; exact le_trans (le_max_left k₁ k₂) (le_max_right _ _)
  have hl1L : l₁ ≤ L := by
    rw [hL]; exact le_trans (le_max_left l₁ l₂) (le_max_left _ _)
  have hpow : (2 : ℝ) ^ k₁ ≤ (2 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hkl
  have harith : (arithQ ρ l₁ : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ L) := by
    refine le_trans (hC l₁) ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hl1L) hCpos.le
  have hcontra : (splitCut ρ L : ℝ) < (splitCut ρ L : ℝ) := by
    calc (splitCut ρ L : ℝ) < (N : ℝ) := hN1
      _ < (2 : ℝ) ^ k₁ * (arithQ ρ l₁ : ℝ) * 8 := hN2
      _ ≤ (2 : ℝ) ^ L * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) * 8 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 8)
          exact mul_le_mul hpow harith (Nat.cast_nonneg _) (by positivity)
      _ = 8 * (2 : ℝ) ^ L * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) := by ring
      _ < (splitCut ρ L : ℝ) := hd
  exact absurd hcontra (lt_irrefl _)

end Work.KMTAreas.A7
