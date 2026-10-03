import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

/-!
# The good-major-arcs condition at the model scale `uScale ρ L`

This file proves that the Ionescu–Wainger good-major-arcs condition `m-small`
(`Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k`, i.e. `k ≤ -Cρ · 2^{ρl}`) holds
**unconditionally at the model scale** `k = -(uScale ρ L)` and `k = -(2 · uScale ρ L)`
(`uScale ρ L = ⌊2^{2ρL}⌋`, `Work.KMTAreas.A7.uScale`), as soon as the height `l` is dominated by the
scale `L` and `L` is large enough.

The whole content is the elementary lower bound

`Cρ · 2^{ρl} ≤ uScale ρ L`  (`const_mul_rpow_le_uScale`),

valid whenever `l ≤ L` and `2^{ρL} ≥ 2 Cρ + 1`: writing `y = 2^{ρL}`, one has
`2^{ρl} ≤ y` and `uScale ρ L = ⌊y²⌋ ≥ y² - 1 ≥ Cρ · y ≥ Cρ · 2^{ρl}`, the middle step because
`y ≥ 2Cρ + 1` and `y ≥ 1` give `y(y - Cρ) ≥ 1`.  Both `GoodMajorArcs` conditions then follow
(the one at `-(2 · uScale)` being the weaker, since `uScale ρ L ≥ 0`).

This is the "large-scale" half of the non-aliasing verification: the good-major-arcs condition
holds *away from the origin*, and the accompanying constant `B` depends only on `ρ` and `Cρ`.
Compare `Work.KMTAreas.A7.goodMajorArcs_uScale`, which proves the same estimate with the two
hypotheses in the other order (`L₀ ≤ L`, `l ≤ L`) but only for `-(2 · uScale ρ L)`.
-/

namespace Work.KMTPlan.A6Clean

/-- **The scale count dominates `Cρ · 2^{ρl}` once `L` is large and `l ≤ L`.**
Explicitly, for `B` satisfying `2^{ρB} ≥ 2Cρ + 1` (which exists because `2^ρ > 1`) and all
`l ≤ L` with `B ≤ L`, one has `Cρ · 2^{ρl} ≤ uScale ρ L = ⌊2^{2ρL}⌋`. -/
private theorem const_mul_rpow_le_uScale (ρ : ℝ) (hρ : 0 < ρ) (Cρ : ℝ) (hCρ : 0 < Cρ) :
    ∃ B : ℕ, ∀ l L : ℕ, l ≤ L → B ≤ L →
      Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
  -- `2^ρ > 1`, so the powers `2^{ρL}` are unbounded.
  have h2ρ : (1 : ℝ) < (2 : ℝ) ^ ρ := Real.one_lt_rpow (by norm_num) hρ
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℕ, 2 * Cρ + 1 ≤ (2 : ℝ) ^ (ρ * (L₀ : ℝ)) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x := (2 * Cρ + 1 : ℝ)) (y := (2 : ℝ) ^ ρ) h2ρ
    refine ⟨n, le_of_lt ?_⟩
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hn
  refine ⟨L₀, ?_⟩
  intro l L hl hL0L
  -- Monotonicity in `L`: `y := 2^{ρL} ≥ 2^{ρL₀} ≥ 2Cρ + 1`.
  have hy_ge : 2 * Cρ + 1 ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    calc 2 * Cρ + 1 ≤ (2 : ℝ) ^ (ρ * (L₀ : ℝ)) := hL₀
      _ ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          have hLL : (L₀ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL0L
          nlinarith [hρ]
  set y : ℝ := (2 : ℝ) ^ (ρ * (L : ℝ)) with hy
  have hyC : 2 * Cρ + 1 ≤ y := by rw [hy]; exact hy_ge
  have hy1 : 1 ≤ y := by linarith
  -- Monotonicity in `l`: `2^{ρl} ≤ y`.
  have hf : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ y := by
    rw [hy]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hl' : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
    nlinarith [hρ]
  -- The scale count is the floor of `y²`.
  have ha : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) = y * y := by
    rw [hy, show 2 * ρ * (L : ℝ) = ρ * (L : ℝ) + ρ * (L : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hu0 : Work.KMTAreas.A7.uScale ρ L = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
    simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat,
      Nat.cast_one, one_mul]
  have hu : (Work.KMTAreas.A7.uScale ρ L : ℝ) = ((⌊y * y⌋₊ : ℕ) : ℝ) := by rw [hu0, ha]
  have hfloor : y * y - 1 < ((⌊y * y⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (y * y); linarith
  have h1 : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ Cρ * y := mul_le_mul_of_nonneg_left hf hCρ.le
  -- `Cρ · y ≤ y² - 1`, since `y(y - Cρ) ≥ y · (Cρ + 1) ≥ 1`.
  have h2 : Cρ * y ≤ y * y - 1 := by nlinarith [hyC, hy1, hCρ]
  rw [hu]
  linarith

/-- **The good-major-arcs condition at the model scales `-(uScale ρ L)` and `-(2 uScale ρ L)`.**
There is `B` (depending only on `ρ` and `Cρ`) such that for every height `l` and scale `L` with
`l ≤ L` and `B ≤ L`, both pairs `(l, -(uScale ρ L))` and `(l, -(2 · uScale ρ L))` are good major
arcs. -/
theorem goodMajorArcs_uScale_of_large (ρ : ℝ) (hρ : 0 < ρ) (Cρ : ℝ) (hCρ : 0 < Cρ) :
    ∃ B : ℕ, ∀ l L : ℕ, l ≤ L → B ≤ L →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
          (-(Work.KMTAreas.A7.uScale ρ L : ℤ)) ∧
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
          (-(2 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
  obtain ⟨B, hB⟩ := const_mul_rpow_le_uScale ρ hρ Cρ hCρ
  refine ⟨B, fun l L hl hBL => ⟨?_, ?_⟩⟩
  · -- `-(uScale ρ L) ≤ -Cρ · 2^{ρl}` is exactly `Cρ · 2^{ρl} ≤ uScale ρ L`.
    have hkey := hB l L hl hBL
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
    have hcast : ((-(Work.KMTAreas.A7.uScale ρ L : ℤ) : ℤ) : ℝ)
        = -(Work.KMTAreas.A7.uScale ρ L : ℝ) := by push_cast; ring
    rw [hcast]
    linarith
  · -- The weaker condition at `-(2 · uScale ρ L)`, since `uScale ρ L ≥ 0`.
    have hkey := hB l L hl hBL
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
    have hcast : ((-(2 * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ)
        = -(2 * (Work.KMTAreas.A7.uScale ρ L : ℝ)) := by push_cast; ring
    rw [hcast]
    have h0 : (0 : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := Nat.cast_nonneg _
    linarith

end Work.KMTPlan.A6Clean
