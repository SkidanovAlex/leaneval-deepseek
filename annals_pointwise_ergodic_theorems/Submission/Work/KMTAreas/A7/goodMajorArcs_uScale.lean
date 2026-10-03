import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger

/- **The arithmetic hypothesis of the fibre bound, verified at the model scale.**

`uScale ρ L = scaleCount 1 ρ L = ⌊2^{2ρL}⌋` (`Work.KMTAreas.A7.uScale`,
`Submission.Work.Analysis.EndVar.Defs`).  Since `GoodMajorArcs ρ Cρ l k` means `k ≤ -Cρ·2^{ρl}`
(`Work.Analysis.IonescuWainger.GoodMajorArcs`), the condition at `k = -(2·uScale ρ L)` is roughly
`2^{2ρL} ≥ Cρ 2^{ρl}/2`, which holds as soon as `l ≤ L` and `L` is large (because
`2·2^{2ρL} ≥ Cρ 2^{ρl}` follows from `2^{2ρL} ≥ 2^{2ρl} ≥ Cρ 2^{ρl}/2` for `2^{ρl} ≥ Cρ/2`).
Monotonicity of `scaleCount 1 ρ ·` in `L` is `Work.KMTAreas.A7.scaleCount_mono`-type. -/
theorem goodMajorArcs_uScale {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 0 < Cρ) :
    ∃ L₀ : ℕ, ∀ (L l : ℕ), L₀ ≤ L → l ≤ L →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
        (-(2 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
  -- `L₀` is chosen so that `2^{ρL₀} ≥ 2Cρ + 1`; the exponential `2^{ρL}` is unbounded because
  -- `2^ρ > 1`.
  have h2ρ : (1 : ℝ) < (2 : ℝ) ^ ρ := Real.one_lt_rpow (by norm_num) hρ
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℕ, 2 * Cρ + 1 ≤ (2 : ℝ) ^ (ρ * (L₀ : ℝ)) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x := (2 * Cρ + 1 : ℝ)) (y := (2 : ℝ) ^ ρ) h2ρ
    refine ⟨n, le_of_lt ?_⟩
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hn
  refine ⟨L₀, ?_⟩
  intro L l hL hl
  -- Monotonicity in `L`: `2^{ρL} ≥ 2^{ρL₀} ≥ 2Cρ + 1`.
  have hy_ge : 2 * Cρ + 1 ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    calc 2 * Cρ + 1 ≤ (2 : ℝ) ^ (ρ * (L₀ : ℝ)) := hL₀
      _ ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          have hLL : (L₀ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
          nlinarith [hρ]
  set y : ℝ := (2 : ℝ) ^ (ρ * (L : ℝ)) with hy
  have hyC : 2 * Cρ + 1 ≤ y := by rw [hy]; exact hy_ge
  have hy1 : 1 ≤ y := by linarith
  -- Monotonicity in `l`: `2^{ρl} ≤ 2^{ρL} = y`.
  have hf : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ y := by
    rw [hy]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hl' : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
    nlinarith [hρ]
  -- The scale count is the floor of `y²`.
  have ha : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) = y * y := by
    rw [hy, show 2 * ρ * (L : ℝ) = ρ * (L : ℝ) + ρ * (L : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hu0 : uScale ρ L = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
    simp only [uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat, Nat.cast_one, one_mul]
  have hu : (uScale ρ L : ℝ) = ((⌊y * y⌋₊ : ℕ) : ℝ) := by rw [hu0, ha]
  have hfloor : y * y - 1 < ((⌊y * y⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (y * y); linarith
  have hkey : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ ((⌊y * y⌋₊ : ℕ) : ℝ) := by
    have h1 : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ Cρ * y := mul_le_mul_of_nonneg_left hf hCρ.le
    have h2 : Cρ * y ≤ y * y - 1 := by nlinarith [hyC, hy1, hCρ]
    linarith
  unfold Work.Analysis.IonescuWainger.GoodMajorArcs
  have hcast : ((-(2 * (uScale ρ L : ℤ)) : ℤ) : ℝ) = -(2 * (uScale ρ L : ℝ)) := by
    push_cast; ring
  rw [hcast, hu]
  have hnn : (0 : ℝ) ≤ ((⌊y * y⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

end Work.KMTAreas.A7
