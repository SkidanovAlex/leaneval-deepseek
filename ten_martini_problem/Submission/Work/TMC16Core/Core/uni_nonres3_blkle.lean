import Mathlib
import Submission.Work.TMC16Core.Core.sum_Dnr_blocks

namespace Work.TMC16Core.Core

/-! ## The block-to-range summation step of `uni_nonres3`

`hblk` bounds the logarithm sum over one `L`-block with the (unique) minimal point
removed, uniformly in the block position and the phase `ξ`.  Here we sum that
estimate over the `k` consecutive blocks of an interval of length `k·L`, with an
*arbitrary* point `d` removed instead of the block minima.

Two elementary facts make this work:

* `log |sin x| ≤ 0` for every `x`, so deleting the minimum `k₀` of a block only
  makes the block sum *larger*: dropping `k₀` (pushing the sum up by `-log|sin k₀| ≥ 0`)
  is absorbed by any other deletion, whose value `log |sin d|` is at most
  `log |sin k₀|` whenever `sin k₀ ≠ 0`.
* the block decomposition `sum_blocks` of an integer interval into `k` blocks of
  length `L`. -/

/-- `log |sin x| ≤ 0`, since `0 ≤ |sin x| ≤ 1`. -/
lemma log_abs_sin_nonpos (x : ℝ) : Real.log |Real.sin x| ≤ 0 := by
  rcases eq_or_ne (Real.sin x) 0 with h | h
  · simp [h]
  · have hpos : 0 < |Real.sin x| := abs_pos.mpr h
    have hle : |Real.sin x| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [Real.neg_one_le_sin x], Real.sin_le_one x⟩
    exact Real.log_nonpos hpos.le hle

/-- Monotonicity of `log |sin ·|` at a non-zero value: if `sin a ≠ 0` and
`|sin a| ≤ |sin b|` then `log |sin a| ≤ log |sin b|` (the second sine is then
automatically non-zero). -/
lemma log_abs_sin_mono {a b : ℝ} (ha : Real.sin a ≠ 0)
    (h : |Real.sin a| ≤ |Real.sin b|) :
    Real.log |Real.sin a| ≤ Real.log |Real.sin b| := by
  have hb : Real.sin b ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h
    exact ha (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  exact Real.log_le_log (abs_pos.mpr ha) h

/-- **The single-block bound with an arbitrary removed point.**  Whatever `d` is,
summing `log |sin (π (ξ + i α))|` over the block `[p, p+L-1]` except at `d` is at
most `-(L-1) log 2 + 32 log L`, provided no *other* point of the block is a zero of
the sine. -/
lemma blk_bound {L : ℕ} {α ξ : ℝ} {p d : ℤ} (hL : 1 ≤ L)
    (hblk : ∀ (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    (hnz : ∀ i ∈ Finset.Icc p (p + (L : ℤ) - 1), i ≠ d →
      Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) :
    ∑ i ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase d,
        Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
      ≤ -(((L : ℝ) - 1) * Real.log 2) + 32 * Real.log (L : ℝ) := by
  set B : Finset ℤ := Finset.Icc p (p + (L : ℤ) - 1) with hB
  set f : ℤ → ℝ := fun i => Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))| with hf
  have hne : B.Nonempty := by
    refine ⟨p, ?_⟩
    rw [hB, Finset.mem_Icc]
    have : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    omega
  obtain ⟨k₀, hk₀, hmin⟩ :=
    Finset.exists_min_image B (fun k => |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) hne
  have hb := hblk k₀ hk₀ (fun k hk => hmin k hk)
  have hS : ∑ k ∈ B.erase k₀, f k ≤ -(((L : ℝ) - 1) * Real.log 2) + 32 * Real.log (L : ℝ) := by
    have h2 := (abs_le.mp hb).2
    simp only [hf] at h2
    linarith
  have hcomp : ∑ i ∈ B.erase d, f i ≤ ∑ i ∈ B.erase k₀, f i := by
    rcases eq_or_ne d k₀ with hd | hd
    · rw [hd]
    · by_cases hdB : d ∈ B
      · have hkd : f k₀ ≤ f d := by
          have hk0nz : Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α)) ≠ 0 :=
            hnz k₀ (hB ▸ hk₀) (Ne.symm hd)
          simp only [hf]
          exact log_abs_sin_mono hk0nz (hmin d hdB)
        have h1 := Finset.sum_erase_add B f hdB
        have h2 := Finset.sum_erase_add B f hk₀
        linarith
      · have he : B.erase d = B := Finset.erase_eq_of_notMem hdB
        rw [he]
        have h1 := Finset.sum_erase_add B f hk₀
        have hk0le : f k₀ ≤ 0 := by
          simp only [hf]; exact log_abs_sin_nonpos _
        linarith
  linarith [hcomp, hS]

theorem uni_nonres3_blkle {L : ℕ} {α ξ : ℝ} (hL : 1 ≤ L)
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ)) :
    ∀ (u : ℤ) (k : ℕ) (d : ℤ),
      (∀ i ∈ Finset.Icc u (u + (k : ℤ) * (L : ℤ) - 1), i ≠ d →
        Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ (Finset.Icc u (u + (k : ℤ) * (L : ℤ) - 1)).erase d,
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ (k : ℝ) * (-(((L : ℝ) - 1) * Real.log 2) + 32 * Real.log (L : ℝ)) := by
  intro u k d h
  have hm : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  rw [sum_blocks u (L : ℤ) hm k d
    (fun i => Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)]
  have hstep : ∀ t ∈ Finset.range k,
      ∑ i ∈ (Finset.Icc (u + (t : ℤ) * (L : ℤ))
          (u + (t : ℤ) * (L : ℤ) + (L : ℤ) - 1)).erase d,
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -(((L : ℝ) - 1) * Real.log 2) + 32 * Real.log (L : ℝ) := by
    intro t ht
    rw [Finset.mem_range] at ht
    refine blk_bound (α := α) (ξ := ξ) (p := u + (t : ℤ) * (L : ℤ)) (d := d) hL
      (fun k₀ hk₀ hmin => hblk (u + (t : ℤ) * (L : ℤ)) k₀ hk₀ hmin) ?_
    intro i hi hid
    refine h i ?_ hid
    rw [Finset.mem_Icc] at hi ⊢
    obtain ⟨h1, h2⟩ := hi
    have ht1 : ((t : ℤ) + 1) * (L : ℤ) ≤ (k : ℤ) * (L : ℤ) := by
      have htk : (t : ℤ) + 1 ≤ (k : ℤ) := by omega
      exact mul_le_mul_of_nonneg_right htk (by exact_mod_cast Nat.zero_le L)
    constructor <;> nlinarith [h1, h2, ht1]
  calc ∑ t ∈ Finset.range k,
        ∑ i ∈ (Finset.Icc (u + (t : ℤ) * (L : ℤ))
            (u + (t : ℤ) * (L : ℤ) + (L : ℤ) - 1)).erase d,
            Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
      ≤ ∑ t ∈ Finset.range k, (-(((L : ℝ) - 1) * Real.log 2) + 32 * Real.log (L : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = (k : ℝ) * (-(((L : ℝ) - 1) * Real.log 2) + 32 * Real.log (L : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Work.TMC16Core.Core
