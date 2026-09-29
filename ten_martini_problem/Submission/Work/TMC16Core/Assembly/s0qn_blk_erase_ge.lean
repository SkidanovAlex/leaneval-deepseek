import Mathlib

namespace Work.TMC16Core.Assembly

/-- **Erasing a worst element can only lose the harmonic block bound by `log (2c)`.**

Suppose on the block `S = Icc p (p+L-1)` every value
`|sin (π (ξ + ((k + Lsh k·qr))·α))|` is at least `2c > 0`, and suppose that for every
*minimiser* `k₀` of that value on `S` the truncated logarithmic sum
`∑_{k ∈ S.erase k₀} log |sin(…)| + (L-1) log 2` is bounded by `B` in absolute value.
Then for an arbitrary integer `d` the analogous sum with `d` removed is still bounded
below by `-(L-1) log 2 - B + log (2c)`.

The point is that removing the minimiser leaves the *largest* possible truncated sum;
removing any other element `d` replaces (relative to the minimiser) the term `log (2c)`
by `log |sin d|` with `|sin d| ≤ 1`, whence one only loses the factor `2c`. -/
theorem s0qn_blk_erase_ge {L : ℕ} {α ξ c : ℝ} {p d qr : ℤ} {Lsh : ℤ → ℤ} {B : ℝ} (hL : 1 ≤ L)
    (hblk : ∀ (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * qr : ℤ) : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ B)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (hlo : ∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        2 * c ≤ |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|) :
    ∑ i ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase d,
        Real.log |Real.sin (Real.pi * (ξ + ((i + Lsh i * qr : ℤ) : ℝ) * α))|
      ≥ -(((L : ℝ) - 1) * Real.log 2) - B + Real.log (2 * c) := by
  -- Pick a minimiser `k₀` of `|sin (π (ξ + (k + Lsh k·qr) α))|` on the block.
  obtain ⟨k₀, hk₀S, hmin⟩ :=
    Finset.exists_min_image (Finset.Icc p (p + (L : ℤ) - 1))
      (fun k : ℤ => |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|)
      (by rw [Finset.nonempty_Icc]; omega)
  have hblk₀ := hblk k₀ hk₀S (fun k hk => hmin k hk)
  -- The truncated sum at the minimiser is bounded below.
  have hT : -(B + ((L : ℝ) - 1) * Real.log 2) ≤
      ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))| := by
    linarith [neg_le_of_abs_le hblk₀]
  -- The value at the minimiser dominates `2c`, hence its log dominates `log (2c)`.
  have hlog_lo : Real.log (2 * c) ≤
      Real.log |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * qr : ℤ) : ℝ) * α))| := by
    have h2c : 0 < 2 * c := by linarith
    exact Real.log_le_log h2c (hlo k₀ hk₀S)
  by_cases hd : d ∈ Finset.Icc p (p + (L : ℤ) - 1)
  · -- `d` lies in the block: its removal differs from the minimiser's by `log|sin d| ≤ 0`.
    have hfd := Finset.sum_erase_add (Finset.Icc p (p + (L : ℤ) - 1))
        (fun k => Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|) hd
    have hfk := Finset.sum_erase_add (Finset.Icc p (p + (L : ℤ) - 1))
        (fun k => Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|) hk₀S
    have hlog_d : Real.log |Real.sin (Real.pi * (ξ + ((d + Lsh d * qr : ℤ) : ℝ) * α))| ≤ 0 :=
      Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one _)
    linarith [hT, hlog_lo, hlog_d]
  · -- `d` lies outside the block: erasing it does nothing.
    rw [Finset.erase_eq_self.mpr hd]
    have hfk := Finset.sum_erase_add (Finset.Icc p (p + (L : ℤ) - 1))
        (fun k => Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|) hk₀S
    linarith [hT, hlog_lo]

end Work.TMC16Core.Assembly
