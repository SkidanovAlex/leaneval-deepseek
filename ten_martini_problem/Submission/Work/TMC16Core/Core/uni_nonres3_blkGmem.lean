import Mathlib

namespace Work.TMC16Core.Core

/-- **The block bound with an arbitrary removed point and an `L∞` lower bound.**

`hblk` bounds the logarithm sum over an `L`-block with the (unique) minimal point
`k₀` removed, uniformly in the block position and the phase `ξ`.  Here we delete an
*arbitrary* point `d` of the block instead, and we are given that the block is
`2c`-separated from `0`, i.e. `2c ≤ |sin (π (ξ + k α))|` throughout.

The two substitutions are:

* deleting the minimum `k₀` instead of `d` changes the (negated) sum by
  `-log |sin k₀| - (-log |sin d|) ≤ 0`, since `|sin k₀| ≤ |sin d|` and there is a
  single such difference — the block bounds `hblk` therefore still apply,
  and the direction of the `|·|` estimate that is used is the one giving an
  *upper* bound on the sum over `erase k₀`.
* the deleted point `d` contributes `-log |sin d| ≥ 0`, while the minimum `k₀`
  contributes `-log |sin k₀| ≤ -log (2c)`; combined with `2c ≤ |sin d|` this
  upgrades the constant `-log |sin k₀|` of `hblk` to the fixed constant
  `-log (2c)`. -/
theorem uni_nonres3_blkGmem {L : ℕ} {α ξ : ℝ} {p d : ℤ} (hL : 1 ≤ L)
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    (hd : d ∈ Finset.Icc p (p + (L : ℤ) - 1))
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (hlo : ∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        2 * c ≤ |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) :
    ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase d,
        -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      ≤ ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) - Real.log (2 * c) := by
  -- The block `B = Icc p (p + L - 1)` is non-empty.
  have hBne : (Finset.Icc p (p + (L : ℤ) - 1)).Nonempty := by
    rw [Finset.nonempty_Icc]
    have h1 : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    omega
  -- Choose a point `k₀` of the block minimising `|sin (π (ξ + k α))|`.
  obtain ⟨k₀, hk₀B, hk₀min⟩ :=
    Finset.exists_min_image (Finset.Icc p (p + (L : ℤ) - 1))
      (fun k => |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) hBne
  -- Apply the block hypothesis at that minimiser.
  have hb := hblk p k₀ hk₀B (fun k hk => hk₀min k hk)
  -- The lower half of `|·| ≤ 32 log L`: the block sum (with `k₀` removed) is not
  -- too negative.
  have hb_lo : -(32 * Real.log (L : ℝ)) ≤
      ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2 := (abs_le.mp hb).1
  -- Hence the *negated* block sum is bounded above.
  have hneg : ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
        -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      = -(∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) :=
    Finset.sum_neg_distrib (s := (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀)
      (fun k => Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|)
  have hSk : ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
        -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      ≤ 32 * Real.log (L : ℝ) + ((L : ℝ) - 1) * Real.log 2 := by
    linarith [hb_lo, hneg]
  -- The negated sum over `erase d` differs from that over `erase k₀` by a single
  -- term difference.
  have hRd : ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase d,
        -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      = ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + (-Real.log |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|
            - (-Real.log |Real.sin (Real.pi * (ξ + (d : ℝ) * α))|)) := by
    rw [Finset.sum_erase_eq_sub (s := Finset.Icc p (p + (L : ℤ) - 1))
          (f := fun k => -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) (a := d) hd,
        Finset.sum_erase_eq_sub (s := Finset.Icc p (p + (L : ℤ) - 1))
          (f := fun k => -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) (a := k₀) hk₀B]
    ring
  -- The minimiser contributes at most `-log (2c)`.
  have hfk₀ : -Real.log |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))| ≤ -Real.log (2 * c) := by
    have h := Real.log_le_log (show (0 : ℝ) < 2 * c by linarith [hc]) (hlo k₀ hk₀B)
    linarith
  -- The deleted point contributes at least `0`.
  have hfd : 0 ≤ -Real.log |Real.sin (Real.pi * (ξ + (d : ℝ) * α))| := by
    have h : Real.log |Real.sin (Real.pi * (ξ + (d : ℝ) * α))| ≤ 0 :=
      Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one _)
    linarith
  linarith [hRd, hSk, hfk₀, hfd]

end Work.TMC16Core.Core
