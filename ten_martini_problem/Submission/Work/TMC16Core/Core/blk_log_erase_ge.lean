import Mathlib
import Submission.Work.TMC16Core.Core.uni_nonres3_blkG
import Submission.Work.TMC16Core.Core.uni_nonres3_blkGmem

namespace Work.TMC16Core.Core

/-- **One-sided log-sum lower bound over a block with an arbitrary point erased.**

Let `B = Icc p (p + L - 1)`.  `hblk` bounds the sum of `log |sin(π(ξ + k α))|` over `B` with
its *minimiser* `k₀` removed, two-sidedly, by `32 log L`; `hlo` gives the uniform lower bound
`2c ≤ |sin(π(ξ + k α))|` on the block, with `0 < c ≤ 1/2`.

Deleting an *arbitrary* point `d` (not necessarily a member of `B`) instead of `k₀` can only
raise the sum: the minimiser `k₀` contributes at worst `log (2c)` while any other point
contributes at least `log (2c)` as well, and in the worst case the erased point `d` is
precisely `k₀`, so one loses nothing beyond `log (2c)`.  Combined with the two-sided block
estimate (whose lower half is `∑_{B.erase k₀} log|sin| ≥ -(L-1) log 2 - 32 log L`) this gives
the stated one-sided bound. -/
theorem blk_log_erase_ge {L : ℕ} {α ξ c : ℝ} {p d : ℤ} (hL : 1 ≤ L)
    (hblk : ∀ (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (hlo : ∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        2 * c ≤ |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) :
    ∑ i ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase d,
        Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
      ≥ -(((L : ℝ) - 1) * Real.log 2) - 32 * Real.log (L : ℝ) + Real.log (2 * c) := by
  classical
  -- Abbreviate the block, the modulus `g` and its logarithm `f`.
  set B : Finset ℤ := Finset.Icc p (p + (L : ℤ) - 1) with hB
  set g : ℤ → ℝ := fun k => |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| with hg
  set f : ℤ → ℝ := fun k => Real.log (g k) with hf
  -- The block is non-empty.
  have hBne : B.Nonempty := by
    rw [hB, Finset.nonempty_Icc]
    have h1 : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    omega
  -- Choose a point `k₀` of the block minimising `|sin (π (ξ + k α))|`.
  obtain ⟨k₀, hk₀B, hk₀min⟩ := Finset.exists_min_image B g hBne
  -- Apply the block hypothesis at that minimiser, and take the lower half of `|·| ≤ 32 log L`.
  have hbk := hblk k₀ hk₀B (fun k hk => hk₀min k hk)
  have hb_lo := (abs_le.mp hbk).1
  have hT : -(32 * Real.log (L : ℝ)) - ((L : ℝ) - 1) * Real.log 2 ≤ ∑ k ∈ B.erase k₀, f k := by
    linarith
  -- `2c ≤ 1`, so `log (2c) ≤ 0`.
  have hlog2c : Real.log (2 * c) ≤ 0 :=
    Real.log_nonpos (by linarith [hc]) (by linarith [hc1])
  -- The minimiser contributes at least `log (2c)`.
  have hk0 : Real.log (2 * c) ≤ f k₀ := by
    rw [hf, hg]
    exact Real.log_le_log (by linarith [hc]) (hlo k₀ hk₀B)
  -- Split on whether the erased point `d` lies in the block.
  by_cases hd : d ∈ B
  · -- `d ∈ B`: peel off the `d`- and `k₀`-terms and compare.
    have hsplit_d := Finset.sum_erase_eq_sub (s := B) (f := f) hd
    have hsplit_k := Finset.sum_erase_eq_sub (s := B) (f := f) hk₀B
    have hfd_le : f d ≤ 0 := by
      rw [hf, hg]
      exact Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one _)
    have hstep : ∑ k ∈ B.erase d, f k ≥ ∑ k ∈ B.erase k₀, f k + Real.log (2 * c) := by
      rw [hsplit_d, hsplit_k]; linarith [hk0, hfd_le]
    linarith [hT, hstep]
  · -- `d ∉ B`: erasing it changes nothing, and the full sum is the `k₀`-erased sum plus `f k₀`.
    have hEr : B.erase d = B := Finset.erase_eq_of_notMem hd
    have hsplit_k : ∑ k ∈ B.erase k₀, f k + f k₀ = ∑ k ∈ B, f k :=
      Finset.sum_erase_add B f hk₀B
    rw [hEr]
    linarith [hT, hk0, hsplit_k]

end Work.TMC16Core.Core
