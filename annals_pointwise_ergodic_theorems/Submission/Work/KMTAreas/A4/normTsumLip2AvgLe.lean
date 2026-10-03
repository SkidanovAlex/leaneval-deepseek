/-
# The trivial per-shift bound for the windowed polynomial average

`Work.KMTAreas.A4.normTsumLip2AvgLe` is the *elementary* bound on the `y`-sum of the `lip-2`
expansion at a fixed shift `s`:

`‖∑'_y h y · F (y + s) · lip2Avg N P M γ g s y‖
   ≤ N⁻¹ (∑_{N/2 < n ≤ N} ‖win M γ (n - s)‖) · ∑'_x ‖F x‖`

for `‖h‖ ≤ 1`, `‖g‖ ≤ 1` and `F ∈ ℓ¹`.  It needs no restriction on the shift `s` and no
smoothness of the window: expanding the definition of `lip2Avg` and using `‖g‖ ≤ 1` bounds every
summand by `‖win M γ (n - s)‖`, and the shift `y ↦ y + s` is a bijection of `ℤ`.

This is the counterpart of `Work.KMTAreas.A4.norm_lip2Avg_le` (which covers only the large-shift
regime `S < |s|`, where the sum of the window values is small) and of the per-shift triangle
inequality `Work.KMTAreas.A4.norm_tsum_mul_lip2Avg_le`.  Here the full window mass is kept, so the
estimate is *exact* in the worst case but finite for every `s`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2MainDefs
import Submission.Work.KMTAreas.A4.lip2Kernel

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **The per-shift `y`-sum of the `lip-2` expansion, bounded by the total window mass.**  For
`‖h‖ ≤ 1`, `‖g‖ ≤ 1` and `F ∈ ℓ¹`,

`‖∑'_y h y · F (y + s) · lip2Avg N P M γ g s y‖
   ≤ N⁻¹ (∑_{n ∈ (N/2, N]} ‖win M γ (n - s)‖) · ‖F‖₁`.

Indeed `lip2Avg N P M γ g s y = N⁻¹ ∑_{N/2 < n ≤ N} win M γ (n - s) g (y + P n)`, so the norm of
the average is at most `N⁻¹ ∑_n ‖win M γ (n - s)‖`; transferring the `y`-sum through the triangle
inequality, `‖h‖ ≤ 1` and the reindexing `y ↦ y + s` gives the claim. -/
theorem normTsumLip2AvgLe {N : ℕ} (P : Polynomial ℤ) {M : ℝ} (γ : Work.Analysis.InverseTheory.FreqCircle) {F g h : ℤ → ℂ} (s : ℤ) (hg : ∀ y : ℤ, ‖g y‖ ≤ 1) (hF : Summable (fun x : ℤ => ‖F x‖)) (hhb : ∀ y : ℤ, ‖h y‖ ≤ 1) : ‖∑' y : ℤ, h y * F (y + s) * Work.KMTAreas.A4.lip2Avg N P M γ g s y‖ ≤ ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖Work.KMTAreas.A4.win M γ ((n : ℤ) - s)‖) * (∑' x : ℤ, ‖F x‖) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hInv0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN0
  have hnorm : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ :=
    RCLike.norm_of_nonneg (K := ℂ) hInv0
  -- the uniform bound on the windowed average, with the full window mass
  have havg : ∀ y : ℤ, ‖lip2Avg N P M γ g s y‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖ := by
    intro y
    rw [lip2Avg, norm_mul, hnorm]
    refine mul_le_mul_of_nonneg_left ?_ hInv0
    calc ‖∑ n ∈ Finset.Ioc (N / 2) N, win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖
        ≤ ∑ n ∈ Finset.Ioc (N / 2) N,
            ‖win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖ := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)).trans (mul_one _).le
  have hmaj : Summable (fun y : ℤ => ‖F (y + s)‖) := hF.comp_injective (add_left_injective s)
  -- pointwise bound for the summands of the `y`-sum
  have hpt : ∀ y : ℤ, ‖h y * F (y + s) * lip2Avg N P M γ g s y‖
      ≤ ‖F (y + s)‖ * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖) := by
    intro y
    rw [norm_mul, norm_mul]
    calc ‖h y‖ * ‖F (y + s)‖ * ‖lip2Avg N P M γ g s y‖
        ≤ 1 * ‖F (y + s)‖ *
            ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hhb y) (norm_nonneg _)) (havg y)
            (norm_nonneg _) ?_
          exact mul_nonneg zero_le_one (norm_nonneg _)
      _ = ‖F (y + s)‖ * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖) := by
          ring
  have hsumm : Summable (fun y : ℤ => ‖h y * F (y + s) * lip2Avg N P M γ g s y‖) :=
    Summable.of_nonneg_of_le (fun y => norm_nonneg _) hpt (hmaj.mul_right _)
  calc ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
      ≤ ∑' y : ℤ, ‖h y * F (y + s) * lip2Avg N P M γ g s y‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' y : ℤ,
          ‖F (y + s)‖ * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖) :=
        Summable.tsum_le_tsum hpt hsumm (hmaj.mul_right _)
    _ = (∑' y : ℤ, ‖F (y + s)‖) *
          ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖) := tsum_mul_right
    _ = (∑' x : ℤ, ‖F x‖) *
          ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖) := by
        rw [← (Equiv.addRight s).tsum_eq (fun x : ℤ => ‖F x‖)]
        rfl
    _ = ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖) *
          (∑' x : ℤ, ‖F x‖) := by
        ring

end Work.KMTAreas.A4
