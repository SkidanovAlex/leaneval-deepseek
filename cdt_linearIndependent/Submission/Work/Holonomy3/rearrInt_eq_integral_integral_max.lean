import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.blocks
import Submission.Work.Holonomy3.lipschitzWith_max_integral
import Submission.Work.Holonomy3.patch_decomp

/-!
# The rearrangement integral is the double integral of `max (g s) (g t)`

The blockwise definition `rearrInt` of the paper's rearrangement integral equals
`∫₀¹∫₀¹ max (g(s), g(t))` for the patched function `g = patched w φ` (the paper's
`∫₀¹ 2t·g*(t) dt`).

The blocks `[blockStart w k, blockStart w k + w k)` (weights `w k = (γ_{k+1}-γ_k)/m`, positive and
summing to `1`) tile `[0,1)`, and on the `k`-th block `patched w φ` is `circleLog (φ k)` composed
with the affine rescaling of the block onto `[0,1]`.  Hence, applying the one-dimensional block
decomposition `integral_patched_eq_blocks` to the two variables in turn (the second with the parametrised
integrand `y ↦ ∫ t, max y (patched w φ t)`, which is continuous), the double integral of
`max (patched s) (patched t)` becomes the weighted double sum over pairs of blocks, i.e. `rearrInt`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan MeasureTheory Set
open scoped BigOperators

/-- The blockwise definition `rearrInt` of the rearrangement integral equals `∫₀¹∫₀¹ max (g(s), g(t))`
for the patched function `g` (`patched w φ`), i.e. the paper's `∫₀¹ 2t·g*(t) dt`. The weights
`w k = (γ_{k+1}-γ_k)/m` are positive and sum to `1`, and `circleLog (φ k)` is continuous on `[0,1]`
(so all the interval integrals are honest). -/
theorem rearrInt_eq_integral_integral_max {l : ℕ} (w : Fin (l + 1) → ℝ)
    (φ : Fin (l + 1) → ℂ → ℂ) (hw : ∀ k, 0 < w k) (hsum : ∑ k, w k = 1)
    (hcont : ∀ k, ContinuousOn (Submission.CDTPlan.circleLog (φ k)) (Set.Icc 0 1)) :
    Submission.CDTPlan.rearrInt w φ = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      max (patched w φ s) (patched w φ t) := by
  -- the function of one variable whose integral over `[0,1]` is the inner integral at `patched w φ s`
  set W : ℝ → ℝ := fun y => ∑ j : Fin (l + 1), w j * ∫ v in (0:ℝ)..1,
    max y (circleLog (φ j) v) with hWdef
  have hW : Continuous W := by
    rw [hWdef]
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact Continuous.const_mul
      ((lipschitzWith_max_integral (circleLog (φ j)) (hcont j)).continuous) (w j)
  -- Step 1: pointwise in `s`, the inner integral is `W (patched w φ s)`
  have step1 : ∀ s : ℝ,
      (∫ t in (0:ℝ)..1, max (patched w φ s) (patched w φ t)) = W (patched w φ s) := by
    intro s
    have hint : ∀ k : Fin (l + 1),
        IntervalIntegrable (fun u : ℝ => max (patched w φ s) (circleLog (φ k) u)) volume 0 1 := by
      intro k
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ContinuousOn.sup continuousOn_const (hcont k)
    have h := integral_patched_eq_blocks w φ hw hsum (fun z : ℝ => max (patched w φ s) z) hint
    rw [hWdef]
    exact h
  have h1 : (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, max (patched w φ s) (patched w φ t))
      = ∫ s in (0:ℝ)..1, W (patched w φ s) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with s _
    exact step1 s
  -- Step 2: apply the block decomposition to the `s`-integral, with test function `W`
  have h2 : (∫ s in (0:ℝ)..1, W (patched w φ s))
      = ∑ k : Fin (l + 1), w k * ∫ u in (0:ℝ)..1, W (circleLog (φ k) u) := by
    have hint : ∀ k : Fin (l + 1),
        IntervalIntegrable (fun u : ℝ => W (circleLog (φ k) u)) volume 0 1 := by
      intro k
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hW.comp_continuousOn (hcont k)
    exact integral_patched_eq_blocks w φ hw hsum W hint
  -- Step 3: expand `W` inside the `u`-integral and pull the finite sum out
  have h3 : ∀ i : Fin (l + 1), (∫ u in (0:ℝ)..1, W (circleLog (φ i) u))
      = ∑ j : Fin (l + 1), w j * ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1,
          max (circleLog (φ i) u) (circleLog (φ j) v) := by
    intro i
    have hWu : (fun u : ℝ => W (circleLog (φ i) u))
        = fun u => ∑ j : Fin (l + 1), w j * ∫ v in (0:ℝ)..1,
            max (circleLog (φ i) u) (circleLog (φ j) v) := by
      funext u
      rw [hWdef]
    rw [hWu, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [intervalIntegral.integral_const_mul]
    · intro j _
      refine IntervalIntegrable.const_mul ?_ (w j)
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ((lipschitzWith_max_integral (circleLog (φ j)) (hcont j)).continuous).comp_continuousOn
        (hcont i)
  have h4 : (∑ k : Fin (l + 1), w k * ∫ u in (0:ℝ)..1, W (circleLog (φ k) u))
      = ∑ i : Fin (l + 1), ∑ j : Fin (l + 1), w i * w j * ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1,
          max (circleLog (φ i) u) (circleLog (φ j) v) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h3 i, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- the double integral is `rearrInt`
  have hchain : (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, max (patched w φ s) (patched w φ t))
      = rearrInt w φ := by
    rw [h1, h2, h4]
    unfold rearrInt
    rfl
  exact hchain.symm

end Work.Holonomy3
