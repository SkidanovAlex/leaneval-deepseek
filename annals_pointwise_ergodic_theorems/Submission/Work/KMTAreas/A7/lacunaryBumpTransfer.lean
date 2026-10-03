/-
# The transfer from a uniform-in-signs bound to a variational estimate on `ℓᵖ(ℤ)`

This module contains the abstract transfer lemma which turns a **uniform-in-signs bound** for a
family of linear operators `T : ℕ → (ℤ → ℂ) → (ℤ → ℂ)` into a **variational estimate** for that
family:

if for every finite set `U` of indices and every choice of signs `ω : ℕ → Bool` the signed sum
`∑_{n ∈ U} ω n • T n f` is bounded on `ℓᵖ(ℤ)` by `M ‖f‖_{ℓᵖ}` (with one constant `M` for all
`U, ω`), then the `r`-variation, `2 < r`, of the family is bounded on `ℓᵖ(ℤ)` by `K M ‖f‖_{ℓᵖ}`
(with `K` depending only on `p, r`).

This is the *elementary half* of the paper's §8 argument for the high-frequency case: the pointwise
inequality `𝕍^r(a) ≤ (2 · 2^{1/r} + 1)(Σ_n ‖a n‖²)^{1/2}`
(`Work.KMTAreas.A7.variationalNorm_le_sqSum`) replaces the variation by the square function of the
*values*, and the Khintchine/Marcinkiewicz–Zygmund linearisation
(`Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns`) replaces that square function by the
uniform-in-signs bound.  The remaining input, in the application, is the Ionescu–Wainger multiplier
theorem applied to the signed symbols.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum
import Submission.Work.KMTAreas.A7.khintchine_sqSum_pointwise
import Submission.Work.KMTAreas.A7.rpow_iSup_ennreal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## Comparing the variational norm of a family with a tail of it, and with the clipped family -/

/-- **The variational norm of a tail.**  The reindexed family `n ↦ a (n + m)` (a tail of `a`) has
variational norm at most that of `a`: every chain of the tail is a chain of `a` (shifted by `m`),
and the pointwise suprema agree. -/
theorem variationalNorm_tail_le {r : NNReal} (m : ℕ) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => a (n + m))
      ≤ PointwiseErgodicTheorems.variationalNorm r a := by
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
    Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  refine add_le_add ?_ ?_
  · refine iSup_le (fun n => le_iSup (fun n => ‖a n‖ₑ) (n + m))
  · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    refine le_iSup_of_le J (le_iSup_of_le (fun i => N i + m) (le_iSup_of_le ?_ le_rfl))
    exact monotone_nat_of_le_succ (fun i => Nat.add_le_add_right (hN (Nat.le_succ i)) m)

/-- **The variational norm of a family with the first `m` indices clipped to zero.**  This is the
`core`-clipping step of the main estimate: `Hcl ρ C₀ … f n = if core … n then a n else 0` with
`core = {n | m ≤ n}` equals `fun n => if n < m then 0 else (tail a) (n - m)`, so the variational
norm of the clipped family is at most `3` times that of the *unclipped* family. -/
theorem variationalNorm_clipped_le {r : NNReal} (hr : 1 ≤ r) (m : ℕ) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => if n < m then 0 else a n)
      ≤ 3 * PointwiseErgodicTheorems.variationalNorm r a := by
  have h1 : (fun n => if n < m then (0 : ℂ) else a n)
      = (fun n => if n < m then 0 else (fun k => a (k + m)) (n - m)) := by
    funext n
    by_cases h : n < m
    · simp [h]
    · simp only [h, if_false]
      rw [Nat.sub_add_cancel (not_lt.mp h)]
  rw [h1]
  exact (Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr m
      (fun k => a (k + m))).trans (mul_le_mul_of_nonneg_left (variationalNorm_tail_le m a)
        (by norm_num : (0 : ℝ≥0∞) ≤ 3))

end Work.KMTAreas.A7
