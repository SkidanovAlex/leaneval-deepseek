/-
# Local `L¹`-convergence of mollifications

For a locally integrable `f : ℂ → ℂ`, a sequence of bump functions `φ n` at `0` with `rOut → 0`,
and a compact set `K`, the mollifications `(φ n).normed volume ⋆ f` converge to `f` in `L¹(K)`:

  `∫ z in K, ‖moll ((φ n).normed volume) f z - f z‖ → 0`.

The proof is the standard one: the pointwise bound `Work.MRMT.Weyl.norm_moll_sub_le` together with
Tonelli's theorem bounds the quantity of interest by
`∫ y, ρ y * ∫ z in K, ‖f (z - y) - f z‖`; by continuity of translation in `L¹` on compacts
(`Work.MRMT.Weyl.continuous_setIntegral_translate`) the function
`y ↦ ∫ z in K, ‖f (z + y) - f z‖` is continuous and vanishes at `0`, so the bump approximation
identity `ContDiffBump.convolution_tendsto_right_of_continuous` gives the result.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.moll_L1_aux
import Submission.Work.MRMT.Weyl.moll_setIntegral_le_swap
import Submission.Work.MRMT.Weyl.continuous_setIntegral_translate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

theorem moll_tendsto_L1_loc {f : ℂ → ℂ} (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0))
    {K : Set ℂ} (hK : IsCompact K) :
    Filter.Tendsto (fun n =>
        ∫ z in K, ‖Work.MRMT.Weyl.moll ((φ n).normed MeasureTheory.volume) f z - f z‖)
      Filter.atTop (nhds 0) := by
  set Ĥ : ℂ → ℝ := fun y => ∫ z in K, ‖f (z + y) - f z‖ with hĤ
  have hĤcont : Continuous Ĥ := continuous_setIntegral_translate hf hK
  have hĤ0 : Ĥ 0 = 0 := by simp [hĤ]
  have hconv : Tendsto (fun n => convolution ((φ n).normed volume) Ĥ (ContinuousLinearMap.lsmul ℝ ℝ)
      volume 0) atTop (𝓝 (Ĥ 0)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℂ)) hφ hĤcont 0
  -- Identify the convolution with the expression produced by the swap estimate.
  have hident : ∀ n, convolution ((φ n).normed volume) Ĥ (ContinuousLinearMap.lsmul ℝ ℝ) volume 0
      = ∫ y, (φ n).normed volume y * (∫ z in K, ‖f (z - y) - f z‖) := by
    intro n
    rw [MeasureTheory.convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hĤ, sub_eq_add_neg, zero_add]
  -- The swap estimate for each `n`.
  have hbound : ∀ n, (∫ z in K, ‖moll ((φ n).normed volume) f z - f z‖)
      ≤ ∫ y, (φ n).normed volume y * (∫ z in K, ‖f (z - y) - f z‖) := by
    intro n
    refine moll_setIntegral_le_swap hf ?_ ?_ ?_ ?_ hK
    · exact ((φ n).contDiff_normed (μ := volume) (n := ⊤)).continuous
    · exact (φ n).hasCompactSupport_normed
    · exact (φ n).integral_normed
    · exact (φ n).nonneg_normed
  have hupper : Tendsto (fun n => ∫ y, (φ n).normed volume y *
      (∫ z in K, ‖f (z - y) - f z‖)) atTop (𝓝 0) := by
    rw [hĤ0] at hconv
    exact hconv.congr' (Eventually.of_forall fun n => hident n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper ?_ ?_
  · intro n
    exact integral_nonneg fun z => norm_nonneg _
  · intro n
    exact hbound n

end Work.MRMT.Weyl
