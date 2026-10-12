import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.TruncDefs` — the truncated FS cut-off symbols

The FS cut-off symbol `fsKinCoeff c = [· − c]₊²` is *not* integrable (`[r−c]₊² → ∞`), so the
symbol-integral identity `SymbolIntegral ℓ (fsKinCoeff c)` cannot be read off from the `L¹`
case directly; it is obtained as the monotone limit of the truncated symbols

    `Ftrunc c n r = if r ≤ n then [r − c]₊² else 0`      (`n : ℕ`).

Each `Ftrunc c n` is nonnegative, bounded (by `[n − c]₊²`), compactly supported in the radial
variable (hence `Integrable (fun p => Ftrunc c n ‖p‖)`), increasing in `n`, and converges
pointwise to `fsKinCoeff c`.  These are the only properties of the approximation used by the
monotone-convergence argument of `SymbolIntegral_fsKinCoeff`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The truncation of the FS cut-off symbol `[· − c]₊²` at radial size `n`:
`Ftrunc c n r = [r − c]₊²` for `r ≤ n` and `0` for `r > n`. -/
noncomputable def Ftrunc (c : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun r => if r ≤ (n : ℝ) then fsKinCoeff c r else 0

lemma Ftrunc_apply (c : ℝ) (n : ℕ) (r : ℝ) :
    Ftrunc c n r = if r ≤ (n : ℝ) then fsKinCoeff c r else 0 := rfl

lemma Ftrunc_of_le {c : ℝ} {n : ℕ} {r : ℝ} (hr : r ≤ (n : ℝ)) :
    Ftrunc c n r = fsKinCoeff c r := if_pos hr

lemma Ftrunc_of_gt {c : ℝ} {n : ℕ} {r : ℝ} (hr : (n : ℝ) < r) :
    Ftrunc c n r = 0 := if_neg (not_le.mpr hr)

/-- The truncated symbol is nonnegative. -/
lemma Ftrunc_nonneg (c : ℝ) (n : ℕ) (r : ℝ) : 0 ≤ Ftrunc c n r := by
  rw [Ftrunc_apply]
  by_cases h : r ≤ (n : ℝ)
  · rw [if_pos h]; exact fsKinCoeff_nonneg c r
  · rw [if_neg h]

/-- The truncated symbol is pointwise bounded by the full cut-off. -/
lemma Ftrunc_le_fsKinCoeff (c : ℝ) (n : ℕ) (r : ℝ) :
    Ftrunc c n r ≤ fsKinCoeff c r := by
  rw [Ftrunc_apply]
  by_cases h : r ≤ (n : ℝ)
  · rw [if_pos h]
  · rw [if_neg h]; exact fsKinCoeff_nonneg c r

/-- The truncated symbol is pointwise bounded by `[n − c]₊²` (its value at the truncation
radius): monotonicity of `[· − c]₊²` on `[c, ∞)` and its vanishing below `c`. -/
lemma Ftrunc_le_max (c : ℝ) (n : ℕ) (r : ℝ) :
    Ftrunc c n r ≤ fsKinCoeff c (n : ℝ) := by
  rw [Ftrunc_apply]
  by_cases h : r ≤ (n : ℝ)
  · rw [if_pos h]
    rcases le_total r c with hrc | hcr
    · rw [fsKinCoeff_of_le hrc]; exact fsKinCoeff_nonneg c _
    · exact fsKinCoeff_mono hcr h
  · rw [if_neg h]; exact fsKinCoeff_nonneg c _

/-- The truncations are increasing in `n`. -/
lemma Ftrunc_mono_le (c : ℝ) {n m : ℕ} (hnm : n ≤ m) (r : ℝ) :
    Ftrunc c n r ≤ Ftrunc c m r := by
  rw [Ftrunc_apply, Ftrunc_apply]
  by_cases h : r ≤ (n : ℝ)
  · rw [if_pos h]
    have hm : r ≤ (m : ℝ) := le_trans h (by exact_mod_cast hnm)
    rw [if_pos hm]
  · rw [if_neg h]
    exact Ftrunc_nonneg c m r

/-- The truncations increase to the full cut-off, pointwise. -/
lemma Ftrunc_tendsto (c : ℝ) (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => Ftrunc c n r) Filter.atTop (𝓝 (fsKinCoeff c r)) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop ⌈r⌉₊] with n hn
  have hr : r ≤ (n : ℝ) := le_trans (Nat.le_ceil r) (by exact_mod_cast hn)
  rw [Ftrunc_of_le hr]

/-- `r ↦ Ftrunc c n r` is measurable (it is piecewise a continuous function and `0`). -/
lemma measurable_Ftrunc (c : ℝ) (n : ℕ) : Measurable (Ftrunc c n) := by
  have h1 : Measurable (fun r : ℝ => fsKinCoeff c r) := by
    simp only [Submission.BoseGases.fsKinCoeff]
    fun_prop
  exact Measurable.ite (p := fun r : ℝ => r ≤ (n : ℝ)) measurableSet_Iic h1 measurable_const

/-- **The truncated symbols are integrable in the radial variable.**  `p ↦ Ftrunc c n ‖p‖`
is supported in the ball of radius `n` and bounded by `[n − c]₊²`. -/
theorem integrable_Ftrunc (c : ℝ) (n : ℕ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Ftrunc c n ‖p‖) := by
  classical
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ => Ftrunc c n ‖p‖) volume :=
    ((measurable_Ftrunc c n).comp continuous_norm.measurable).aestronglyMeasurable
  have hind : (fun p : ℝ³ => Ftrunc c n ‖p‖)
      = (closedBall (0 : ℝ³) (n : ℝ)).indicator (fun p => Ftrunc c n ‖p‖) := by
    funext p
    by_cases hp : p ∈ closedBall (0 : ℝ³) (n : ℝ)
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp]
      rw [mem_closedBall, dist_zero_right, not_le] at hp
      exact Ftrunc_of_gt hp
  rw [hind, MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
  refine MeasureTheory.IntegrableOn.of_bound
    ((isCompact_closedBall (0 : ℝ³) (n : ℝ)).measure_lt_top)
    (hmeas.restrict) (fsKinCoeff c (n : ℝ)) ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (Ftrunc_nonneg c n ‖p‖)]
  exact Ftrunc_le_max c n ‖p‖

end Work.OneBodyKin
