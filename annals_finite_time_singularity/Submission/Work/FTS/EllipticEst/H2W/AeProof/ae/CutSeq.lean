import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shifted two-scale cutoff family `Vn` of the level-`0` energy argument

`Vn n z = ψ((n+1)z - 2) · χ(z/(n+1))`, where `ψ = Real.smoothTransition` is the smooth step
(`0` on `(-∞,0]`, `1` on `[1,∞)`) and `χ = Work.Stability.chi` is the bump (`1` on `[-1,1]`,
`0` off `(-2,2)`).

Compared with the sibling family `Work.FTS.EllipticEst.PropL2Cut.Wc` (which is
`ψ((n+1)z)·χ(z/(n+1))`) the step is *shifted* by `2`: the family now vanishes on a whole
neighbourhood `(-∞, 2/(n+1)]` of the origin.  That is exactly what the `w²`-weighted truncated
energy identity needs at the `z → 0⁺` end (with the weight `Vn n·w²` the boundary terms are
identically zero, whereas for `Wc n·w²` they would have to be killed by the flatness of `ψ`).

The two scales are the ones of `Wc`: the `ψ`-ramp sits at `z ≈ 2/(n+1) → 0` and the `χ`-ramp at
`z ≈ n+1 → ∞`, which is what keeps the weighted transfer quantities `(z²·Vn n·w²)''` and
`(z·Vn n·w²)'` uniformly bounded by a multiple of `w²`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false

/-- The shifted two-scale cutoff `Vn n z = ψ((n+1)z - 2)·χ(z/(n+1))`. -/
def Vn (n : ℕ) (z : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * z - 2) * Work.Stability.chi (z / ((n : ℝ) + 1))

theorem Vn_apply (n : ℕ) (z : ℝ) :
    Vn n z = Real.smoothTransition (((n : ℝ) + 1) * z - 2)
      * Work.Stability.chi (z / ((n : ℝ) + 1)) := rfl

/-- `Vn n` is smooth. -/
theorem Vn_contDiff (n : ℕ) : ContDiff ℝ ∞ (Vn n) := by
  unfold Vn
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Work.Stability.chi_contDiff.comp (by fun_prop))

/-- `Vn n` is nonnegative. -/
theorem Vn_nonneg (n : ℕ) (z : ℝ) : 0 ≤ Vn n z := by
  unfold Vn
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Work.Stability.chi_nonneg _)

/-- `Vn n` is bounded by `1`. -/
theorem Vn_le_one (n : ℕ) (z : ℝ) : Vn n z ≤ 1 := by
  unfold Vn
  simpa using mul_le_mul (Real.smoothTransition.le_one _) (Work.Stability.chi_le_one _)
    (Work.Stability.chi_nonneg _) zero_le_one

/-- `Vn n` vanishes off `[-(2(n+1)), 2(n+1)]`. -/
theorem Vn_eq_zero_of_abs {n : ℕ} {z : ℝ} (h : 2 * ((n : ℝ) + 1) ≤ |z|) : Vn n z = 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : 2 ≤ |z / ((n : ℝ) + 1)| := by
    rw [abs_div, abs_of_nonneg hpos.le, le_div_iff₀ hpos]
    linarith
  unfold Vn
  rw [Work.Stability.chi_eq_zero h2, mul_zero]

/-- `Vn n` has compact support. -/
theorem Vn_hasCompactSupport (n : ℕ) : HasCompactSupport (Vn n) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * ((n : ℝ) + 1)))
    (b := 2 * ((n : ℝ) + 1))) ?_
  intro z hz
  simp only [Set.mem_Icc, not_and_or, not_le] at hz
  exact Vn_eq_zero_of_abs (by
    rcases hz with h | h
    · rw [abs_of_neg (by linarith [h])]; linarith
    · rw [abs_of_pos (by linarith [h])]; linarith)

/-- `Vn n` vanishes on `(-∞, 2/(n+1)]`: the shifted step keeps the family away from the origin. -/
theorem Vn_eq_zero_of_le {n : ℕ} {z : ℝ} (hz : z ≤ 2 / ((n : ℝ) + 1)) : Vn n z = 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : ((n : ℝ) + 1) * z - 2 ≤ 0 := by
    rw [le_div_iff₀ hpos] at hz
    linarith
  unfold Vn
  rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

/-- `Vn n z → 1` for every `z > 0`. -/
theorem Vn_tendsto_one (z : ℝ) (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Vn n z) Filter.atTop (nhds 1) := by
  have hnat : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ ((n : ℝ) + 1) * z - 2 := by
    have hz' : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) * z - 2) Filter.atTop Filter.atTop := by
      have hlin : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) * z) Filter.atTop Filter.atTop :=
        Filter.Tendsto.atTop_mul_const hz hnat
      simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right _ (-2) hlin
    exact hz'.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, |z / ((n : ℝ) + 1)| ≤ 1 := by
    have hlim : Filter.Tendsto (fun n : ℕ => z / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hnat
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact le_of_lt hn
  have hev : ∀ᶠ n : ℕ in Filter.atTop, Vn n z = 1 := by
    filter_upwards [h1, h2] with n hn1 hn2
    unfold Vn
    rw [Real.smoothTransition.one_of_one_le hn1, Work.Stability.chi_eq_one hn2, one_mul]
  exact tendsto_const_nhds.congr' (hev.mono (fun n h => h.symm))

end Work.FTS.EllipticEst.H2W.AeProof.ae
