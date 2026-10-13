import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.zHardyAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.boundarySeqs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.truncBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Topology Interval

/-! ## The radial self-pairing bound in one dimension

With `D = z ∂_z`, `w(z) = (1+z)²/z²` and `ρ = w²`, the estimate

`|∫_0^∞ ρ (DY) Y| ≤ 2 ∫_0^∞ ρ Y²`

is obtained from the exact identity (`s z = z ρ z = (1+z)^4/z^3`)

`(s Y²)' = s' Y² + 2 ρ (z Y') Y`

by integrating over `[ε, M] ⊂ (0,∞)`, where the boundary term `s Y²` vanishes along a
sequence `ε ↑ 0` (dyadic minimisers, `zHardy_seq_bot`) and `M → ∞`
(`zHardy_seq_top`), using `|s'| ≤ 4 ρ` pointwise. -/

noncomputable section

/-- The `L²`-weighted square `w(z)² Y(z)²` of a radial profile. -/
def selfH (Y : ℝ → ℝ) : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2

/-- The integrand `w(z)² (z Y'(z)) Y(z)` of the self-paired radial term. -/
def selfF (Y : ℝ → ℝ) : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)

/-- `w²` is continuous on any compact subinterval of `(0,∞)`. -/
theorem continuousOn_wSq {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => (Work.Spaces.w z) ^ 2) (Set.Icc a b) := by
  have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2) (Set.Icc a b) :=
    (continuousOn_const.add continuousOn_id).pow 2
  have h2 : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Icc a b) := continuousOn_id.pow 2
  have h3 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b) :=
    h1.div h2 (fun y hy => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hy.1)))
  have h4 : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Icc a b) := h3.pow 2
  unfold Work.Spaces.w
  exact h4

/-- `selfH Y` is continuous on any compact subinterval of `(0,∞)`. -/
theorem continuousOn_selfH {Y : ℝ → ℝ} (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0)) {a b : ℝ}
    (ha : 0 < a) : ContinuousOn (selfH Y) (Set.Icc a b) := by
  have h1 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Icc a b) := continuousOn_wSq ha
  have h2 : ContinuousOn (fun z : ℝ => (Y z) ^ 2) (Set.Icc a b) :=
    (hY.continuousOn.mono (fun y hy => lt_of_lt_of_le ha hy.1)).pow 2
  have h3 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Icc a b) :=
    h1.mul h2
  exact h3

theorem dzSelf1d {Y : ℝ → ℝ} (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0))
    (hF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0))
    (hD : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
      (Set.Ioi 0)) :
    |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)|
      ≤ 2 * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  change |∫ z in Set.Ioi 0, selfF Y z| ≤ 2 * ∫ z in Set.Ioi 0, selfH Y z
  have hHint : MeasureTheory.IntegrableOn (selfH Y) (Set.Ioi 0) := by
    change MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0)
    exact hF
  have hHnn : ∀ z, 0 ≤ selfH Y z := by
    intro z
    change 0 ≤ (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
    positivity
  by_cases hint : MeasureTheory.IntegrableOn (selfF Y) (Set.Ioi 0)
  · obtain ⟨ε, M, hεpos, hεM, hε0, hMtop, hHε, hHM⟩ :=
      boundarySeqs (selfH Y) hHint hHnn
        (fun k => continuousOn_selfH hY (by positivity))
        (fun k => continuousOn_selfH hY (by positivity))
    have hL1 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), selfF Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, selfF Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (selfF Y) hint hεpos hε0 hMtop
    have hL2 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, selfH Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (selfH Y) hHint hεpos hε0 hMtop
    have hk : ∀ k : ℕ, |∫ z in Set.Ioc (ε k) (M k), selfF Y z|
        ≤ (1 / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + 2 * ∫ z in Set.Ioc (ε k) (M k), selfH Y z := by
      intro k
      have htb := truncBound (Y := Y) (a := ε k) (b := M k) hY (hεpos k) (hεM k)
      simp only [intervalIntegral.integral_of_le (hεM k)] at htb
      simpa only [selfH, selfF] using htb
    have hbound : Tendsto
        (fun k => (1 / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + 2 * ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (2 * ∫ z in Set.Ioi 0, selfH Y z)) := by
      have hmid : Tendsto
          (fun k => (1 / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)) atTop (𝓝 0) := by
        have h := (hHM.add hHε).const_mul (1 / 2)
        simpa using h
      have h2 : Tendsto (fun k => 2 * ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
          (𝓝 (2 * ∫ z in Set.Ioi 0, selfH Y z)) := hL2.const_mul 2
      simpa using hmid.add h2
    exact le_of_tendsto_of_tendsto' hL1.abs hbound hk
  · rw [integral_undef hint, abs_zero]
    exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi (fun z _ => hHnn z))

end

end Work.FTS.StrongPersist.H6Pair6Aux
