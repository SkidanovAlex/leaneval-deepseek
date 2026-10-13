/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Aux/abs_sub_sub_mul_le.lean` — the one-variable mean
value bound with an explicit modulus

The quantitative form of the mean value theorem used by `c1_of_locUnif_slots_lip` (and by its
auxiliary `hasFDerivAt_of_fst_snd`): if `φ` has derivative `ψ` on the open interval and `ψ`
stays within `ε` of the constant `c` on the closed interval, then the chord of `φ` is
`c`-linear up to `ε` per unit length.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- **One-variable mean value bound.**  For `a ≤ b`, if `φ` is continuous on `[a,b]` and
`HasDerivAt φ (ψ x) x` for `x ∈ (a,b)`, with `ψ` continuous on `[a,b]` and `|ψ x - c| ≤ ε`
there, then `|φ b - φ a - c (b - a)| ≤ ε (b - a)`. -/
theorem abs_sub_sub_mul_le {φ ψ : ℝ → ℝ} {a b c ε : ℝ} (hab : a ≤ b)
    (hcontφ : ContinuousOn φ (Set.Icc a b))
    (hder : ∀ x ∈ Set.Ioo a b, HasDerivAt φ (ψ x) x)
    (hcontψ : ContinuousOn ψ (Set.Icc a b))
    (hψ : ∀ x ∈ Set.Icc a b, |ψ x - c| ≤ ε) :
    |φ b - φ a - c * (b - a)| ≤ ε * (b - a) := by
  have hder' : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun t : ℝ => φ t - c * t) (ψ x - c) x := by
    intro x hx
    have hc : HasDerivAt (fun t : ℝ => c * t) c x :=
      hasDerivAt_const_mul c
    exact (hder x hx).sub hc
  have hcontΦ : ContinuousOn (fun t : ℝ => φ t - c * t) (Set.Icc a b) :=
    hcontφ.sub (continuous_const.continuousOn.mul continuous_id.continuousOn)
  have hint : IntervalIntegrable (fun x : ℝ => ψ x - c) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact hcontψ.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => c) (Set.Icc a b))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcontΦ hder' hint
  have hintabs : IntervalIntegrable (fun x : ℝ => |ψ x - c|) volume a b :=
    hint.abs
  have hmono : (∫ x in a..b, |ψ x - c|) ≤ ∫ x in a..b, ε :=
    intervalIntegral.integral_mono_on hab hintabs intervalIntegrable_const
      (fun x hx => hψ x hx)
  have hconst : (∫ x in a..b, ε) = ε * (b - a) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul, mul_comm]
  calc |φ b - φ a - c * (b - a)|
      = |(φ b - c * b) - (φ a - c * a)| := by ring_nf
    _ = |∫ x in a..b, (ψ x - c)| := by rw [hFTC]
    _ ≤ ∫ x in a..b, |ψ x - c| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in a..b, ε := hmono
    _ = ε * (b - a) := hconst

end Work.FTS.StrongEps.E5Aux
