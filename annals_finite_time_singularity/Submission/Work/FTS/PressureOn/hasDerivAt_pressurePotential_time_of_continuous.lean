/-
# The time-derivative of the pressure potential: the jointly continuous case

This is the companion of `hasDerivAt_pressurePotential_time_of_integrable`: the requested
`Work.FTS.PressureOn.hasDerivAt_pressurePotential_time` is false as stated (its slices need not be
integrable against the singular kernel `∇Nfund (x - ·)`, see the counterexample file
`refute_hasDerivAt_pressurePotential_time.lean`), and the corrected hypothesis is precisely that
those slices *are* integrable.

Here we show that **joint continuity of `f`**, together with the support hypothesis `hsupp`, is
enough to produce that integrability (the support ball is compact, so `f` is bounded on it, and
`‖∇Nfund (x - ·)‖ ≲ ‖x - ·‖⁻²` is locally integrable in dimension three).  This is the form in
which the lemma is applied to the physical reconstruction, where `f = u × ω` is the Lamb vector of
a jointly `C^{1,α}` velocity/vorticity pair with compactly supported vorticity.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.hasDerivAt_pressurePotential_time_of_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- `∇Nfund` is Borel measurable (it is `(4π)⁻¹‖z‖⁻³ • z`). -/
theorem measurable_nablaNfund : Measurable (nablaNfund : R3 → R3) := by
  have h1 : Measurable fun z : R3 => ((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ : ℝ) :=
    measurable_const.mul ((continuous_norm.pow 3).measurable.inv)
  have h2 : Measurable fun z : R3 => z := measurable_id
  exact h1.smul h2

/-- The slice integrand `y ↦ ⟪∇Nfund (x - y), f y s⟫` is a.e. strongly measurable as soon as `f`
is jointly continuous. -/
theorem aestronglyMeasurable_kernel_inner {f : R3 → ℝ → R3}
    (hcont : Continuous fun p : R3 × ℝ => f p.1 p.2) (x : R3) (s : ℝ) :
    AEStronglyMeasurable (fun y => inner ℝ (nablaNfund (x - y)) (f y s)) volume := by
  have hk : Measurable fun y : R3 => nablaNfund (x - y) :=
    measurable_nablaNfund.comp ((continuous_const.sub continuous_id)).measurable
  have hf : Measurable fun y : R3 => f y s :=
    (hcont.comp (continuous_id.prodMk continuous_const)).measurable
  exact (hk.inner hf).aemeasurable.aestronglyMeasurable

/-- **The missing integrability, from joint continuity.**  If `f` is jointly continuous and its
slices are supported in a fixed ball, then the slices are integrable against the kernel `∇Nfund`. -/
theorem integrable_kernel_inner_of_continuous {f : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hcont : Continuous fun p : R3 × ℝ => f p.1 p.2)
    (hsupp : ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y, f y s ≠ 0 → ‖y‖ ≤ R) :
    ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      Integrable (fun y => inner ℝ (nablaNfund (x - y)) (f y s)) volume := by
  obtain ⟨R, hR⟩ := hsupp
  -- a uniform bound for `‖f y s‖` on the compact `closedBall 0 R × Icc (t-1) (t+1)`
  have hK : IsCompact (closedBall (0 : R3) R ×ˢ Icc (t - 1) (t + 1)) :=
    (isCompact_closedBall (0 : R3) R).prod isCompact_Icc
  obtain ⟨B, hB⟩ := (hK.image hcont).isBounded.exists_norm_le
  have hB' : ∀ y ∈ closedBall (0 : R3) R, ∀ s ∈ Icc (t - 1) (t + 1), ‖f y s‖ ≤ B := by
    intro y hy s hs
    exact hB _ (Set.mem_image_of_mem (fun p : R3 × ℝ => f p.1 p.2) (show (y, s) ∈
      closedBall (0 : R3) R ×ˢ Icc (t - 1) (t + 1) from ⟨hy, hs⟩))
  intro s hsS
  have hsI : s ∈ Icc (t - 1) (t + 1) := ⟨hsS.1.le, hsS.2.le⟩
  refine Integrable.mono' (integrable_indicator_kernelWeight (R := R) (C := B) x)
    (aestronglyMeasurable_kernel_inner hcont x s) ?_
  refine ae_of_all _ (fun y => ?_)
  by_cases hy : y ∈ closedBall (0 : R3) R
  · have hby : (closedBall (0 : R3) R).indicator (fun y => B * ‖nablaNfund (x - y)‖) y
        = B * ‖nablaNfund (x - y)‖ := Set.indicator_of_mem hy _
    rw [hby]
    calc ‖inner ℝ (nablaNfund (x - y)) (f y s)‖
        ≤ ‖nablaNfund (x - y)‖ * ‖f y s‖ := norm_inner_le_norm _ _
      _ ≤ ‖nablaNfund (x - y)‖ * B :=
          mul_le_mul_of_nonneg_left (hB' y hy s hsI) (norm_nonneg _)
      _ = B * ‖nablaNfund (x - y)‖ := by ring
  · have hy' : R < ‖y‖ := by
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hy
      exact not_le.mp hy
    have hfs : f y s = 0 := by
      by_contra hne
      exact not_le.mpr hy' (hR s hsS y hne)
    have hby : (closedBall (0 : R3) R).indicator (fun y => B * ‖nablaNfund (x - y)‖) y = 0 :=
      Set.indicator_of_notMem hy _
    rw [hby, hfs, inner_zero_right, norm_zero]

/-- **The requested lemma, with the regularity hypothesis that makes it true**: `f` jointly
continuous and supported in a fixed ball (uniformly in time near `t`).  Both extra hypotheses are
automatic for the Lamb vector of a compactly supported physical solution, and *one* of them is
genuinely necessary -- see `refute_hasDerivAt_pressurePotential_time.lean`. -/
theorem hasDerivAt_pressurePotential_time_of_continuous {f : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hcont : Continuous fun p : R3 × ℝ => f p.1 p.2)
    (hsupp : ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y, f y s ≠ 0 → ‖y‖ ≤ R)
    (hlip : ∃ C, ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖f y s - f y t‖ ≤ C * |s - t|)
    (hderiv : ∀ y, HasDerivAt (f y) (FiniteTimeSingularity.timeDeriv f y t) t) :
    HasDerivAt (fun s => pressurePotential (f · s) x)
      (-∫ y, inner ℝ (nablaNfund (x - y)) (FiniteTimeSingularity.timeDeriv f y t)) t :=
  hasDerivAt_pressurePotential_time_of_integrable hsupp hlip hderiv
    (integrable_kernel_inner_of_continuous hcont hsupp)

end Work.FTS.PressureOn
