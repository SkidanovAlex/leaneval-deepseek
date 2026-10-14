import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.Physical.BiotSavart.vorticityDecay_of_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.BiotSavart

/-- **The `α`-power decay of a bounded vorticity of compact support.**

If `ω` vanishes outside the closed ball of radius `R` and `‖ω‖ ≤ M` everywhere, then
`‖ω x‖ ≤ C/(‖x‖^α + 1)` for all `x`, with the explicit constant `C = max 1 (M(R^α+1))`:
outside the ball the left-hand side vanishes, while inside it `‖x‖^α ≤ R^α`, so that
`M(‖x‖^α+1) ≤ M(R^α+1) ≤ C`. -/
theorem vorticityDecay_of_support {α : NNReal} {ω : Work.FTS.Physical.R3 → Work.FTS.Physical.R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hsupp : ∀ x : Work.FTS.Physical.R3, ω x ≠ 0 → x ∈ Metric.closedBall 0 R) (hbdd : ∀ x : Work.FTS.Physical.R3, ‖ω x‖ ≤ M) : ∃ C : ℝ, 0 < C ∧ ∀ x : Work.FTS.Physical.R3, ‖ω x‖ ≤ C / (‖x‖ ^ ((α : NNReal) : ℝ) + 1) := by
  refine ⟨max 1 (M * (R ^ (α : ℝ) + 1)), lt_of_lt_of_le one_pos (le_max_left _ _), fun x => ?_⟩
  rcases eq_or_ne (ω x) 0 with h0 | hne
  · rw [h0, norm_zero]
    positivity
  · -- the point lies in the support ball, so `‖x‖ ^ α ≤ R ^ α`
    have hxmem : x ∈ Metric.closedBall (0 : Work.FTS.Physical.R3) R := hsupp x hne
    rw [Metric.mem_closedBall, dist_zero_right] at hxmem
    have hxα : ‖x‖ ^ ((α : NNReal) : ℝ) ≤ R ^ (α : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg x) hxmem (by positivity)
    have hden : 0 < ‖x‖ ^ ((α : NNReal) : ℝ) + 1 := by
      have := Real.rpow_nonneg (norm_nonneg x) ((α : NNReal) : ℝ); linarith
    have hdenR : 0 < R ^ (α : ℝ) + 1 := by
      have := Real.rpow_nonneg hR (α : ℝ); linarith
    rw [le_div_iff₀ hden]
    have h1 : M * (R ^ (α : ℝ) + 1) ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_right _ _
    have h2 : 1 ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_left _ _
    nlinarith [hbdd x, h1, h2, hdenR, hxα, Real.rpow_nonneg (norm_nonneg x) ((α : NNReal) : ℝ)]

end Work.FTS.Physical.BiotSavart
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.A_le_exp_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set

namespace Work.FTS.Physical.Clock

theorem A_le_exp_mul (C : Work.FTS.Physical.PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) : C.A s ≤ C.A τ * Real.exp (-(s - τ) / 2) := by
  -- `x ↦ A x * exp (x/2)` is antitone on `[0,∞)`: its derivative is
  -- `exp (x/2) * A x * (1/2 - (1 + μ x)) ≤ 0`, since `A x > 0` and `1 + μ x ≥ 1/2`.
  have hcont : ContinuousOn (fun x : ℝ => C.A x * Real.exp (x / 2)) (Set.Ici (0:ℝ)) := by
    exact C.hAcont.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
  have hderiv : ∀ x ∈ interior (Set.Ici (0:ℝ)),
      HasDerivWithinAt (fun x : ℝ => C.A x * Real.exp (x / 2))
        ((-(1 + C.mu x) * C.A x) * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1/2)))
        (interior (Set.Ici (0:ℝ))) x := by
    intro x hx
    have hx' : (0:ℝ) < x := by simpa [interior_Ici] using hx
    have h1 : HasDerivAt (fun x : ℝ => C.A x) (-(1 + C.mu x) * C.A x) x := C.hAderiv x hx'.le
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (Real.exp (x / 2) * (1/2)) x :=
      ((hasDerivAt_id x).div_const 2).exp
    exact (h1.mul h2).hasDerivWithinAt
  have hnonpos : ∀ x ∈ interior (Set.Ici (0:ℝ)),
      (-(1 + C.mu x) * C.A x) * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1/2)) ≤ 0 := by
    intro x hx
    have hx' : (0:ℝ) < x := by simpa [interior_Ici] using hx
    have hA : 0 < C.A x := C.hApos x hx'.le
    have hE : 0 < Real.exp (x / 2) := Real.exp_pos _
    have hmu : (1:ℝ)/2 ≤ 1 + C.mu x := by
      have := C.hmu_lo x hx'.le
      linarith
    have heq : (-(1 + C.mu x) * C.A x) * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1/2))
        = Real.exp (x / 2) * C.A x * ((1:ℝ)/2 - (1 + C.mu x)) := by ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hE.le hA.le) (by linarith)
  have hanti : AntitoneOn (fun x : ℝ => C.A x * Real.exp (x / 2)) (Set.Ici (0:ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hcont hderiv hnonpos
  have h1 : C.A s * Real.exp (s / 2) ≤ C.A τ * Real.exp (τ / 2) :=
    hanti hτ (le_trans hτ hτs) hτs
  -- multiply the target inequality by `exp (s/2) > 0` to reduce it to `h1`
  have hpos : 0 < Real.exp (s / 2) := Real.exp_pos _
  have key : C.A s * Real.exp (s / 2) ≤ (C.A τ * Real.exp (-(s - τ) / 2)) * Real.exp (s / 2) := by
    calc C.A s * Real.exp (s / 2) ≤ C.A τ * Real.exp (τ / 2) := h1
      _ = (C.A τ * Real.exp (-(s - τ) / 2)) * Real.exp (s / 2) := by
            rw [mul_assoc, ← Real.exp_add]; congr 1; ring_nf
  exact (mul_le_mul_iff_left₀ hpos).mp key

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.T_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

set_option autoImplicit false

namespace Work.FTS.Physical.Clock

/-- **Grönwall-type monotonicity of `τ ↦ A τ · e^{τ/2}`.**  This is the only place where the
modulation lower bound `1/2 ≤ 1 + μ` is used. -/
private theorem antitoneOn_A_mul_exp (C : Work.FTS.Physical.PhysClock) :
    AntitoneOn (fun t : ℝ => C.A t * Real.exp (t / 2)) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact C.hAcont.mul ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn)
  · -- differentiability on the interior
    intro t ht
    have ht0 : 0 ≤ t := by
      have h := interior_subset ht
      simpa using h
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
      have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
      simpa using h2.exp
    exact ((C.hAderiv t ht0).mul h1).differentiableAt.differentiableWithinAt
  · -- the derivative is nonpositive
    intro t ht
    have ht0 : 0 ≤ t := by
      have h := interior_subset ht
      simpa using h
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
      have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
      simpa using h2.exp
    have hd : HasDerivAt (fun s : ℝ => C.A s * Real.exp (s / 2))
        (Real.exp (t / 2) * C.A t * (-(1 + C.mu t) + 1 / 2)) t := by
      have h3 := (C.hAderiv t ht0).mul h1
      convert h3 using 1
      ring
    rw [hd.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.exp_pos _).le (C.hApos t ht0).le)
      (by linarith [C.hmu_lo t ht0])

/-- **Exponential decay of the amplitude**: `A s ≤ A 0 · e^{-s/2}` for `s ≥ 0`. -/
private theorem A_le_exp_half (C : Work.FTS.Physical.PhysClock) {s : ℝ} (hs : 0 ≤ s) :
    C.A s ≤ C.A 0 * Real.exp ((-(1 / 2)) * s) := by
  have h0mem : (0 : ℝ) ∈ Set.Ici 0 := le_refl (0 : ℝ)
  have hs' : s ∈ Set.Ici (0 : ℝ) := hs
  have hle : C.A s * Real.exp (s / 2) ≤ C.A 0 := by
    have h := antitoneOn_A_mul_exp C (a := 0) (b := s) h0mem hs' hs
    simpa using h
  have h1 : -(s / 2) = (-(1 / 2)) * s := by ring
  calc C.A s = C.A s * Real.exp (s / 2) * Real.exp (-(s / 2)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ C.A 0 * Real.exp (-(s / 2)) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = C.A 0 * Real.exp ((-(1 / 2)) * s) := by rw [h1]

/-- **Integrability of the amplitude on `[0,∞)`**: the blow-up happens in finite time. -/
private theorem integrableOn_A_Tpos (C : Work.FTS.Physical.PhysClock) :
    MeasureTheory.IntegrableOn C.A (Set.Ici 0) := by
  have hg : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp ((-(1 / 2)) * s)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi (by norm_num) 0)
  have hg2 : MeasureTheory.IntegrableOn (fun s : ℝ => C.A 0 * Real.exp ((-(1 / 2)) * s))
      (Set.Ici 0) := by
    show MeasureTheory.Integrable (fun s : ℝ => C.A 0 * Real.exp ((-(1 / 2)) * s))
      (volume.restrict (Set.Ici 0))
    exact (show MeasureTheory.Integrable (fun s : ℝ => Real.exp ((-(1 / 2)) * s))
      (volume.restrict (Set.Ici 0)) from hg).const_mul _
  have hmeas : MeasureTheory.AEStronglyMeasurable C.A (volume.restrict (Set.Ici 0)) :=
    C.hAcont.aestronglyMeasurable measurableSet_Ici
  have hbound : ∀ᵐ s ∂(volume.restrict (Set.Ici 0)),
      ‖C.A s‖ ≤ C.A 0 * Real.exp ((-(1 / 2)) * s) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Real.norm_of_nonneg (C.hApos s hs).le]
      exact A_le_exp_half C hs)
  exact hg2.mono' hmeas hbound

/-- **The blow-up time is positive.** -/
theorem T_pos (C : Work.FTS.Physical.PhysClock) : 0 < C.T := by
  change 0 < ∫ s in Set.Ici (0 : ℝ), C.A s
  have hint : MeasureTheory.IntegrableOn C.A (Set.Ici 0) := integrableOn_A_Tpos C
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici 0)] C.A := by
    have h : ∀ᵐ s ∂(volume.restrict (Set.Ici 0)), 0 ≤ C.A s := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      exact Filter.Eventually.of_forall (fun s hs => (C.hApos s hs).le)
    exact h
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hpos : (0 : ENNReal) < volume (Set.Icc (0 : ℝ) 1) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Function.support C.A ∩ Set.Ici 0 := by
    intro x hx
    exact ⟨(C.hApos x hx.1).ne', hx.1⟩
  exact lt_of_lt_of_le hpos (MeasureTheory.measure_mono hsub)

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.clock_slope_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slope of the clock at the blow-up time

The clock of the dynamic rescaling is `t(τ) = ∫₀^τ A`, where the amplitude `A` is positive and
continuous on `[0,∞)` (`PhysClock.hApos`, `PhysClock.hAcont`).  This file computes the *right*
slope of the clock at `τ = 0`:

`t(y)/y ⟶ A(0)`  and  `y/t(y) ⟶ A(0)⁻¹`  as `y → 0⁺`.

The first limit is the fundamental theorem of calculus: `A` has right limit `A(0)` at `0`, so the
average of `A` over `(0,y)` tends to `A(0)`; equivalently `t` has right derivative `A 0` at `0`,
and the Newton quotient `(t(y) - t(0))/(y - 0) = t(y)/y` converges to it
(`hasDerivWithinAt_iff_tendsto_slope`).  The second limit follows from the first by continuity of
`x ↦ x⁻¹` at the *nonzero* value `A(0) > 0` and the field identity `(t(y)/y)⁻¹ = y/t(y)`
(`inv_div`, which in a `DivisionMonoid` is unconditional — no side condition on `t(y)` is needed).

Both limits are one-sided: `t` is only known to be a primitive of `A` with `A` continuous on
`[0,∞)`, so nothing is claimed about the slope from the left (`A` is not even assumed continuous
on `(-∞,0)`).
-/

namespace Work.FTS.Physical.Clock

open Filter MeasureTheory
open scoped Topology

/-- **`t` has right derivative `A 0` at `0`.**  This is the fundamental theorem of calculus at the
left endpoint `0` of the fake-time half-line: `A` is integrable on the degenerate interval `0..0`,
strongly measurable at `𝓝[>] 0` (being continuous on `[0,∞)`), and continuous at `0` within
`(0,∞)` (`PhysClock.hAcont`), so `u ↦ ∫₀^u A` has derivative `A 0` at `0` within `Ici 0`.

Note that no two-sided derivative is claimed (nor true in general): `A` is only assumed continuous
on `[0,∞)`. -/
theorem hasDerivWithinAt_t_zero (C : Work.FTS.Physical.PhysClock) :
    HasDerivWithinAt C.t (C.A 0) (Set.Ici (0 : ℝ)) 0 := by
  -- `A` is continuous at `0` along `(0,∞)`
  have hA : ContinuousWithinAt C.A (Set.Ioi (0 : ℝ)) 0 :=
    (C.hAcont 0 (Set.mem_Ici.mpr le_rfl)).mono Set.Ioi_subset_Ici_self
  -- and strongly measurable at `𝓝[>] 0`
  have hmeas : StronglyMeasurableAtFilter C.A (𝓝[Set.Ioi (0 : ℝ)] 0) volume :=
    ⟨Set.Ioi 0, self_mem_nhdsWithin,
      (C.hAcont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi⟩
  -- and integrable on the degenerate interval `0..0`
  have hf : IntervalIntegrable C.A volume (0 : ℝ) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le le_rfl]
    exact C.hAcont.mono Set.Icc_subset_Ici_self
  have hderiv : HasDerivWithinAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, C.A x) (C.A 0) (Set.Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right hf hmeas hA
  exact hderiv

/-- **The right slope of the clock at `0` is `A 0`**: `t(y)/y → A(0)` as `y → 0⁺`. -/
theorem tendsto_t_div_self (C : Work.FTS.Physical.PhysClock) :
    Filter.Tendsto (fun y : ℝ => C.t y / y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (C.A 0)) := by
  -- the Newton quotient is the slope, which converges to the right derivative
  have hslope : Filter.Tendsto (slope C.t 0) (nhdsWithin (0 : ℝ) (Set.Ici 0 \ {0}))
      (nhds (C.A 0)) :=
    hasDerivWithinAt_iff_tendsto_slope.mp (hasDerivWithinAt_t_zero C)
  -- `Ioi 0` is (up to the irrelevant point `0`) the domain of the slope
  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) \ {0} := by
    intro y hy
    have hy0 : 0 < y := Set.mem_Ioi.mp hy
    exact ⟨le_of_lt hy0, by simp [ne_of_gt hy0]⟩
  have hmono := hslope.mono_left (nhdsWithin_mono 0 hsub)
  refine hmono.congr' ?_
  filter_upwards with y
  simp [slope_def_field]

/-- **The reciprocal right slope of the clock at `0`**: `y/t(y) → A(0)⁻¹` as `y → 0⁺`.  This is
`t(y)/y → A(0)` (`tendsto_t_div_self`) composed with inversion at the nonzero value `A(0) > 0`,
using the identity `(t(y)/y)⁻¹ = y/t(y)` of a `DivisionMonoid`. -/
theorem tendsto_self_div_t (C : Work.FTS.Physical.PhysClock) :
    Filter.Tendsto (fun y : ℝ => y / C.t y) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((C.A 0)⁻¹)) := by
  have hne : C.A 0 ≠ 0 := ne_of_gt (C.hApos 0 le_rfl)
  have h2 : Filter.Tendsto (fun y : ℝ => (C.t y / y)⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((C.A 0)⁻¹)) :=
    (tendsto_t_div_self C).inv₀ hne
  refine h2.congr' ?_
  filter_upwards with y
  exact inv_div (C.t y) y

/-- **The slope of the clock at the blow-up time.**  The clock `t(τ) = ∫₀^τ A` of a `PhysClock`
has slope `A(0)` at `τ = 0` from the right, in both orientations: `t(y)/y → A(0)` and
`y/t(y) → A(0)⁻¹` as `y → 0⁺`. -/
theorem clock_slope_tendsto (C : Work.FTS.Physical.PhysClock) :
    Filter.Tendsto (fun y : ℝ => C.t y / y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (C.A 0)) ∧
    Filter.Tendsto (fun y : ℝ => y / C.t y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((C.A 0)⁻¹)) :=
  ⟨tendsto_t_div_self C, tendsto_self_div_t C⟩

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.continuousOn_t =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.Physical.Clock


end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.exists_t_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology Interval
open Set Filter MeasureTheory

set_option autoImplicit false

namespace Work.FTS.Physical.Clock

/-- The amplitude `A` extended to all of `ℝ` by constancy to the left of `0`.  Unlike `A` itself,
`extA` is continuous everywhere, which is what makes `τ ↦ ∫₀^τ extA` (and hence the clock) a
globally continuous primitive.  On `[0,∞)` the extension agrees with `A` (see `extA_apply`). -/
private def extA (C : PhysClock) : ℝ → ℝ := fun τ => C.A (max τ 0)

@[simp]
private theorem extA_apply (C : PhysClock) (τ : ℝ) : extA C τ = C.A (max τ 0) := rfl

/-- `extA` is continuous. -/
private theorem extA_cont (C : PhysClock) : Continuous (extA C) := by
  have h : Continuous fun τ : ℝ => max τ 0 := continuous_id.max continuous_const
  have h2 := C.hAcont.comp_continuous h fun τ => le_max_right τ 0
  exact h2


/-- **The decay bound.**  From `A' = -(1+μ)A` with `1 + μ ≥ 1/2`, the function
`τ ↦ A(τ)e^{τ/2}` has nonpositive derivative on `(0,∞)`, hence is antitone there; this gives
`A(s) ≤ A(τ)e^{(τ-s)/2}` for `0 ≤ τ ≤ s`. -/
private theorem A_decay (C : PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) :
    C.A s ≤ C.A τ * Real.exp (τ / 2 - s / 2) := by
  have hanti : AntitoneOn (fun x : ℝ => C.A x * Real.exp (x / 2)) (Ici (0 : ℝ)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Ici (0 : ℝ))
      (f := fun x : ℝ => C.A x * Real.exp (x / 2))
      (f' := fun x : ℝ => C.A x * Real.exp (x / 2) * (1 / 2 - (1 + C.mu x)))
      (convex_Ici 0) ?_ ?_ ?_
    · exact C.hAcont.mul
        (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
        simpa using (hasDerivAt_id x).div_const 2
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) * (1 / 2)) x :=
        h1.exp
      have h3 : HasDerivAt (fun y : ℝ => C.A y * Real.exp (y / 2))
          ((-(1 + C.mu x) * C.A x) * Real.exp (x / 2)
            + C.A x * (Real.exp (x / 2) * (1 / 2))) x :=
        (C.hAderiv x hx0).mul h2
      have h4 : HasDerivAt (fun y : ℝ => C.A y * Real.exp (y / 2))
          (C.A x * Real.exp (x / 2) * (1 / 2 - (1 + C.mu x))) x := by
        convert h3 using 1
        ring
      exact h4.hasDerivWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      have h5 : (1 : ℝ) / 2 - (1 + C.mu x) ≤ 0 := by
        have := C.hmu_lo x hx0
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (C.hApos x hx0).le (Real.exp_pos _).le) h5
  have hs : s ∈ Ici (0 : ℝ) := hτ.trans hτs
  have hle : C.A s * Real.exp (s / 2) ≤ C.A τ * Real.exp (τ / 2) := hanti hτ hs hτs
  have h6 : C.A s * Real.exp (s / 2) * Real.exp (-(s / 2))
      ≤ C.A τ * Real.exp (τ / 2) * Real.exp (-(s / 2)) :=
    mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  calc C.A s = C.A s * Real.exp (s / 2) * Real.exp (-(s / 2)) := by
        rw [mul_assoc, ← Real.exp_add, show s / 2 + -(s / 2) = 0 by ring, Real.exp_zero, mul_one]
    _ ≤ C.A τ * Real.exp (τ / 2) * Real.exp (-(s / 2)) := h6
    _ = C.A τ * Real.exp (τ / 2 - s / 2) := by
        rw [mul_assoc, ← Real.exp_add, show τ / 2 + -(s / 2) = τ / 2 - s / 2 by ring]

/-- The pointwise domination of the (extended) amplitude by an integrable exponential. -/
private theorem extA_bound (C : PhysClock) (a : ℝ) :
    ‖extA C a‖ ≤ extA C 0 * Real.exp (-(a / 2)) := by
  have h0 : extA C 0 = C.A 0 := by simp only [extA_apply, max_eq_left le_rfl]
  rcases lt_or_ge (0 : ℝ) a with ha | ha
  · have ha' : extA C a = C.A a := by simp only [extA_apply, max_eq_left ha.le]
    rw [ha', h0, Real.norm_of_nonneg (C.hApos a ha.le).le]
    simpa using A_decay C (le_refl 0) ha.le
  · have ha' : extA C a = C.A 0 := by simp only [extA_apply, max_eq_right ha]
    rw [ha', h0, Real.norm_of_nonneg (C.hApos 0 le_rfl).le]
    exact le_mul_of_one_le_right (C.hApos 0 le_rfl).le (Real.one_le_exp (by linarith))

/-- The (extended) amplitude is integrable on `(0,∞)`. -/
private theorem extA_integrableOn (C : PhysClock) : IntegrableOn (extA C) (Ioi (0 : ℝ)) := by
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-(s / 2))) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun s : ℝ => Real.exp ((-(1 : ℝ) / 2) * s)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by norm_num) 0
    refine h1.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show Real.exp ((-(1 : ℝ) / 2) * x) = Real.exp (-(x / 2))
    rw [show (-(1 : ℝ) / 2) * x = -(x / 2) by ring]
  have hg : Integrable (fun s : ℝ => extA C 0 * Real.exp (-(s / 2))) (volume.restrict (Ioi 0)) :=
    hexp.const_mul (extA C 0)
  refine hg.mono' ((extA_cont C).aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
  exact Eventually.of_forall fun a => extA_bound C a

/-- **Surjectivity of the clock.**  Every physical time `t ∈ [0,T)` is `t(τ)` for some fake time
`τ ≥ 0`. -/
theorem exists_t_eq (C : Work.FTS.Physical.PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    ∃ τ : ℝ, 0 ≤ τ ∧ C.t τ = t := by
  obtain ⟨ht0, htT⟩ := ht
  have hint : IntegrableOn (extA C) (Ioi (0 : ℝ)) := extA_integrableOn C
  have htend : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(n : ℝ), extA C x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), extA C x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop
  have hagree : ∀ b : ℝ, 0 ≤ b → (∫ x in (0 : ℝ)..b, C.A x) = ∫ x in (0 : ℝ)..b, extA C x := by
    intro b hb
    rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [extA_apply, max_eq_left (le_of_lt hx.1)]
  have hT : C.T = ∫ x in Ioi (0 : ℝ), extA C x := by
    rw [PhysClock.T, MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [extA_apply, max_eq_left (le_of_lt (mem_Ioi.mp hx))]
  have htend' : Tendsto (fun n : ℕ => C.t (n : ℝ)) atTop (𝓝 C.T) := by
    rw [hT]
    refine Filter.Tendsto.congr' ?_ htend
    filter_upwards with n
    exact (hagree (n : ℝ) (Nat.cast_nonneg n)).symm
  have hmem : {y : ℝ | t < y} ∈ 𝓝 C.T := isOpen_Ioi.mem_nhds htT
  obtain ⟨N, hN⟩ := (htend'.eventually hmem).exists
  have hcont : Continuous fun b : ℝ => ∫ x in (0 : ℝ)..b, extA C x :=
    intervalIntegral.continuous_primitive (fun a b => (extA_cont C).intervalIntegrable a b) 0
  have hcontOn : ContinuousOn C.t (Icc (0 : ℝ) (N : ℝ)) := by
    refine hcont.continuousOn.congr fun b hb => ?_
    exact hagree b hb.1
  have h0N : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmem' : t ∈ Icc (C.t 0) (C.t (N : ℝ)) := by
    rw [PhysClock.t_zero]
    exact ⟨ht0, hN.le⟩
  obtain ⟨τ, hτmem, hτeq⟩ := intermediate_value_Icc h0N hcontOn hmem'
  exact ⟨τ, hτmem.1, hτeq⟩

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.hasDerivAt_t =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Clock

/-- **`t' = A`**: the physical time `t(τ) = ∫₀^τ A` is differentiable with derivative `A(τ)` in the
interior of the fake-time half-line.  This is the fundamental theorem of calculus for the upper
limit of an interval integral, `A` being continuous at `τ` by `PhysClock.hAcont` and `0 < τ`. -/
theorem hasDerivAt_t (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 < τ) : HasDerivAt C.t (C.A τ) τ := by
  -- `A` is interval-integrable on `[0,τ]` since it is continuous there
  have hci : IntervalIntegrable C.A MeasureTheory.volume 0 τ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hτ.le]
    exact C.hAcont.mono Set.Icc_subset_Ici_self
  -- `τ` lies in the interior of `[0,∞)`, so continuity on `[0,∞)` gives continuity at `τ`
  have hcont : ContinuousAt C.A τ :=
    (C.hAcont.continuousWithinAt (Set.mem_Ici.mpr hτ.le)).continuousAt
      (Filter.mem_of_superset (isOpen_Ioi.mem_nhds hτ) Set.Ioi_subset_Ici_self)
  have hsm : StronglyMeasurableAtFilter C.A (nhds τ) MeasureTheory.volume :=
    C.hAcont.mono Set.Ioi_subset_Ici_self |>.stronglyMeasurableAtFilter isOpen_Ioi τ
      (Set.mem_Ioi.mpr hτ)
  exact intervalIntegral.integral_hasDerivAt_right hci hsm hcont

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.t_strictMonoOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set MeasureTheory
open scoped Interval

namespace Work.FTS.Physical.Clock

/-- **The clock is strictly increasing in fake time.**  For `0 ≤ a < b` one has
`t a < t b`: the increment is `∫_a^b A > 0` since `A > 0` on the fake-time half-line. -/
theorem t_strictMonoOn (C : Work.FTS.Physical.PhysClock) : StrictMonoOn C.t (Set.Ici 0) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  -- `A` is continuous on `[a,b]`, hence interval integrable there
  have hint : IntervalIntegrable C.A volume a b :=
    (C.hAcont.mono fun x hx => le_trans ha0 hx.1).intervalIntegrable_of_Icc hab.le
  -- the integral of the (strictly positive, continuous) amplitude over `[a,b]` is positive
  have hpos : 0 < ∫ s in a..b, C.A s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint
      (fun x hx => C.hApos x (le_trans ha0 hx.1.le)) hab
  -- additivity of the interval integral splits `t b = t a + ∫_a^b A`
  have hsplit : C.t b = C.t a + ∫ s in a..b, C.A s := by
    rw [Work.FTS.Physical.PhysClock.t, Work.FTS.Physical.PhysClock.t,
      ← intervalIntegral.integral_add_adjacent_intervals
        ((C.hAcont.mono fun x hx => hx.1).intervalIntegrable_of_Icc ha0) hint]
  linarith

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.tendsto_t_atTop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Clock

open MeasureTheory Filter Topology Set
open scoped Topology

set_option autoImplicit false

/-! ## Elementary consequences of the modulation bounds -/




/-! ## The clock exhausts the blow-up interval -/


end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Liouville =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical


end Work.FTS.Physical
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.CurlCLM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

/-- The canonical continuous linear identification `ℝ³ ≃L[ℝ] (Fin 3 → ℝ)`: its underlying
function is `WithLp.ofLp`. -/
noncomputable abbrev euclidEquiv : R3 ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ

/-- `WithLp.ofLp` as a continuous linear map `ℝ³ →L[ℝ] (Fin 3 → ℝ)`. -/
noncomputable abbrev ofLpCLM : R3 →L[ℝ] (Fin 3 → ℝ) := (euclidEquiv : R3 →L[ℝ] (Fin 3 → ℝ))

/-- `WithLp.toLp 2` as a continuous linear map `(Fin 3 → ℝ) →L[ℝ] ℝ³`. -/
noncomputable abbrev toLpCLM : (Fin 3 → ℝ) →L[ℝ] R3 := (euclidEquiv.symm : (Fin 3 → ℝ) →L[ℝ] R3)

theorem ofLpCLM_apply (x : R3) : ofLpCLM x = x.ofLp := rfl

theorem toLpCLM_apply (X : Fin 3 → ℝ) : toLpCLM X = WithLp.toLp 2 X := rfl


/-- `WithLp.toLp 2` commutes with the (three-term) sum in the definition of the curl. -/
theorem toLp_sum3 (f : Fin 3 → (Fin 3 → ℝ)) :
    WithLp.toLp 2 (∑ i, f i) = ∑ i, WithLp.toLp 2 (f i) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp

/-- The continuous linear map `v ↦ a × v` on `ℝ³`. -/
noncomputable def crossCLM (a : R3) : R3 →L[ℝ] R3 :=
  toLpCLM.comp (((crossProduct a.ofLp).toContinuousLinearMap).comp ofLpCLM)

theorem crossCLM_apply (a v : R3) : crossCLM a v = WithLp.toLp 2 (a ⨯₃ v) := by
  simp only [crossCLM, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    ofLpCLM_apply, toLpCLM_apply]

/-- **The curl as a continuous linear map of the derivative**:
`curlCLM T = ∑ i, eᵢ × (T eᵢ)`. -/
noncomputable def curlCLM : (R3 →L[ℝ] R3) →L[ℝ] R3 :=
  ∑ i : Fin 3, (crossCLM (FiniteTimeSingularity.e i)).comp
    (ContinuousLinearMap.apply ℝ R3 (FiniteTimeSingularity.e i))

/-- The same function as `curlCLM`, written with the standard basis and the canonical
identification `euclidEquiv : ℝ³ ≃L[ℝ] (Fin 3 → ℝ)`. -/
noncomputable def curlOf (T : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2
    ((∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i))) : Fin 3 → ℝ)

theorem curlOf_apply (T : R3 →L[ℝ] R3) :
    curlOf T =
      WithLp.toLp 2 (∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i))) :=
  rfl

theorem curlCLM_eq_curlOf (T : R3 →L[ℝ] R3) : curlCLM T = curlOf T := by
  have h1 : curlCLM T =
      ∑ i : Fin 3,
        WithLp.toLp 2 (FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i))) := by
    simp only [curlCLM, sum_apply, ContinuousLinearMap.comp_apply, crossCLM_apply,
      ContinuousLinearMap.apply_apply]
  rw [h1, curlOf_apply, toLp_sum3]

/-- `vorticity u x = curlCLM (fderiv ℝ u x)`: the definition of the curl, with the sum of cross
products repackaged as a continuous linear map of the derivative. -/
theorem vorticity_eq_curlCLM (u : R3 → R3) (x : R3) :
    vorticity u x = curlCLM (fderiv ℝ u x) := by
  rw [curlCLM_eq_curlOf, curlOf_apply]
  rfl



end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.RadialPrim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical


end Work.FTS.Physical
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.fderiv_symm_of_vorticity_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

open FiniteTimeSingularity
open scoped Matrix

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary basis and linear-algebra facts -/

/-- The inner product on `ℝ³` in coordinates: `⟪x, y⟫ = ∑ k, y k * x k`. -/
private lemma inner_eq_sum (x y : 𝔼) : inner ℝ x y = ∑ k : Fin 3, y k * x k := by
  simp [PiLp.inner_apply]



/-! ## The coordinates of the curl

The definition of `vorticity` is `∑ i, e i × (L (e i))`; in the standard basis its three
coordinates are the classical curl components. -/





/-! ## The target lemma -/


end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.integral_radial_eq_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Pressure


end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.vorticity_timeDeriv_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂ₜ (∇ × u(·,t)) = ∇ × (∂ₜ u)(·,t)` on `ℝ³`

The vorticity of a space-time velocity field commutes with the time derivative: if
`f = uncurry u : ℝ³ × ℝ → ℝ³` is `C²` near `(x,t)`, then

  `deriv (fun s => vorticity (fun y => u y s) x) t = vorticity (fun y => deriv (fun s => u y s) t) x`.

Both sides are the mixed second derivative `∂ₓ∂ₜ f` contracted with the curl
`∑ᵢ eᵢ ⨯₃ (·)`: the content of the lemma is exactly the symmetry of the second
derivative of `f` (`ContDiffAt.isSymmSndFDerivAt`) together with the two chain rules
that express `∂ₜ (fderiv ℝ f (x,·))` and `fderiv ℝ (∂ₜ f(·,t))` at the point `(x,t)`.

The curl `vorticity u x = ∑ᵢ eᵢ ⨯₃ (fderiv ℝ u x eᵢ)` is *linear* in `fderiv ℝ u x`, so
it is packaged here as the continuous linear map `curlCLMT` (built from `WithLp.toLp`,
`WithLp.ofLp` and the cross product, all of which are continuous linear in finite
dimension).  This lets the time derivative pass through the whole curl in one step.
-/

open scoped Matrix
open Filter Topology

namespace Work.FTS.Physical.Pressure

/-! ## Plumbing: the curl as a continuous linear map -/










/-! ## The three analytic inputs -/




/-! ## The theorem -/


end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.PressureOn.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- `ℝ³`, definitionally `Work.LWP.R3` and `Work.FTS.Physical.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The open set on which the pointwise vorticity equation is available -/

/-- **The complement of the singular set.**  `Uax` is `ℝ³` with the axis `x₀ = x₁ = 0` and the
plane `x₂ = 0` removed.  On `Uax` the paper's meridian coordinates are non-degenerate and the
pointwise vorticity equation `∂_tω + (u·∇)ω = (ω·∇)u` is available; its complement is a union of a
plane and a line, hence null. -/
def Uax : Set R3 := {x | x 2 ≠ 0 ∧ x 0 ^ 2 + x 1 ^ 2 ≠ 0}

/-- `Uax` is open (the complement of a plane and of a line). -/
theorem isOpen_Uax : IsOpen Uax := by
  have hc0 : Continuous fun x : R3 => x 0 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 0
  have hc1 : Continuous fun x : R3 => x 1 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 1
  have hc2 : Continuous fun x : R3 => x 2 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2
  have h1 : IsOpen {x : R3 | x 2 ≠ 0} :=
    isOpen_compl_iff.mpr (isClosed_eq hc2 continuous_const)
  have h2 : IsOpen {x : R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} := by
    have hcl : IsClosed {x : R3 | x 0 ^ 2 + x 1 ^ 2 = 0} :=
      isClosed_eq ((hc0.pow 2).add (hc1.pow 2)) continuous_const
    simpa only [ne_eq, Set.compl_ofPred] using isOpen_compl_iff.mpr hcl
  have : Uax = {x : R3 | x 2 ≠ 0} ∩ {x : R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} := rfl
  rw [this]
  exact h1.inter h2

/-! ## The Newtonian kernel and the scalar potential `q` -/

/-- **The gradient of the Newtonian kernel `N = (4π‖·‖)⁻¹`**: `∇N z = −z/(4π‖z‖³)`. -/
noncomputable def newtonGrad (z : R3) : R3 := -((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z

/-- **The gradient of the fundamental solution `Nfund = −(4π‖·‖)⁻¹`** (the normalisation with
`Δ Nfund = δ₀`): `∇Nfund z = z/(4π‖z‖³) = −newtonGrad z`.  The design's potential is
`q = −(∇Nfund)∗(u×ω)`. -/
noncomputable def nablaNfund (z : R3) : R3 := ((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z

@[simp] theorem nablaNfund_eq_neg_newtonGrad (z : R3) : nablaNfund z = -newtonGrad z := by
  unfold nablaNfund newtonGrad
  simp

/-- **The scalar potential of the pressure reconstruction**, the design's
`q = −(∇Nfund)∗(u×ω)`: `q x = −∫ ⟪∇Nfund(x−y), f y⟫ dy = ∫ ⟪newtonGrad(x−y), f y⟫ dy`.  It is
the decaying solution of the Poisson equation `Δq = −div f` (see the module docstring). -/
noncomputable def pressurePotential (f : R3 → R3) (x : R3) : ℝ :=
  -∫ y, inner ℝ (nablaNfund (x - y)) (f y)

/-- The kernel form of the potential: `q x = ∫ ⟪newtonGrad(x−y), f y⟫ dy`.  This is the form in
which the kernel bounds are stated. -/
theorem pressurePotential_eq_integral_newtonGrad (f : R3 → R3) (x : R3) :
    pressurePotential f x = ∫ y, inner ℝ (newtonGrad (x - y)) (f y) := by
  have h : (fun y => inner ℝ (nablaNfund (x - y)) (f y))
      = fun y => -inner ℝ (newtonGrad (x - y)) (f y) := by
    funext y
    rw [nablaNfund_eq_neg_newtonGrad, inner_neg_left]
  rw [pressurePotential, h, integral_neg, neg_neg]

/-- **The Lamb vector** of the velocity/vorticity pair, as a space-time field. -/
noncomputable def lamb (u ω : R3 → ℝ → R3) : R3 → ℝ → R3 :=
  fun x t => WithLp.toLp 2 (u x t ⨯₃ ω x t)

/-- **The pressure of the reconstruction**: `p := −‖u‖²/2 − q` with `q` the Newtonian potential of
the Lamb vector `u × ω` of `u = physVel ω`. -/
noncomputable def pressureOn (ω : R3 → ℝ → R3) : R3 → ℝ → ℝ := fun x t =>
  -(‖physVel ω x t‖ ^ 2 / 2)
    - pressurePotential (fun y => WithLp.toLp 2 (physVel ω y t ⨯₃ ω y t)) x

@[simp] theorem newtonGrad_apply (z : R3) :
    newtonGrad z = -((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z := rfl

@[simp] theorem pressurePotential_apply (f : R3 → R3) (x : R3) :
    pressurePotential f x = -∫ y, inner ℝ (nablaNfund (x - y)) (f y) := rfl

@[simp] theorem lamb_apply (u ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    lamb u ω x t = WithLp.toLp 2 (u x t ⨯₃ ω x t) := rfl

@[simp] theorem pressureOn_apply (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    pressureOn ω x t = -(‖physVel ω x t‖ ^ 2 / 2)
      - pressurePotential (fun y => WithLp.toLp 2 (physVel ω y t ⨯₃ ω y t)) x := rfl


/-- The pointwise size of the kernel: `‖∇N(z)‖ = (4π)^{-1}‖z‖^{-2}`.  This is the `L²`-marginal
kernel which makes the convolution integral conditionally convergent at infinity and integrable
over the (bounded) support of the Lamb vector. -/
theorem norm_newtonGrad (z : R3) :
    ‖newtonGrad z‖ = (4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖ := by
  rw [newtonGrad_apply, norm_smul, norm_neg]
  have h : ‖((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ : ℝ)‖
      = (4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
  rw [h]

/-! ## The statement of the pressure reconstruction -/

/-- **Pressure reconstruction on the physical solution (design §1).**

For a physical vorticity field `ω` whose Biot–Savart velocity `u = physVel ω` is jointly `C^{1,α}`
on the strips `ℝ³ × [0,S]`, `S < T`, is the curl of `ω` at every time, is divergence-free, and is
compactly supported on every strip; and whose time derivative `∂_tω` is jointly continuous on
`ℝ³ × [0,T)` (with `ω x` differentiable in `t` from the right at every `t ∈ [0,T)`, and `Dω(·,t)`
locally integrable), and which solves the vorticity equation pointwise on the open set `Uax` (the
complement of the axis and of the plane, a null set) — there is a pressure `p`, jointly `C¹` on
`ℝ³ × [0,T)`, with `∂_t u + (u·∇)u + ∇p = 0` on `ℝ³ × (0,T)`.

The extra hypotheses are exactly what excludes the two counterexamples to the old
`Work.LWP.PressureReconstruction`: the `HasDerivWithinAt` clause excludes the Cantor-staircase
shear (whose `∂_tω` is not a derivative), and `u = physVel ω` excludes the `u = (a(t),0,0)` field
(which is not the Biot–Savart field of its vorticity).  The pressure is the explicit
`pressureOn ω = −‖u‖²/2 − q`, `q = −(∇N)∗(u×ω)`. -/
def PressureReconstructionOn (α : ℝ≥0) : Prop := ∀ (ω : R3 → ℝ → R3) (T : ℝ),
  let u := physVel ω
  (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
  (∀ t ∈ Ico 0 T, ∀ x, vorticity (u · t) x = ω x t) → (∀ t ∈ Ico 0 T, div (u · t) = 0) →
  (∀ S ∈ Ioo 0 T, ∃ R, ∀ t ∈ Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R) →
  ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2) (univ ×ˢ Ico 0 T) →
  (∀ x, ∀ t ∈ Ico 0 T, HasDerivWithinAt (ω x) (timeDeriv ω x t) (Ici t) t) →
  (∀ t ∈ Ioo 0 T, LocallyIntegrable (fun x => fderiv ℝ (ω · t) x)) →
  (∀ t ∈ Ioo 0 T, ∀ x ∈ Uax, ContDiffAt ℝ 2 (u · t) x ∧ ContDiffAt ℝ 1 (ω · t) x ∧
     timeDeriv ω x t + directionalDeriv ω u x t = directionalDeriv u ω x t) →
  ∃ p, ContDiffOn ℝ 1 p.uncurry (univ ×ˢ Ico 0 T) ∧
    ∀ x, ∀ t ∈ Ioo 0 T, timeDeriv u x t + directionalDeriv u u x t + spaceGrad p x t = 0

/-! ## The Newtonian kernel and the Hessian trace -/

/-- The cross product as an element of `R3` (the notation `⨯₃` returns `Fin 3 → ℝ`). -/
def crossVec (a b : R3) : R3 := WithLp.toLp 2 (a ⨯₃ b)

@[simp] theorem crossVec_apply (a b : R3) : crossVec a b = WithLp.toLp 2 (a ⨯₃ b) := rfl

/-- **The Newtonian kernel** `N z = (4π‖z‖)⁻¹`; `newtonGrad = ∇N`. -/
noncomputable def newtonKernel (z : R3) : ℝ := (4 * Real.pi * ‖z‖)⁻¹

/-- **The trace of the Hessian**, `laplaceTrace φ x = ∑ᵢ ∂ᵢ∂ᵢ φ(x)`, the Euclidean Laplacian in
the standard basis (`FiniteTimeSingularity.e i`). -/
noncomputable def laplaceTrace (φ : R3 → ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) x
    (FiniteTimeSingularity.e i)

/-- The vector-valued analogue of `laplaceTrace`. -/
noncomputable def laplaceTraceVec (g : R3 → R3) (x : R3) : R3 :=
  ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ g w (FiniteTimeSingularity.e i)) x
    (FiniteTimeSingularity.e i)

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open MeasureTheory

/-!
# The weighted `L²` Young inequality for the plane convolution

`conv_shift_sq_integral_le`: if `k` is integrable with `∫ |k| ≤ 1` and supported in the `ℓ¹`-ball
of radius `2ε`, and `Q ≥ 0` is a weight which is comparable to its translates
(`Q y ≤ e^{Cw |p|₁} Q (y + p)`), then the convolution `k * G` satisfies

  `∫ y, Q y * (∫ p, k p * G (y - p))² ≤ e^{2 Cw ε} ∫ y, Q y * G y²`,

and the left-hand side is integrable as soon as `Q G²` is.

The proof is the weighted Young inequality: the pointwise Cauchy–Schwarz estimate in the finite
measure `|k p| dp` (carried out in `ℝ≥0∞`, so that no a-priori finiteness of
`∫ p, |k p| G (y - p)²` is needed), the weight-shift bound `shiftNormLe` in the `p`-variable, and
Tonelli's theorem.
-/

/-- `x ^ (1/2) * x ^ (1/2) = x` for `x : ℝ≥0∞`. -/
theorem ennreal_half_mul_self (x : ENNReal) : x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x := by
  rcases eq_or_ne x ⊤ with h | h
  · simp [h]
  · rw [← ENNReal.rpow_add_of_add_pos h (1/2) (1/2) (by norm_num)]
    norm_num

/-- `(x ^ (1/2)) ^ 2 = x` for `x : ℝ≥0∞`. -/
theorem ennreal_half_sq (x : ENNReal) : (x ^ (1/2:ℝ)) ^ 2 = x := by
  rw [pow_two, ennreal_half_mul_self]

/-- `(x ^ 2) ^ (1/2) = x` for `x : ℝ≥0∞`. -/
theorem ennreal_sq_half (x : ENNReal) : (x ^ 2) ^ (1/2:ℝ) = x := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul,
    show ((2:ℕ):ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]

/-- **Cauchy–Schwarz for `ℝ≥0∞`-valued functions**: `(∫ A C)² ≤ (∫ A) (∫ A C²)`.

Equivalently Cauchy–Schwarz in the measure `A dμ` for the functions `1` and `C`. This is the form
of the estimate that requires no finiteness of `∫ A C²`; both sides are allowed to be `⊤`. -/
theorem ennreal_cs_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {A C : α → ENNReal}
    (hA : AEMeasurable A μ) (hC : AEMeasurable C μ) :
    (∫⁻ a, A a * C a ∂μ) ^ 2 ≤ (∫⁻ a, A a ∂μ) * ∫⁻ a, A a * (C a) ^ 2 ∂μ := by
  have hg : AEMeasurable (fun a => A a * C a ^ 2) μ := hA.mul (hC.pow_const 2)
  have hmain := ENNReal.lintegral_mul_norm_pow_le hA hg (p := 1/2) (q := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  have hL : (fun a => A a ^ (1/2:ℝ) * (A a * C a ^ 2) ^ (1/2:ℝ)) = (fun a => A a * C a) := by
    funext a
    have h1 : (A a * C a ^ 2) ^ (1/2:ℝ) = A a ^ (1/2:ℝ) * C a := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), ennreal_sq_half]
    rw [h1, ← mul_assoc, ennreal_half_mul_self]
  rw [hL] at hmain
  have hsq : (∫⁻ a, A a * C a ∂μ) * (∫⁻ a, A a * C a ∂μ)
      ≤ ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) *
        ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) :=
    mul_le_mul' hmain hmain
  calc (∫⁻ a, A a * C a ∂μ) ^ 2
      = (∫⁻ a, A a * C a ∂μ) * (∫⁻ a, A a * C a ∂μ) := pow_two _
    _ ≤ ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) *
        ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) := hsq
    _ = ((∫⁻ a, A a ∂μ) ^ (1/2:ℝ)) ^ 2 * ((∫⁻ a, A a * C a ^ 2 ∂μ) ^ (1/2:ℝ)) ^ 2 := by
        rw [← pow_two, mul_pow]
    _ = (∫⁻ a, A a ∂μ) * ∫⁻ a, A a * C a ^ 2 ∂μ := by rw [ennreal_half_sq, ennreal_half_sq]

set_option linter.unusedVariables false in
theorem conv_shift_sq_integral_le {k Q G : ℝ × ℝ → ℝ} {Cw ε : ℝ}
    (hε0 : 0 < ε) (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk1 : (∫ p : ℝ × ℝ, |k p|) ≤ 1)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hGm : Measurable G)
    (hconv : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G (y - p)))
    (hI : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G y ^ 2)) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
      ∧ (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
          ≤ Real.exp (2 * Cw * ε) * (∫ y : ℝ × ℝ, Q y * G y ^ 2) := by
  classical
  set M : ℝ := ∫ p : ℝ × ℝ, |k p| with hM
  set T : ℝ := ∫ y : ℝ × ℝ, Q y * G y ^ 2 with hT
  set E : ℝ := Real.exp (2 * Cw * ε) with hE
  have hKint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |k p|) := hk.abs
  have hK0 : ∀ p : ℝ × ℝ, 0 ≤ |k p| := fun p => abs_nonneg _
  have hM0 : 0 ≤ M := by rw [hM]; exact MeasureTheory.integral_nonneg hK0
  have hM1 : M ≤ 1 := by rw [hM]; exact hk1
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact MeasureTheory.integral_nonneg (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  have hE0 : 0 ≤ E := by rw [hE]; exact Real.exp_nonneg _
  have hkae : AEMeasurable (fun p : ℝ × ℝ => |k p|) := hk.aemeasurable.abs
  -- the forward shift bound for the weight `Q`
  have hQfwd : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y := by
    intro y p
    simpa using hQsh' (y + p) (-p)
  -- the weighted `L²` shift bound (`shiftNormLe`)
  have hshift : ∀ p : ℝ × ℝ,
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) ∧
        (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2)
          ≤ Real.exp (Cw * (|p.1| + |p.2|)) * T := by
    intro p
    have h := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.shiftNormLe
      hCw hQ0 hQm hQfwd hGm hI p
    rw [hT]
    exact h
  -- the exponential moment of the kernel
  have hKexp : ∀ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|)) ≤ |k p| * E := by
    intro p
    rcases eq_or_ne (k p) 0 with hp | hp
    · simp [hp]
    · have h1 : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
      rw [hE]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      calc Cw * (|p.1| + |p.2|) ≤ Cw * (2 * ε) := mul_le_mul_of_nonneg_left h1 hCw
        _ = 2 * Cw * ε := by ring
  have hKexpInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |k p| * Real.exp (Cw * (|p.1| + |p.2|))) := by
    refine (hKint.mul_const E).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact hk.abs.aestronglyMeasurable.mul
        ((Real.continuous_exp.measurable.comp (measurable_const.mul
          (measurable_fst.abs.add measurable_snd.abs))).aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))]
      exact hKexp p
  have hKexpBound : (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) ≤ E * M := by
    have hm := MeasureTheory.integral_mono hKexpInt (hKint.mul_const E) hKexp
    rw [MeasureTheory.integral_mul_const] at hm
    rw [hM]
    exact le_trans hm (le_of_eq (mul_comm _ _))
  -- ## the pointwise Cauchy–Schwarz bound
  have hpt : ∀ y : ℝ × ℝ, ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
      ≤ ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) := by
    intro y
    set c : ℝ := ∫ p : ℝ × ℝ, k p * G (y - p) with hc
    have hcint : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G (y - p)) := hconv y
    have hA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |k p|) := hkae.ennreal_ofReal
    have hC : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |G (y - p)|) :=
      ((hGm.comp (measurable_const.sub measurable_id)).aemeasurable.abs).ennreal_ofReal
    have hcs := ennreal_cs_sq hA hC
    -- bound the left factor by the `lintegral`
    have h1 : ENNReal.ofReal |c| ≤ ∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|) := by
      rw [hc]
      calc ENNReal.ofReal |∫ p : ℝ × ℝ, k p * G (y - p)|
          ≤ ENNReal.ofReal (∫ p : ℝ × ℝ, |k p * G (y - p)|) :=
            ENNReal.ofReal_le_ofReal MeasureTheory.abs_integral_le_integral_abs
        _ = ∫⁻ p, ENNReal.ofReal (|k p * G (y - p)|) :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcint.abs
              (Filter.Eventually.of_forall fun p => abs_nonneg _)
        _ = ∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|) :=
            MeasureTheory.lintegral_congr (fun p => by rw [abs_mul])
    -- the rewritten Cauchy–Schwarz
    have hcs' : (∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|)) ^ 2
        ≤ ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) := by
      have hL : (∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|))
          = ∫⁻ p, ENNReal.ofReal |k p| * ENNReal.ofReal |G (y - p)| :=
        MeasureTheory.lintegral_congr (fun p => ENNReal.ofReal_mul (abs_nonneg (k p)))
      have hR1 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal |k p|) = ENNReal.ofReal M := by
        rw [hM]
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hKint
          (Filter.Eventually.of_forall hK0)).symm
      have hR2 : (∫⁻ p, ENNReal.ofReal |k p| * (ENNReal.ofReal |G (y - p)|) ^ 2)
          = ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) :=
        MeasureTheory.lintegral_congr (fun p => by
          rw [← ENNReal.ofReal_pow (abs_nonneg (G (y - p))) 2, sq_abs,
            ENNReal.ofReal_mul (abs_nonneg (k p))])
      calc (∫⁻ p, ENNReal.ofReal (|k p| * |G (y - p)|)) ^ 2
          = (∫⁻ p, ENNReal.ofReal |k p| * ENNReal.ofReal |G (y - p)|) ^ 2 := by rw [hL]
        _ ≤ (∫⁻ p, ENNReal.ofReal |k p|)
              * ∫⁻ p, ENNReal.ofReal |k p| * (ENNReal.ofReal |G (y - p)|) ^ 2 := hcs
        _ = ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) := by rw [hR1, hR2]
    have h2 : (ENNReal.ofReal |c|) ^ 2
        ≤ ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) :=
      le_trans (pow_le_pow_left' h1 2) hcs'
    -- transport the weight `Q y` inside the integral
    have h3 : ENNReal.ofReal (Q y * c ^ 2) = ENNReal.ofReal (Q y) * (ENNReal.ofReal |c|) ^ 2 := by
      rw [ENNReal.ofReal_mul (hQ0 y), ← ENNReal.ofReal_pow (abs_nonneg c) 2, sq_abs]
    have h4 : ENNReal.ofReal (Q y) * (ENNReal.ofReal M
          * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2))
        = ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) := by
      have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (|k p| * G (y - p) ^ 2)) :=
        ((hkae.mul (((hGm.comp (measurable_const.sub measurable_id)).aemeasurable).pow_const 2)
          ).ennreal_ofReal)
      have hsplit : (∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
          = ENNReal.ofReal (Q y) * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2) := by
        rw [← MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (Q y)) hmeas]
        exact MeasureTheory.lintegral_congr (fun p => ENNReal.ofReal_mul (hQ0 y))
      rw [hsplit]
      ring
    calc ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
        = ENNReal.ofReal (Q y) * (ENNReal.ofReal |c|) ^ 2 := h3
      _ ≤ ENNReal.ofReal (Q y) * (ENNReal.ofReal M
            * ∫⁻ p, ENNReal.ofReal (|k p| * G (y - p) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 bot_le
      _ = ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) := h4
  -- ## measurability of the two-variable integrand
  have hΨm : AEMeasurable (Function.uncurry fun y p : ℝ × ℝ =>
      ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hQ1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Q z.1))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hQm.aemeasurable.ennreal_ofReal.comp_fst
    have hk1' : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal |k z.2|)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hkae.ennreal_ofReal.comp_snd
    have hG1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal |G (z.1 - z.2)|)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      ((hGm.comp (measurable_fst.sub measurable_snd)).aemeasurable.abs).ennreal_ofReal
    have hprod : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Q z.1) * ENNReal.ofReal |k z.2| * (ENNReal.ofReal |G (z.1 - z.2)|) ^ 2)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hQ1.mul hk1').mul (hG1.pow_const 2)
    refine hprod.congr (Filter.Eventually.of_forall fun z => ?_)
    show ENNReal.ofReal (Q z.1) * ENNReal.ofReal |k z.2| * (ENNReal.ofReal |G (z.1 - z.2)|) ^ 2
        = ENNReal.ofReal (Q z.1 * (|k z.2| * G (z.1 - z.2) ^ 2))
    rw [ENNReal.ofReal_mul (hQ0 z.1), ENNReal.ofReal_mul (abs_nonneg (k z.2)),
      ← ENNReal.ofReal_pow (abs_nonneg (G (z.1 - z.2))) 2, sq_abs]
    ring_nf
  -- ## the Tonelli computation
  have hswap : (∫⁻ y : ℝ × ℝ, ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
      = ∫⁻ p : ℝ × ℝ, ∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) :=
    MeasureTheory.lintegral_lintegral_swap hΨm
  have hinner : ∀ p : ℝ × ℝ, (∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
      = ENNReal.ofReal |k p| * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2) := by
    intro p
    have hmeas : AEMeasurable (fun y : ℝ × ℝ => ENNReal.ofReal (Q y * G (y - p) ^ 2)) :=
      (hQm.aemeasurable.mul
        (((hGm.comp (measurable_id.sub measurable_const)).aemeasurable).pow_const 2)).ennreal_ofReal
    have hpt2 : ∀ y : ℝ × ℝ, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))
        = ENNReal.ofReal |k p| * ENNReal.ofReal (Q y * G (y - p) ^ 2) := by
      intro y
      calc ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))
          = ENNReal.ofReal (Q y) * ENNReal.ofReal (|k p| * G (y - p) ^ 2) :=
            ENNReal.ofReal_mul (hQ0 y)
        _ = ENNReal.ofReal (Q y)
              * (ENNReal.ofReal |k p| * ENNReal.ofReal (G (y - p) ^ 2)) := by
            rw [ENNReal.ofReal_mul (abs_nonneg (k p))]
        _ = ENNReal.ofReal |k p| * (ENNReal.ofReal (Q y) * ENNReal.ofReal (G (y - p) ^ 2)) := by
            ring
        _ = ENNReal.ofReal |k p| * ENNReal.ofReal (Q y * G (y - p) ^ 2) := by
            rw [ENNReal.ofReal_mul (hQ0 y)]
    calc (∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)))
        = ∫⁻ y, ENNReal.ofReal |k p| * ENNReal.ofReal (Q y * G (y - p) ^ 2) :=
          MeasureTheory.lintegral_congr hpt2
      _ = ENNReal.ofReal |k p| * ∫⁻ y, ENNReal.ofReal (Q y * G (y - p) ^ 2) :=
          MeasureTheory.lintegral_const_mul'' _ hmeas
      _ = ENNReal.ofReal |k p| * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2) := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hshift p).1
            (Filter.Eventually.of_forall fun y => mul_nonneg (hQ0 y) (sq_nonneg _))]
  have hYmeas : AEMeasurable (fun y : ℝ × ℝ =>
      ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))) MeasureTheory.volume :=
    hΨm.lintegral_prod_right
  have hstep2 : (∫⁻ p, ENNReal.ofReal |k p|
        * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2))
      ≤ ∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T) := by
    refine MeasureTheory.lintegral_mono (fun p => ?_)
    have hle := mul_le_mul_of_nonneg_left (hshift p).2 (abs_nonneg (k p))
    calc ENNReal.ofReal |k p| * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2)
        = ENNReal.ofReal (|k p| * ∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2) :=
          (ENNReal.ofReal_mul (abs_nonneg (k p))).symm
      _ ≤ ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simpa [mul_assoc] using hle
  have hstep3 : (∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T))
      = ENNReal.ofReal ((∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T) := by
    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)))) :=
      hKexpInt.aemeasurable.ennreal_ofReal
    have hX0 : 0 ≤ ∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|)) :=
      MeasureTheory.integral_nonneg (fun p => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
    calc (∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T))
        = ∫⁻ p, ENNReal.ofReal T
            * ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|))) := by
          refine MeasureTheory.lintegral_congr (fun p => ?_)
          rw [ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)), mul_comm]
      _ = ENNReal.ofReal T
            * ∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|))) :=
          MeasureTheory.lintegral_const_mul'' _ hmeas
      _ = (∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)))) * ENNReal.ofReal T :=
          mul_comm _ _
      _ = ENNReal.ofReal (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|)))
            * ENNReal.ofReal T := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hKexpInt
            (Filter.Eventually.of_forall fun p =>
              mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))]
      _ = ENNReal.ofReal ((∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T) :=
          (ENNReal.ofReal_mul hX0).symm
  have hMid : (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T ≤ E * T := by
    have h1 : (∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T ≤ (E * M) * T :=
      mul_le_mul_of_nonneg_right hKexpBound hT0
    have h3 : M * T ≤ 1 * T := mul_le_mul_of_nonneg_right hM1 hT0
    have h2 : (E * M) * T ≤ E * T := by nlinarith [hE0, hM0, hT0, h3]
    exact le_trans h1 h2
  have hEnd : M * (E * T) ≤ E * T := by
    have h3 : M * (E * T) ≤ 1 * (E * T) := mul_le_mul_of_nonneg_right hM1 (mul_nonneg hE0 hT0)
    simpa using h3
  have hlin : (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2))
      ≤ ENNReal.ofReal (E * T) := by
    calc (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2))
        ≤ ∫⁻ y : ℝ × ℝ, ENNReal.ofReal M
            * ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2)) :=
          MeasureTheory.lintegral_mono hpt
      _ = ENNReal.ofReal M * (∫⁻ y : ℝ × ℝ,
            ∫⁻ p, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))) :=
          MeasureTheory.lintegral_const_mul'' _ hYmeas
      _ = ENNReal.ofReal M * (∫⁻ p : ℝ × ℝ,
            ∫⁻ y, ENNReal.ofReal (Q y * (|k p| * G (y - p) ^ 2))) := by rw [hswap]
      _ = ENNReal.ofReal M * (∫⁻ p, ENNReal.ofReal |k p|
            * ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2)) := by
          rw [MeasureTheory.lintegral_congr hinner]
      _ ≤ ENNReal.ofReal M
            * ∫⁻ p, ENNReal.ofReal (|k p| * Real.exp (Cw * (|p.1| + |p.2|)) * T) :=
          mul_le_mul_of_nonneg_left hstep2 bot_le
      _ = ENNReal.ofReal M
            * ENNReal.ofReal ((∫ p : ℝ × ℝ, |k p| * Real.exp (Cw * (|p.1| + |p.2|))) * T) := by
          rw [hstep3]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (E * T) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hMid) bot_le
      _ = ENNReal.ofReal (M * (E * T)) := (ENNReal.ofReal_mul hM0).symm
      _ ≤ ENNReal.ofReal (E * T) := ENNReal.ofReal_le_ofReal hEnd
  -- ## conclusion
  have hFmeas : AEStronglyMeasurable
      (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2) MeasureTheory.volume := by
    have hjoint : AEStronglyMeasurable
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * G (z.1 - z.2))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hk.aestronglyMeasurable.comp_snd).mul
        ((hGm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable)
    have hconvmeas : AEStronglyMeasurable
        (fun y : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * G (y - p)) MeasureTheory.volume :=
      hjoint.integral_prod_right'
    exact hQm.aestronglyMeasurable.mul (hconvmeas.pow 2)
  have hFnn : 0 ≤ᵐ[MeasureTheory.volume]
      (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2) :=
    Filter.Eventually.of_forall (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  refine ⟨(MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hFmeas hFnn).mp ?_, ?_⟩
  · exact ne_top_of_lt (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
  · calc (∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)
        = (∫⁻ y : ℝ × ℝ,
            ENNReal.ofReal (Q y * (∫ p : ℝ × ℝ, k p * G (y - p)) ^ 2)).toReal :=
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae hFnn hFmeas
      _ ≤ (ENNReal.ofReal (E * T)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = E * T := ENNReal.toReal_ofReal (mul_nonneg hE0 hT0)
      _ = Real.exp (2 * Cw * ε) * (∫ y : ℝ × ℝ, Q y * G y ^ 2) := by rw [hE, hT]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
