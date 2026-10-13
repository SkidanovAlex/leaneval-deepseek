/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak.aeSigmaUpgradeRho` — the `ρ`-form of the `σ`-upgrade of the level-`0` mass

The statement is the `u`-half of Step 1 of Proposition `prop:H2` of Elgindi's paper in the
*weak* (`AeData`) class, in the *weakest* possible hypothesis form: instead of asking for the
honesty of the angular slice `θ ↦ (∂_θu(z,θ)·w(z))²` in `z` (the `L2Mem` hypothesis of
`Work.FTS.EllipticEst.H2W.Ae.aeSigmaUp`), one only assumes that the *totalised* integral

`z ↦ (w z)² · ∫_θ (∂_θu(z,θ))²`

is integrable on `(0,∞)`.  The conclusion is the `ρ`-form of the `σ`-upgrade,

`HkSq α 0 u ≤ C · ∫_{z>0} (w z)² ∫_θ (∂_θu(z,θ))²`,

i.e. the singular angular weight `σ θ = sin(2θ)^{-η}` of the left-hand side is traded for the
*unweighted* angular integral of `∂_θu`, at the price of the universal constant `C`.

The passage from the weak hypothesis to the honest one is where the work is.  The key point is
that in the class `AeData` the right-hand side can never be the junk value `0` attached by
Lean's totalised Bochner integral to a non-integrable function: `AeData` contains
`HkMem α 0 (∂_θθu)`, which for `z > 0` says that `(∂_θθu(z,·))²σ` is integrable; since
`σ ≥ 1` on each compact subinterval and `σ^{-1} = sin(2θ)^{η}` is integrable on `Iθ`, the
Cauchy–Schwarz bound makes `∂_θθu(z,·) ∈ L¹`, so `∂_θu(z,·)` has finite endpoint limits and
is therefore *bounded* on `(0,π/2)`; a bounded function on the finite measure space `Iθ` is
square integrable.  This is exactly `Work.FTS.EllipticEst.Honest.SliceBddSqSigma`, and it
gives the per-slice honesty clause of `L2Mem`; the `z`-integrability clause follows from the
hypothesis because `w z` does not depend on `θ`, hence

`∫_θ (∂_θu(z,θ)·w z)² = (w z)² ∫_θ (∂_θu(z,θ))²`

(pointwise in `z`, with the same reading of the two totalised integrals in the degenerate
case).  Then `H2W.Ae.aeSigmaUp` applies, and the two `L²Sq`-forms are identified.

Nothing here uses the equation, the moment conditions or the radial data: only the angular
`HkMem` honesty of `∂_θθu`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaUp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## Elementary facts about the two `θ`-integrals and the two radial domains -/

/-- The two angular integrals of the statement agree pointwise in `z`, because `w z` does not
depend on `θ`.  (`integral_const_mul` is unconditional, so this needs no integrability.) -/
private theorem slice_w_sq_eq (u : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2) := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-- `Iz = [0,∞)` and `Ioi 0` carry the same measure (`{0}` is null). -/
private theorem restrict_Iz_eq_restrict_Ioi :
    MeasureTheory.volume.restrict Iz = MeasureTheory.volume.restrict (Set.Ioi 0) := by
  rw [Work.Spaces.Iz]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]

/-- Honesty on `Iz` from honesty on the smaller set `Ioi 0`. -/
private theorem integrableOn_Iz_of_Ioi {f : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn f (Set.Ioi 0)) : MeasureTheory.IntegrableOn f Iz := by
  show MeasureTheory.Integrable f (MeasureTheory.volume.restrict Iz)
  rw [restrict_Iz_eq_restrict_Ioi]
  exact h

/-! ## The per-slice honesty of `∂_θu` -/

/-- **For `z > 0` the angular slice of `∂_θu` is square-integrable.**  The `HkMem`-honesty of
`∂_θθu` (which `AeData` supplies) makes `(∂_θθu(z,·))²σ` integrable, hence `∂_θθu(z,·) ∈ L¹`
by Cauchy–Schwarz against `σ^{-1} = sin(2θ)^{η} ∈ L¹`; then `∂_θu(z,·)` has finite endpoint
limits and is bounded (`SliceBddSqSigma`), and a bounded function on `Iθ` is square
integrable. -/
private theorem slice_pth_sq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Iθ := by
  have hsm2 : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have h0 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma h.memAng2 hz
    simpa only [Work.Spaces.pth, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Nat.reduceAdd] using h0
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.EllipticEst.Honest.SliceBddSqSigma hsm2 h2
  have hvol : (MeasureTheory.volume : Measure ℝ) Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine MeasureTheory.IntegrableOn.of_bound hvol
    ((measurable_deriv (fun t : ℝ => u z t)).aestronglyMeasurable.pow 2) (C ^ 2) ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc (deriv (fun t : ℝ => u z t) θ) ^ 2
      = |deriv (fun t : ℝ => u z t) θ| ^ 2 := by rw [sq_abs]
    _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC θ hθ).1 2

/-! ## The `L2Mem` hypothesis of `aeSigmaUp` from the weak integral hypothesis -/

/-- The weak hypothesis `IntegrableOn (z ↦ (w z)² ∫_θ (∂_θu)²) (Ioi 0)` upgrades to the
`L2Mem`-honesty of `∂_θu · w`: the `z`-clause is the pointwise identity `slice_w_sq_eq`, and
the per-slice clause is `slice_pth_sq_integrable` (for `z > 0`; at `z = 0` the factor `w 0 = 0`
makes the slice vanish identically). -/
private theorem l2Mem_pth_mul_w {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hInt : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)) (Set.Ioi 0)) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      have hzero : (fun θ => (Work.Spaces.pth u 0 θ * Work.Spaces.w 0) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · have hslice := slice_pth_sq_integrable h hzpos
      have h1 : MeasureTheory.Integrable
          (fun θ => (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth u z θ) ^ 2)
          (MeasureTheory.volume.restrict Iθ) :=
        MeasureTheory.Integrable.const_mul hslice ((Work.Spaces.w z) ^ 2)
      refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
      ring
  · have hIntIz : MeasureTheory.Integrable
        (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2))
        (MeasureTheory.volume.restrict Iz) := integrableOn_Iz_of_Ioi hInt
    refine hIntIz.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (slice_w_sq_eq u z).symm

/-! ## The target -/

theorem aeSigmaUpgradeRho : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)) (Set.Ioi 0) →
      Work.Spaces.HkSq α 0 u ≤ C * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.H2W.Ae.aeSigmaUp
  refine ⟨C, hCpos, fun α u G h hInt => ?_⟩
  have hmain := hC α u G h (l2Mem_pth_mul_w h hInt)
  have hconv : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) := by
    rw [Work.Spaces.L2Sq]
    trans ∫ z in Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
    · exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici
        (fun z _ => slice_w_sq_eq u z)
    · rw [restrict_Iz_eq_restrict_Ioi]
  rwa [hconv] at hmain

end Work.FTS.EllipticEst.AngAWeak
