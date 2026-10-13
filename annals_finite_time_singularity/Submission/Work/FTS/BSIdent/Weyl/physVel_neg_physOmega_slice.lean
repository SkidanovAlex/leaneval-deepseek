/-
# The physical velocity slice of the negated vorticity is its Biot–Savart field

This is the *analytic* half of the Weyl route (`Submission/Work/FTS/BSIdent/Weyl.lean`, route C):
for a `RegPkg` regularity package `α, S, A, B, g` and a physical time `t` whose fake time
`clockInv C t` lies in the strip `[0,S]`, the slice

  `−(physOmega α A B g C) · t`

of the negated physical vorticity is a bounded, compactly supported, `α`-Hölder **swirl** field
(the physical vorticity is `A(τ)⁻¹ • profile (3α) (gSlice g τ) (ρ^{3α}/B τ) • e_θ`, and negation
commutes with the swirl representation), so the whole `BSSwirl` chapter applies to it:

* `physVel (−physOmega) · t = BS ω` is `C¹` (`biotSavart_contDiff_one`),
* `∇ × (BS ω) = ω` (`vorticity_biotSavart_of_weakDivFree`),
* `div (BS ω) = 0` (`div_biotSavart_eq_zero`),
* `‖BS ω x‖ ≤ C/(1+‖x‖²)`, hence `BS ω → 0` at infinity (`biotSavart_decay`).

The only new ingredient relative to `vorticity_and_div_biotSavart_physVort` and
`physVel_slice_continuous_decay` (the same statements for the *unnegated* slice) is that the four
data of the swirl field (`bound`, `support`, `Hölder`, weak divergence-freeness) are stable under
pointwise negation: the first three are immediate from `‖−a‖ = ‖a‖` and `−a ≠ 0 ↔ a ≠ 0`, and the
last one is `weakDivFree_neg` below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.Regularity.physVort_support
import Submission.Work.FTS.Regularity.physVort_bound
import Submission.Work.FTS.Regularity.physVort_holder_slice
import Submission.Work.FTS.BSIdent.Weyl.physVort_slice_eq_swirlField
import Submission.Work.FTS.BSSwirl.Main
import Submission.Work.FTS.Physical.Omega
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one
import Submission.Work.FTS.PressureOn.biotSavart_decay

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Filter Gradient
open scoped Topology

/-- **Weak divergence-freeness is stable under pointwise negation.**  If `∫ ⟪ω, ∇k⟫ = 0` for every
smooth compactly supported `k`, the same holds for `−ω`, since both the inner product
(`inner_neg_left`) and the integral (`integral_neg`) are additive in the field. -/
private theorem weakDivFree_neg {ω : R3 → R3} (h : Work.FTS.BSSwirl.WeakDivFree ω) :
    Work.FTS.BSSwirl.WeakDivFree (fun x => -ω x) := by
  intro k hk hks
  have h1 := h k hk hks
  have h2 : (fun x => inner ℝ (-ω x) (gradient k x))
      = fun x => -(inner ℝ (ω x) (gradient k x)) := by
    funext x
    rw [inner_neg_left]
  rw [h2, integral_neg, h1, neg_zero]

theorem physVel_neg_physOmega_slice {α : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {C : Work.FTS.Physical.PhysClock} {S t : ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g)
    (hτ : Work.FTS.Physical.clockInv C t ∈ Set.Icc 0 S) :
    ContDiff ℝ 1 (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t)
      ∧ (∀ x : Work.FTS.BSIdent.R3,
          FiniteTimeSingularity.vorticity
            (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t) x
          = -(Work.FTS.Physical.physOmega α A B g C x t))
      ∧ (∀ x : Work.FTS.BSIdent.R3,
          FiniteTimeSingularity.div
            (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t) x = 0)
      ∧ Filter.Tendsto (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t)
          (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
  -- the four quantitative data of the unnegated physical vorticity slice
  obtain ⟨M, hM0, hbdd0⟩ := Work.FTS.Regularity.physVort_bound h
  obtain ⟨R, hR0, hsupp0⟩ := Work.FTS.Regularity.physVort_support h
  obtain ⟨Cd, hCd0, hhold0⟩ := Work.FTS.Regularity.physVort_holder_slice h
  -- the slice of `physVel` is the Biot–Savart field of the negated vorticity slice
  have hslice : (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t)
      = Work.LWP.biotSavart (fun y : Work.FTS.BSIdent.R3 =>
          -(Work.FTS.Regularity.physVort α A B g y (Work.FTS.Physical.clockInv C t))) := by
    funext x; rfl
  -- abbreviate the negated vorticity slice
  let ω : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3 := fun y =>
    -(Work.FTS.Regularity.physVort α A B g y (Work.FTS.Physical.clockInv C t))
  have hbdd : ∀ y : Work.FTS.BSIdent.R3, ‖ω y‖ ≤ M := fun y => by
    simp only [ω, norm_neg]
    exact hbdd0 _ hτ y
  have hsupp : ∀ y : Work.FTS.BSIdent.R3, ω y ≠ 0 → y ∈ Metric.closedBall 0 R := fun y hy => by
    simp only [ω] at hy
    exact hsupp0 _ hτ y (by simpa using hy)
  have hhold : ∀ a b : Work.FTS.BSIdent.R3, ‖ω a - ω b‖ ≤ Cd * ‖a - b‖ ^ α := fun a b => by
    have h2 : ω a - ω b
        = -(Work.FTS.Regularity.physVort α A B g a (Work.FTS.Physical.clockInv C t)
            - Work.FTS.Regularity.physVort α A B g b (Work.FTS.Physical.clockInv C t)) := by
      simp only [ω]; abel
    rw [h2, norm_neg]
    exact hhold0 _ hτ a b
  have hcontω : Continuous ω := Work.FTS.BSSwirl.continuous_of_holder_pointwise h.hα hhold
  have hmeas : AEStronglyMeasurable ω volume := hcontω.aestronglyMeasurable
  -- the negated slice is a swirl field: `physVort · τ = swirlField φ`, hence `ω = −swirlField φ`
  let φ : ℝ → ℝ → ℝ := fun r z => (A (Work.FTS.Physical.clockInv C t))⁻¹ *
      Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
  have hsw : (Work.FTS.Regularity.physVort α A B g · (Work.FTS.Physical.clockInv C t))
      = Work.FTS.BSSwirl.swirlField φ :=
    physVort_slice_eq_swirlField α (Work.FTS.Physical.clockInv C t) A B g
  have hbdd_sw : ∀ x : Work.FTS.BSIdent.R3, ‖Work.FTS.BSSwirl.swirlField φ x‖ ≤ M := fun x => by
    rw [← congrFun hsw x]; exact hbdd0 _ hτ x
  have hsupp_sw : ∀ x : Work.FTS.BSIdent.R3,
      Work.FTS.BSSwirl.swirlField φ x ≠ 0 → x ∈ Metric.closedBall 0 R :=
    fun x hx => hsupp0 _ hτ x (by rwa [← congrFun hsw x] at hx)
  have hhold_sw : ∀ a b : Work.FTS.BSIdent.R3,
      ‖Work.FTS.BSSwirl.swirlField φ a - Work.FTS.BSSwirl.swirlField φ b‖
        ≤ Cd * ‖a - b‖ ^ α := fun a b => by
    rw [← congrFun hsw a, ← congrFun hsw b]; exact hhold0 _ hτ a b
  have hmeas_sw : AEStronglyMeasurable (Work.FTS.BSSwirl.swirlField φ) volume :=
    (Work.FTS.BSSwirl.continuous_of_holder_pointwise h.hα hhold_sw).aestronglyMeasurable
  have hdiv_sw : Work.FTS.BSSwirl.WeakDivFree (Work.FTS.BSSwirl.swirlField φ) :=
    Work.FTS.BSSwirl.weakDivFree_swirlField hM0 hR0.le hbdd_sw hmeas_sw hsupp_sw
  have hdiv : Work.FTS.BSSwirl.WeakDivFree ω := by
    have h1 : ω = fun x => -(Work.FTS.BSSwirl.swirlField φ x) := by
      funext x; simp only [ω]; rw [congrFun hsw x]
    rw [h1]
    exact weakDivFree_neg hdiv_sw
  -- the four conclusions for `BS ω`
  have hcd : ContDiff ℝ 1 (Work.LWP.biotSavart ω) :=
    Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one hR0 hM0 h.hα hbdd hsupp hmeas hhold
  have hcurl : ∀ x, FiniteTimeSingularity.vorticity (Work.LWP.biotSavart ω) x = ω x :=
    Work.FTS.BSSwirl.vorticity_biotSavart_of_weakDivFree hR0 hM0 h.hα hCd0 hbdd hsupp hmeas hhold
      hdiv
  have hdivBS : ∀ x, FiniteTimeSingularity.div (Work.LWP.biotSavart ω) x = 0 :=
    Work.FTS.BSSwirl.div_biotSavart_eq_zero hR0 hM0 h.hα hCd0 hbdd hsupp hmeas hhold
  obtain ⟨Cd2, _hCd20, hdec⟩ := Work.FTS.PressureOn.biotSavart_decay hM0 hbdd hsupp
  have htend : Filter.Tendsto (Work.LWP.biotSavart ω)
      (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (Eventually.of_forall fun x => by simpa using hdec x) ?_
    have h4 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => 1 + ‖x‖ ^ 2)
        (Filter.cocompact Work.FTS.BSIdent.R3) Filter.atTop :=
      Filter.tendsto_atTop_mono (fun x => by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1 / 2)])
        tendsto_norm_cocompact_atTop
    have h5 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => (1 + ‖x‖ ^ 2)⁻¹)
        (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) :=
      h4.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using h5.const_mul Cd2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hslice]; exact hcd
  · intro x
    rw [hslice, hcurl x]
    show -(Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C t))
      = -(Work.FTS.Physical.physOmega α A B g C x t)
    rfl
  · intro x
    rw [hslice]; exact hdivBS x
  · rw [hslice]; exact htend

end

end Work.FTS.BSIdent.Weyl
