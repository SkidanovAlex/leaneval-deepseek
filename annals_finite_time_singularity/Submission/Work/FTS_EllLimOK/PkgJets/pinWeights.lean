/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets.pinWeights` — the angular weights of the pinning estimate

The pinning estimate `PkgJets.pinningBound` bounds the `ℋ⁰`-norm of the slot
`Φ̃/cos θ = PhiTil α g (E g)/cos θ` by the `ℋ⁶`-norm of the source.  Via the reconstruction
`∂_θ(cos θ·Ψ) = cos θ·Vop Ψ` (`Work.FTS_EllLimOK.Vop_reconstruct`) the pointwise-in-`z`
angular estimate is the weighted Hardy inequality

`∫_θ (Ψ/cos θ)²·ν ≤ K·∫_θ (Vop Ψ)²·ν`   with   `ν θ = sin(2θ)^{-η}`,

i.e. with `A := cos θ·Ψ` and `A' = cos θ·Vop Ψ`,

`∫_θ A²·W₁ ≤ K·∫_θ (A')²·W₂`,   `W₁ = ν/cos⁴θ`,  `W₂ = ν/cos²θ`.

This file collects the three weights (`wNu`, `wOne`, `wTwo`) and the primitive `wLam` of `W₁` from
the *regular* end `θ = 0`, together with the elementary facts about them (nonnegativity,
positivity on the open interval, the value at `0` and the derivative).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The weights -/

/-- `ν θ = sin(2θ)^{-η}` with `η = Work.Spaces.eta = 99/100`. -/
def wNu (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `W₁ θ = sin(2θ)^{-η}/cos⁴θ`: the weight of the slot `Ψ/cos θ` (i.e. of `A = cos θ·Ψ`). -/
def wOne (θ : ℝ) : ℝ := wNu θ / (Real.cos θ) ^ 4

/-- `W₂ θ = sin(2θ)^{-η}/cos²θ`: the weight of the slot `Vop Ψ` (i.e. of `A' = cos θ·Vop Ψ`). -/
def wTwo (θ : ℝ) : ℝ := wNu θ / (Real.cos θ) ^ 2

/-- The primitive `Λ θ = ∫_0^θ W₁` of `W₁` from the regular end `θ = 0`. -/
def wLam (θ : ℝ) : ℝ := ∫ s in (0 : ℝ)..θ, wOne s

/-! ## Elementary facts -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

theorem wNu_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wNu θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem wNu_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < wNu θ :=
  Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _

theorem cos_four_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ (Real.cos θ) ^ 4 :=
  pow_nonneg (Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩) 4

theorem wOne_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wOne θ :=
  div_nonneg (wNu_nonneg hθ) (cos_four_nonneg_of_mem_Iθ hθ)

theorem cos_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ (Real.cos θ) ^ 2 :=
  pow_nonneg (Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩) 2

theorem wTwo_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ wTwo θ :=
  div_nonneg (wNu_nonneg hθ) (cos_two_nonneg_of_mem_Iθ hθ)

theorem wOne_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < wOne θ :=
  div_pos (wNu_pos hθ) (pow_pos (cos_pos_of_mem_Ioo hθ) 4)

theorem wTwo_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < wTwo θ :=
  div_pos (wNu_pos hθ) (pow_pos (cos_pos_of_mem_Ioo hθ) 2)

@[simp] theorem wOne_zero : wOne 0 = 0 := by
  have h : (-(Work.Spaces.eta)) ≠ 0 := by norm_num [Work.Spaces.eta]
  simp [wOne, wNu, Real.zero_rpow, h]

@[simp] theorem wLam_zero : wLam 0 = 0 := by simp [wLam]

theorem measurable_wNu : Measurable (fun θ : ℝ => wNu θ) :=
  (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

theorem measurable_wOne : Measurable (fun θ : ℝ => wOne θ) := by
  have h : Measurable (fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / (Real.cos θ) ^ ((4 : ℕ) : ℝ)) :=
    ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _).div
      ((Real.measurable_cos.comp measurable_id).pow_const _)
  simpa only [wOne, wNu, Real.rpow_natCast] using h

/-! ## Integrability of `W₁` near `0`, and the primitive -/

/-- On `[0,y]` the weight `W₁` is dominated by a multiple of `sin(2·)^{-η}`. -/
theorem wOne_le_of_mem_Icc {y : ℝ} (hy : y ∈ Set.Ioo 0 (π / 2)) {s : ℝ}
    (hs : s ∈ Set.Icc 0 y) : wOne s ≤ wNu s / (Real.cos y) ^ 4 := by
  have hcosy : 0 < Real.cos y := cos_pos_of_mem_Ioo hy
  have hpi : y ≤ Real.pi := by linarith [Real.pi_pos, hy.2]
  have hcos : Real.cos y ≤ Real.cos s := Real.cos_le_cos_of_nonneg_of_le_pi hs.1 hpi hs.2
  have h4 : (Real.cos y) ^ 4 ≤ (Real.cos s) ^ 4 := pow_le_pow_left₀ (le_of_lt hcosy) hcos 4
  have hwNu_nn : 0 ≤ wNu s := wNu_nonneg ⟨hs.1, le_trans hs.2 (le_of_lt hy.2)⟩
  have hcos4 : 0 < (Real.cos s) ^ 4 := by
    have hspos : 0 < Real.cos s := lt_of_lt_of_le hcosy hcos
    positivity
  rw [wOne, div_le_div_iff₀ hcos4 (by positivity)]
  calc wNu s * (Real.cos y) ^ 4 ≤ wNu s * (Real.cos s) ^ 4 :=
        mul_le_mul_of_nonneg_left h4 hwNu_nn
    _ = wNu s * (Real.cos s) ^ 4 := rfl

/-- `W₁` is integrable on `[0,y]` for `y ∈ (0,π/2)`. -/
theorem integrableOn_wOne_Icc {y : ℝ} (hy : y ∈ Set.Ioo 0 (π / 2)) :
    IntegrableOn wOne (Set.Icc 0 y) := by
  have hcosy : 0 < Real.cos y := cos_pos_of_mem_Ioo hy
  have hsub : Set.Icc 0 y ⊆ Work.Spaces.Iθ := fun s hs =>
    ⟨hs.1, le_trans hs.2 (le_of_lt hy.2)⟩
  have h1 : IntegrableOn wNu (Set.Icc 0 y) :=
    ((Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
      (by norm_num [Work.Spaces.eta])).1).mono_set hsub
  have hInt : IntegrableOn (fun s => wNu s / (Real.cos y) ^ 4) (Set.Icc 0 y) := by
    rw [MeasureTheory.IntegrableOn]
    simpa only [inv_mul_eq_div] using h1.const_mul (((Real.cos y) ^ 4)⁻¹)
  rw [MeasureTheory.IntegrableOn] at hInt ⊢
  refine hInt.mono' measurable_wOne.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (wOne_nonneg (hsub hs))]
  exact wOne_le_of_mem_Icc hy hs

theorem wLam_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) : 0 ≤ wLam θ := by
  rw [wLam]
  exact intervalIntegral.integral_nonneg h0 fun u hu => wOne_nonneg ⟨hu.1, le_trans hu.2 h1⟩

/-- The primitive of `W₁` has derivative `W₁` on the open quadrant. -/
theorem hasDerivAt_wLam {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt wLam (wOne θ) θ := by
  have hint : IntervalIntegrable wOne volume (0 : ℝ) θ := by
    refine ⟨(integrableOn_wOne_Icc hθ).mono_set ?_, (integrableOn_wOne_Icc hθ).mono_set ?_⟩
    · rintro s ⟨h1, h2⟩
      exact ⟨le_of_lt h1, h2⟩
    · rintro s ⟨h1, h2⟩
      exact absurd h1 (not_lt.mpr (le_trans h2 (le_of_lt hθ.1)))
  have hcont : ContinuousAt wOne θ := by
    unfold wOne wNu
    refine ContinuousAt.div ?_ ?_ ?_
    ·
      exact (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.mul continuousAt_id)).rpow_const
          (Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
    · exact (Real.continuous_cos.continuousAt).pow 4
    · exact pow_ne_zero 4 (ne_of_gt (cos_pos_of_mem_Ioo hθ))
  have h := intervalIntegral.integral_hasDerivAt_right hint
    measurable_wOne.aestronglyMeasurable.stronglyMeasurableAtFilter hcont
  exact h

end Work.FTS_EllLimOK.PkgJets
