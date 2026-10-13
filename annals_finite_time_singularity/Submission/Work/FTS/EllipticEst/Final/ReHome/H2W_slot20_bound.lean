/-
Copied from `Submission.Work.FTS.EllipticEst.H2W.slot20_bound` for `Final/slot20_bound_fts`.
Only the `import` lines are redirected (see `Final/slot20_bound_fts.lean` for why):
the copy of `Mine/TopSlotTwo` (`Final/ReHome/TkKit.lean`) drops the `Mine/ShiftLevelOne`
import and the two declarations at the end of that file that use it, which cuts the
`RPFresh/excess_finite` dependency out of the closure.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Final.ReHome.TkKit
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.remov.slice_step4
import Submission.Work.FTS.EllipticEst.remov.slice5_reduce
import Submission.Work.FTS.EllipticEst.remov.coerc.weak_poincare_second

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The reduction of `slot20_bound` to the slice estimates

Write `f = ∂_θθΨ`.  The top angular slot of `f` at level `2` is `(D_θ²f·Wt α)²`, and

`D_θ² f = sin²(2θ)·∂_θ²f + 2sin(2θ)cos(2θ)·∂_θf`,

so `(D_θ²f·Wt α)² ≤ 2w²(∂_θ²f)²σ₄ + 8w²(∂_θf)²σ₂` with `σ₄ = sig4 (gam α)`, `σ₂ = sig2 (gam α)`.
Both terms are *slices* of the paper's Steps 5 and 4: with `f = ∂_θθΨ`,
`∂_θ²f = ∂_θ⁴Ψ` and `∂_θf = ∂_θ³Ψ = D_θ(∂_θθΨ)/sin(2θ)`.

The second term is exactly (8 times) the left-hand side of the sibling `slot01_bound`
(`s20M3_eq`), and the first is the quantity controlled by the slice Step-5 estimate for the
equation `Lzero1 (Ψ z ·) = Gsrc α F Ψ z ·`.  The rest of this file records the reduction and the
source domination; the two analytic inputs are the slice estimates themselves. -/

/-- The first sum of the target's right-hand side: the pure (`D_z`-only) slots of `∂_θθΨ` at
level `2`. -/
def pPure (Ψ : ℝ → ℝ → ℝ) : ℝ := ∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
  Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## The pointwise reduction -/

/-- **The pointwise reduction.**  With `f = ∂_θθΨ` the level-`2` top angular slot of `f` is the
square of `D_θ²f = sin²(2θ)·∂_θ²f + 2sin(2θ)cos(2θ)·∂_θf`, so

`(D_θ²f·Wt α)² ≤ 2 w² (∂_θ²f)² σ₄ + 8 w² (∂_θf)² σ₂`

on `Iθ`, where `σ₄ = sig4 (gam α)`, `σ₂ = sig2 (gam α)`. -/
theorem pt_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (h2 : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun t => deriv (fun s => Work.Spaces.pthIter 2 Ψ z s) t) θ') :
    (Work.Spaces.mixed 0 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 2 * (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
              Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
        + 8 * (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
              Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ) := by
  have hbase := Work.FTS.EllipticEst.Mine.Tk_pointwise_le_closed α hα hα4
    (Work.Spaces.pthIter 2 Ψ) z θ hθ h2
  have e1 : deriv (fun θ' => deriv (fun t => Work.Spaces.pthIter 2 Ψ z t) θ') θ
      = Work.Spaces.pthIter 4 Ψ z θ := rfl
  have e2 : deriv (fun t => Work.Spaces.pthIter 2 Ψ z t) θ
      = Work.Spaces.pthIter 3 Ψ z θ := rfl
  rw [e1, e2] at hbase
  exact hbase

/-- The slice of `Ψ` at `z > 0` is `C⁴` on the open angular interval (the smoothness hypothesis
of the weak class is on the open quadrant). -/
theorem slice_contDiff {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 4 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hp : ContDiffOn ℝ 4 (fun θ' : ℝ => (z, θ')) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have h2 := (hsm 4).comp hp (fun θ' hθ' => ⟨hz, hθ'⟩)
  simpa [Function.comp_def, Function.uncurry] using h2

/-- The second `∂_θ`-derivative of the slice is differentiable (so that the pointwise expansion
of `D_θ²` is available). -/
theorem slice_diff2 {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) :
    ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun t => deriv (fun s => Work.Spaces.pthIter 2 Ψ z s) t) θ' := by
  intro θ' hθ'
  have hG : ContDiffOn ℝ 4 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := slice_contDiff hsm hz
  have h1 : ContDiffOn ℝ 3 (deriv (fun θ => Ψ z θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    hG.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : ContDiffOn ℝ 2 (deriv (deriv (fun θ => Ψ z θ))) (Set.Ioo 0 (Real.pi / 2)) :=
    h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h3 : ContDiffOn ℝ 1 (deriv (deriv (deriv (fun θ => Ψ z θ))))
      (Set.Ioo 0 (Real.pi / 2)) :=
    h2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (h3.contDiffAt (isOpen_Ioo.mem_nhds hθ')).differentiableAt (by norm_num)

/-! ## The two dominating pieces and the reduction of the top slot -/

/-- The `∂_θ⁴Ψ`-piece of the dominating integrand (the slice Step-5 quantity). -/
def s20F4 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  2 * (Work.Spaces.w z) ^ 2 *
    ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
      Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)

/-- The `∂_θ³Ψ`-piece of the dominating integrand (the slice Step-4 quantity). -/
def s20F3 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  8 * (Work.Spaces.w z) ^ 2 *
    ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
      Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ)

/-- `M₄ := ∫_z ∫_θ 2w²(∂_θ⁴Ψ)²σ₄`: the quantity the slice Step-5 estimate controls. -/
def s20M4 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, s20F4 α Ψ z θ

/-- `M₃ := ∫_z ∫_θ 8w²(∂_θ³Ψ)²σ₂`: the quantity the slice Step-4 estimate controls. -/
def s20M3 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, s20F3 α Ψ z θ

/-- `A₂ := ∫_z w² ∫_θ (∂_θ²Ψ)² sEta`: the pure `η`-slot of `∂_θθΨ` at level `0`. -/
def s20A2 (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ)

/-- `A₁ := ∫_z w² ∫_θ (∂_θΨ)²`. -/
def s20A1 (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)

/-- `A₀ := ∫_z w² ∫_θ Ψ²`. -/
def s20A0 (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)

/-- `J₂ := ∫_z w² ∫_θ (∂_θ²G)² σ₄`, the source of the slice Step-5 estimate. -/
def s20J2 (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2
        (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
      Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)

/-- **The pointwise identity turning `M₃` into the sibling `slot01_bound` slot.** -/
theorem s20F3_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (z : ℝ) :
    s20F3 α Ψ z θ
      = 8 * (Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 := by
  have hg : Work.Spaces.gam α ≠ 0 := ne_of_gt (Work.Spaces.gam_pos hα)
  have hgam : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hg1 : -(Work.Spaces.gam α / 2) ≠ 0 := by intro hc; exact hg (by linarith)
  have hg2 : -(Work.Spaces.gam α) ≠ 0 := by intro hc; exact hg (by linarith)
  have h2g : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := by intro hc; linarith
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hsig : Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ
      = (Real.sin (2 * θ)) ^ ((2 : ℝ) - Work.Spaces.gam α) := rfl
  have hDth : Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ := rfl
  have hWt : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  have hq : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rcases eq_or_lt_of_le hs with h0 | hpos
    · rw [← h0, Real.zero_rpow hg1, Real.zero_rpow hg2]
      ring
    · rw [← Real.rpow_add hpos]
      congr 1
      ring
  have hsp : (Real.sin (2 * θ)) ^ ((2 : ℝ) - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ (2 : ℝ)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rcases eq_or_lt_of_le hs with h0 | hpos
    · rw [← h0, Real.zero_rpow h2g, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
        Real.zero_rpow hg2]
      ring
    · rw [← Real.rpow_add hpos (2 : ℝ) (-(Work.Spaces.gam α))]
      simp only [sub_eq_add_neg]
  have hs2 : (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (2 : ℝ) :=
    (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm
  rw [hDth, hWt, s20F3, hsig, hsp, mul_pow, mul_pow, mul_pow, hs2]
  simp only [pow_two]
  rw [hq]
  ring

/-- **`M₃` is `8` times the left-hand side of the sibling `slot01_bound`.** -/
theorem s20M3_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) :
    s20M3 α Ψ = 8 * Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) := by
  have hpt : ∀ z, (∫ θ in Work.Spaces.Iθ, s20F3 α Ψ z θ)
      = 8 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1
          (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => s20F3_eq α hα hα4 Ψ hθ z))
  calc s20M3 α Ψ
      = 8 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1
          (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
        rw [s20M3, ← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = 8 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
          (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) := rfl

/-- The pointwise bound, integrated once in `θ`. -/
theorem tk_le_two_terms (α : ℝ) (hα : 0 < α) (Ψ : ℝ → ℝ → ℝ)
    (hpt : ∀ z θ : ℝ, z ∈ Work.Spaces.Iz → θ ∈ Work.Spaces.Iθ →
      (Work.Spaces.mixed 0 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ s20F4 α Ψ z θ + s20F3 α Ψ z θ)
    (hR : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => s20F4 α Ψ z θ + s20F3 α Ψ z θ) Work.Spaces.Iθ)
    (hRz : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (s20F4 α Ψ z θ + s20F3 α Ψ z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (s20F4 α Ψ z θ + s20F3 α Ψ z θ) := by
  rw [Work.FTS.EllipticEst.remov.Step.Tk]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hRz ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hR z hz) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
  exact hpt z θ hz hθ

/-- **The reduction of the top slot.**  The pointwise `D_θ²`-expansion dominates the top angular
slot of `∂_θθΨ` by `F₄ + F₃`, and both pieces are honest (hypotheses); integrating gives
`Tk α 2 (∂_θθΨ) ≤ M₄ + M₃`. -/
theorem tk_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (h4θ : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => s20F4 α Ψ z θ) Work.Spaces.Iθ)
    (h4z : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, s20F4 α Ψ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (h3θ : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => s20F3 α Ψ z θ) Work.Spaces.Iθ)
    (h3z : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, s20F3 α Ψ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ s20M4 α Ψ + s20M3 α Ψ := by
  have hsm := h.smooth
  have hpt : ∀ z θ : ℝ, z ∈ Work.Spaces.Iz → θ ∈ Work.Spaces.Iθ →
      (Work.Spaces.mixed 0 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ s20F4 α Ψ z θ + s20F3 α Ψ z θ := by
    intro z θ hz hθ
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with hz0 | hzpos
    · subst hz0
      have hw0 : Work.Spaces.Wt α 0 θ = 0 := by
        simp only [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
        norm_num
      rw [hw0, mul_zero, pow_two, mul_zero]
      have hs' : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
      have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) :=
        Real.rpow_nonneg hs' _
      have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
        Real.rpow_nonneg hs' _
      refine add_nonneg ?_ ?_
      · rw [s20F4]
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) h4)
      · rw [s20F3]
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) h3)
    · have h2 := slice_diff2 hsm hzpos
      have hp := pt_le α hα hα4 Ψ z θ hθ h2
      simpa only [s20F4, s20F3] using hp
  have hRz : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (s20F4 α Ψ z θ + s20F3 α Ψ z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (h4z.add h3z).congr (by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      exact (MeasureTheory.integral_add (h4θ z hz) (h3θ z hz)).symm)
  have hmain := tk_le_two_terms α hα Ψ hpt
    (fun z hz => (h4θ z hz).add (h3θ z hz))
    hRz
  have hsplit : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (s20F4 α Ψ z θ + s20F3 α Ψ z θ)) = s20M4 α Ψ + s20M3 α Ψ := by
    have hcongr : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, (s20F4 α Ψ z θ + s20F3 α Ψ z θ))
          = (∫ θ in Work.Spaces.Iθ, s20F4 α Ψ z θ)
            + (∫ θ in Work.Spaces.Iθ, s20F3 α Ψ z θ) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      exact MeasureTheory.integral_add (h4θ z hz) (h3θ z hz)
    rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_add h4z h3z]
    simp only [s20M4, s20M3]
  rw [hsplit] at hmain
  exact hmain

/-! ## Nonnegativity of the intermediate quantities -/

theorem L2Sq_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.L2Sq g :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

theorem pPure_nonneg (Ψ : ℝ → ℝ → ℝ) : 0 ≤ pPure Ψ :=
  Finset.sum_nonneg fun _ _ => L2Sq_nonneg _

theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

theorem s20A2_nonneg (Ψ : ℝ → ℝ → ℝ) : 0 ≤ s20A2 Ψ := by
  rw [s20A2]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine mul_nonneg (sq_nonneg _) ?_
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  exact mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)

theorem s20A1_nonneg (Ψ : ℝ → ℝ → ℝ) : 0 ≤ s20A1 Ψ := by
  rw [s20A1]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine mul_nonneg (sq_nonneg _) ?_
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _

theorem s20A0_nonneg (Ψ : ℝ → ℝ → ℝ) : 0 ≤ s20A0 Ψ := by
  rw [s20A0]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine mul_nonneg (sq_nonneg _) ?_
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _

theorem s20M3_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : 0 ≤ s20M3 α Ψ := by
  rw [s20M3]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  refine mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

theorem s20J2_nonneg (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : 0 ≤ s20J2 α F Ψ := by
  rw [s20J2]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine mul_nonneg (sq_nonneg _) ?_
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

/-! ## The assembly -/

/-- **Assembly.**  The four analytic inputs (the honesty of the two dominating pieces, the
two-dimensional Step-5 and Step-4 estimates for the slices, and the domination of the source
and of the lower-order terms by `purePart + HkSq`) give the target. -/
theorem slot20_of_pieces
    (hHon : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => s20F4 α Ψ z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, s20F4 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => s20F3 α Ψ z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, s20F3 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hStep5 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      s20M4 α Ψ ≤ C * (s20J2 α F Ψ + s20M3 α Ψ + s20A2 Ψ + s20A1 Ψ + s20A0 Ψ))
    (hStep4 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      s20M3 α Ψ ≤ C * (pPure Ψ + Work.Spaces.HkSq α 2 F))
    (hSource : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      s20J2 α F Ψ + (s20A2 Ψ + s20A1 Ψ + s20A0 Ψ)
        ≤ C * (pPure Ψ + Work.Spaces.HkSq α 2 F)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
        ≤ K * (pPure Ψ + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨C5, hC5, h5⟩ := hStep5
  obtain ⟨C3, hC3, h3⟩ := hStep4
  obtain ⟨Cs, hCs, hs⟩ := hSource
  refine ⟨C5 * (Cs + C3 + Cs) + C3, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  obtain ⟨h4θ, h4z, h3θ, h3z⟩ := hHon α F Ψ hα hα4 h
  have htk := tk_le α hα hα4 F Ψ h h4θ h4z h3θ h3z
  have hsp := h5 α F Ψ hα hα4 h
  have hs4 := h3 α F Ψ hα hα4 h
  have hsrc := hs α F Ψ hα hα4 h
  set R : ℝ := pPure Ψ + Work.Spaces.HkSq α 2 F with hR
  have hR0 : 0 ≤ R := by
    rw [hR]; exact add_nonneg (pPure_nonneg Ψ) (Work.Spaces.HkSq_nonneg α 2 F)
  have hL0 : 0 ≤ s20A2 Ψ + s20A1 Ψ + s20A0 Ψ := by
    linarith [s20A2_nonneg Ψ, s20A1_nonneg Ψ, s20A0_nonneg Ψ]
  have hJ0 : 0 ≤ s20J2 α F Ψ := s20J2_nonneg α F Ψ
  have hJle : s20J2 α F Ψ ≤ Cs * R := by
    rw [hR] at hsrc ⊢
    linarith [hsrc, hL0]
  have hLle : s20A2 Ψ + s20A1 Ψ + s20A0 Ψ ≤ Cs * R := by
    rw [hR] at hsrc ⊢
    linarith [hsrc, hJ0]
  have hM3le : s20M3 α Ψ ≤ C3 * R := by
    rw [hR]; exact hs4
  have hS : s20J2 α F Ψ + s20M3 α Ψ + (s20A2 Ψ + s20A1 Ψ + s20A0 Ψ)
      ≤ (Cs + C3 + Cs) * R := by
    have h1 : s20J2 α F Ψ + s20M3 α Ψ ≤ Cs * R + C3 * R := add_le_add hJle hM3le
    have h2 : s20J2 α F Ψ + s20M3 α Ψ + (s20A2 Ψ + s20A1 Ψ + s20A0 Ψ)
        ≤ Cs * R + C3 * R + Cs * R := add_le_add h1 hLle
    nlinarith [h2, hR0]
  have hM4le : s20M4 α Ψ ≤ C5 * ((Cs + C3 + Cs) * R) := by
    have hnn : 0 ≤ s20J2 α F Ψ + s20M3 α Ψ + (s20A2 Ψ + s20A1 Ψ + s20A0 Ψ) := by
      linarith [hJ0, s20M3_nonneg α Ψ, hL0]
    have hstep5' : s20M4 α Ψ
        ≤ C5 * (s20J2 α F Ψ + s20M3 α Ψ + (s20A2 Ψ + s20A1 Ψ + s20A0 Ψ)) := by
      linarith [hsp]
    exact hstep5'.trans (mul_le_mul_of_nonneg_left hS hC5.le)
  have hfin : Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ (C5 * ((Cs + C3 + Cs) * R) + C3 * R) := htk.trans (add_le_add hM4le hM3le)
  have harith : C5 * ((Cs + C3 + Cs) * R) + C3 * R
      = (C5 * (Cs + C3 + Cs) + C3) * R := by ring
  linarith [hfin, harith.symm.le, harith.le]

