import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall

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


