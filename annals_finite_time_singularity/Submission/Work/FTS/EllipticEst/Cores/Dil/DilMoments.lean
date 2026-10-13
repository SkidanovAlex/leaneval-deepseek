/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular moments of the second difference-quotient datum

The class `EllWeakPos` is defined by *linear* conditions besides the equation: the two angular
moments `F_* F' ≡ 0`, `F_* Ψ' ≡ 0`.  For the second difference-quotient datum

  `(dq c (dq c F), dq c (dq c Ψ))`,   `dq c h = (h (c·) - h)/(c-1)`,

those moments are the *second difference quotients* of the moment functions `F_* F`, `F_* Ψ`,
which vanish identically — and, crucially, the linearity of the Bochner integral needed here only
requires the integrability of the *slices of `F` and `Ψ` themselves* (not of any derivative),
which is available in the weak class.

Indeed `dq c (dq c h) z θ = (h (c²z) θ - 2 h (c z) θ + h z θ)/(c-1)²`, so the moment is the
same combination of `F_* h (c²z)`, `F_* h (c z)`, `F_* h z`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.Tools
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The moment of a second difference quotient -/

theorem Fstar_dqq_eq {c : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => f (c * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (dq c (dq c f)) z
      = (Work.Elliptic.Fstar f (c ^ 2 * z) - 2 * Work.Elliptic.Fstar f (c * z)
          + Work.Elliptic.Fstar f z) / (c - 1) ^ 2 := by
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ => 2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ := h2.const_mul 2
  have hsplit : (fun θ => dq c (dq c f) z θ * Work.Elliptic.sinCos2 θ)
      = fun θ => (f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2
          - (2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) / (c - 1) ^ 2
          + (f z θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2 := by
    funext θ
    by_cases hc1 : c - 1 = 0
    · have hc : c = 1 := sub_eq_zero.mp hc1
      subst hc
      simp [dq_apply]
    · simp only [dq_apply]
      field_simp
      ring
  have hA : MeasureTheory.IntegrableOn
      (fun θ => (f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2)
      Work.Spaces.Iθ := h1.div_const _
  have hB : MeasureTheory.IntegrableOn
      (fun θ => (2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) / (c - 1) ^ 2)
      Work.Spaces.Iθ := hI2.div_const _
  have hC : MeasureTheory.IntegrableOn
      (fun θ => (f z θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2) Work.Spaces.Iθ :=
    h3.div_const _
  have hAB : MeasureTheory.IntegrableOn
      (fun θ => (f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) / (c - 1) ^ 2
        - (2 * (f (c * z) θ * Work.Elliptic.sinCos2 θ)) / (c - 1) ^ 2) Work.Spaces.Iθ :=
    hA.sub hB
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar, hsplit,
    MeasureTheory.integral_add hAB hC, MeasureTheory.integral_sub hA hB]
  simp only [MeasureTheory.integral_div, MeasureTheory.integral_const_mul]
  ring

/-- If moreover the three moments vanish, so does the moment of the second difference quotient. -/
theorem Fstar_dqq_eq_zero {c : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => f (c ^ 2 * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => f (c * z) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h4 : Work.Elliptic.Fstar f (c ^ 2 * z) = 0) (h5 : Work.Elliptic.Fstar f (c * z) = 0)
    (h6 : Work.Elliptic.Fstar f z = 0) :
    Work.Elliptic.Fstar (dq c (dq c f)) z = 0 := by
  rw [Fstar_dqq_eq h1 h2 h3, h4, h5, h6]
  simp

/-! ## The two instantiations -/

theorem Fstar_dqq_F_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {c : ℝ} (hc : 1 < c) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (dq c (dq c F)) z = 0 := by
  intro z hz
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    smoothOpen_of_bslOp_eq (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  have hmF : Work.Spaces.HkMem α 0 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 2) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hSF) h.memF
  have hint : ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => F y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun y hy => integrableOn_sinCos2_of_HkMem hSF hmF hy
  refine Fstar_dqq_eq_zero (hint (c ^ 2 * z) ?_) (hint (c * z) ?_) (hint z hz) ?_ ?_ ?_
  · positivity
  · positivity
  · exact h.orthF (c ^ 2 * z) (by positivity)
  · exact h.orthF (c * z) (by positivity)
  · exact h.orthF z hz

theorem Fstar_dqq_Ψ_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {c : ℝ} (hc : 1 < c) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (dq c (dq c Ψ)) z = 0 := by
  intro z hz
  have hint : ∀ y : ℝ, 0 < y →
      MeasureTheory.IntegrableOn (fun θ => Ψ y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun y hy => integrableOn_sinCos2_of_weak (k := 2) (by norm_num) h hy
  refine Fstar_dqq_eq_zero (hint (c ^ 2 * z) ?_) (hint (c * z) ?_) (hint z hz) ?_ ?_ ?_
  · positivity
  · positivity
  · exact h.orthPsi (c ^ 2 * z) (by positivity)
  · exact h.orthPsi (c * z) (by positivity)
  · exact h.orthPsi z hz

end Work.FTS.EllipticEst.Cores.Dil
