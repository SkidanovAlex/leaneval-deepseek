import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.basis_apply_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Splitting the integral of a sum of four functions over a set of `ℝ × ℝ`. -/
lemma integral_rect_add4 {s : Set (ℝ × ℝ)} {f₁ f₂ f₃ f₄ : ℝ × ℝ → ℝ}
    (h₁ : IntegrableOn f₁ s) (h₂ : IntegrableOn f₂ s) (h₃ : IntegrableOn f₃ s)
    (h₄ : IntegrableOn f₄ s) :
    (∫ x in s, (f₁ x + f₂ x + f₃ x + f₄ x))
      = (∫ x in s, f₁ x) + (∫ x in s, f₂ x) + (∫ x in s, f₃ x) + (∫ x in s, f₄ x) := by
  rw [show (∫ x in s, (f₁ x + f₂ x + f₃ x + f₄ x))
      = ∫ x in s, ((f₁ + f₂ + f₃) x + f₄ x) from rfl]
  rw [integral_add ((h₁.add h₂).add h₃) h₄]
  rw [show (∫ x in s, (f₁ + f₂ + f₃) x) = ∫ x in s, ((f₁ + f₂) x + f₃ x) from rfl]
  rw [integral_add (h₁.add h₂) h₃]
  rw [show (∫ x in s, (f₁ + f₂) x) = ∫ x in s, (f₁ x + f₂ x) from rfl]
  rw [integral_add h₁ h₂]

/-- **The derivative bounds of `rect_deriv_bounds`, for an arbitrary datum.**

If `G` is `C^∞` on the open quadrant and its six second-order quantities
`∂_zG, ∂_θG, ∂_z²G, ∂_z∂_θG, ∂_θ∂_zG, ∂_θ²G` have `L²`-norms bounded by `C * M` on a
rectangle `[a',b'] × [c',d'] ⊆ Q0`, then the `L²`-norms on that rectangle of the first and
second Fréchet derivatives of `uncurry G` are bounded by `4 * C * M` and `16 * C * M`.

This is purely a `2 × 2` operator-norm computation (`eqc_opNorm_le_basis_sum₂` and
Cauchy–Schwarz `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`) followed by Fubini
(`eqc_setIntegral_rect_eq`): on `ℝ × ℝ` the operator norm of a linear functional is dominated
by the sum of its two basis values, and that of a bilinear form by the sum of the absolute
values of its four matrix entries (`norm_fderiv_fderiv_le_basis`), which are
`∂_z²G, ∂_z∂_θG, ∂_θ∂_zG, ∂_θ²G`. -/
theorem rect_deriv_bounds_aux {G : ℝ → ℝ → ℝ} {C M a' b' c' d' : ℝ}
    (hsub : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0)
    (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (h1 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz G z θ) ^ 2 ≤ C * M)
    (h2 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth G z θ) ^ 2 ≤ C * M)
    (h3 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pz G) z θ) ^ 2 ≤ C * M)
    (h4 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2 ≤ C * M)
    (h5 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2 ≤ C * M)
    (h6 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 ≤ C * M) :
    (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (Function.uncurry G) x‖ ^ 2 ≤ 4 * C * M)
      ∧ (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) x‖ ^ 2 ≤ 16 * C * M) := by
  classical
  have hR2m : MeasurableSet (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
    measurableSet_Icc.prod measurableSet_Icc
  have hR2k : IsCompact (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
    isCompact_Icc.prod isCompact_Icc
  have hG2 : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0 :=
    hG.of_le two_le_smoothOrder
  constructor
  · -- ## first derivative
    have hpt1 : ∀ x ∈ Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (Function.uncurry G) x‖ ^ 2
          ≤ 2 * (Work.Spaces.pz G x.1 x.2) ^ 2
            + 2 * (Work.Spaces.pth G x.1 x.2) ^ 2 := by
      rintro ⟨z, θ⟩ hx
      have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
        (hG2.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hsub hx))).differentiableAt
          (by norm_num)
      have hb := Work.FTS.StrongLWP.Sobolev.eqc_opNorm_le_basis_sum
        (fderiv ℝ (Function.uncurry G) (z, θ))
      calc ‖fderiv ℝ (Function.uncurry G) (z, θ)‖ ^ 2
          ≤ (‖(fderiv ℝ (Function.uncurry G) (z, θ)) (1, 0)‖
              + ‖(fderiv ℝ (Function.uncurry G) (z, θ)) (0, 1)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ ≤ 2 * (((fderiv ℝ (Function.uncurry G) (z, θ)) (1, 0)) ^ 2
              + ((fderiv ℝ (Function.uncurry G) (z, θ)) (0, 1)) ^ 2) := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
            simpa only [sq_abs] using Work.FTS.StrongLWP.Sobolev.eqc_sq_add2_le
              |(fderiv ℝ (Function.uncurry G) (z, θ)) (1, 0)|
              |(fderiv ℝ (Function.uncurry G) (z, θ)) (0, 1)|
        _ = 2 * (Work.Spaces.pz G z θ) ^ 2 + 2 * (Work.Spaces.pth G z θ) ^ 2 := by
            rw [← Work.Spaces.pz_eq_fderiv hd, ← Work.Spaces.pth_eq_fderiv hd]
            ring
    have hpzint : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz G x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k (((hG.pz).continuousOn.mono hsub).pow 2)
    have hpthint : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth G x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k (((hG.pth).continuousOn.mono hsub).pow 2)
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        2 * (Work.Spaces.pz G x.1 x.2) ^ 2 + 2 * (Work.Spaces.pth G x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      (hpzint.const_mul 2).add (hpthint.const_mul 2)
    have hI1 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pz G x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hpzint]
      exact h1
    have hI2 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pth G x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hpthint]
      exact h2
    calc ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d', ‖fderiv ℝ (Function.uncurry G) x‖ ^ 2
        ≤ ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
            (2 * (Work.Spaces.pz G x.1 x.2) ^ 2 + 2 * (Work.Spaces.pth G x.1 x.2) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hInt
            (ae_restrict_of_forall_mem hR2m hpt1)
      _ = 2 * (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d', (Work.Spaces.pz G x.1 x.2) ^ 2)
            + 2 * (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d', (Work.Spaces.pth G x.1 x.2) ^ 2) := by
          rw [integral_add (hpzint.const_mul 2) (hpthint.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 4 * C * M := by nlinarith [hI1, hI2]
  · -- ## second derivative
    have hpt2 : ∀ x ∈ Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) x‖ ^ 2
          ≤ 4 * ((Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2) := by
      rintro ⟨z, θ⟩ hx
      have hb : ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)‖ ≤
          |Work.Spaces.pz (Work.Spaces.pz G) z θ| + |Work.Spaces.pz (Work.Spaces.pth G) z θ|
            + |Work.Spaces.pth (Work.Spaces.pz G) z θ|
            + |Work.Spaces.pth (Work.Spaces.pth G) z θ| := by
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pthIter_succ,
          Work.Spaces.pthIter_zero] using
          norm_fderiv_fderiv_le_basis (G := G) Work.FTS.EllipticEst.isOpen_Q0 hG2 (hsub hx)
      calc ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)‖ ^ 2
          ≤ (|Work.Spaces.pz (Work.Spaces.pz G) z θ|
              + |Work.Spaces.pz (Work.Spaces.pth G) z θ|
              + |Work.Spaces.pth (Work.Spaces.pz G) z θ|
              + |Work.Spaces.pth (Work.Spaces.pth G) z θ|) ^ 2 :=
            pow_le_pow_left₀
              (norm_nonneg (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ))) hb 2
        _ ≤ 4 * ((Work.Spaces.pz (Work.Spaces.pz G) z θ) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) := by
            simpa only [sq_abs] using Work.FTS.StrongLWP.Sobolev.eqc_sq_add4_le
              |Work.Spaces.pz (Work.Spaces.pz G) z θ| |Work.Spaces.pz (Work.Spaces.pth G) z θ|
              |Work.Spaces.pth (Work.Spaces.pz G) z θ| |Work.Spaces.pth (Work.Spaces.pth G) z θ|
    have he1 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pz).pz).continuousOn.mono hsub).pow 2)
    have he2 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pth).pz).continuousOn.mono hsub).pow 2)
    have he3 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pz).pth).continuousOn.mono hsub).pow 2)
    have he4 : IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ContinuousOn.integrableOn_compact hR2k ((((hG.pth).pth).continuousOn.mono hsub).pow 2)
    have hInt2 : IntegrableOn (fun x : ℝ × ℝ =>
        4 * ((Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2))
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      (((he1.add he2).add he3).add he4).const_mul 4
    have hg1 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he1]
      exact h3
    have hg2 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he2]
      exact h4
    have hg3 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he3]
      exact h5
    have hg4 : ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2 ≤ C * M := by
      rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq he4]
      exact h6
    calc ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
            ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) x‖ ^ 2
        ≤ ∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
            4 * ((Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
              + (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hInt2
            (ae_restrict_of_forall_mem hR2m hpt2)
      _ = 4 * ((∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pz (Work.Spaces.pz G) x.1 x.2) ^ 2)
            + (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
            + (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
            + (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
              (Work.Spaces.pth (Work.Spaces.pth G) x.1 x.2) ^ 2)) := by
          rw [integral_const_mul, integral_rect_add4 he1 he2 he3 he4]
      _ ≤ 16 * C * M := by nlinarith [hg1, hg2, hg3, hg4]

theorem rect_deriv_bounds {F : ℝ → ℝ → ℝ} {α C : ℝ} {a' b' c' d' : ℝ} (j i : ℕ)
    (hsub : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (h1 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h2 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h3 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h4 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h5 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)
    (h6 : ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
        (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) :
    (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed j i F)) x‖ ^ 2
          ≤ 4 * C * Work.Spaces.HkSq α 6 F)
      ∧ (∫ x in Set.Icc a' b' ×ˢ Set.Icc c' d',
        ‖fderiv ℝ (fderiv ℝ (Function.uncurry (Work.Spaces.mixed j i F))) x‖ ^ 2
          ≤ 16 * C * Work.Spaces.HkSq α 6 F) :=
  rect_deriv_bounds_aux (G := Work.Spaces.mixed j i F) (M := Work.Spaces.HkSq α 6 F)
    hsub (hFsm.mixed j i) h1 h2 h3 h4 h5 h6

end Work.FTS.StrongEps.LocUnif
