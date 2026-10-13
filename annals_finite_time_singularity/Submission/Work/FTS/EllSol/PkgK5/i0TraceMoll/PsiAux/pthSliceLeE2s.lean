/-
# `Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux.pthSliceLeE2s`

For a trace-class datum `G` (`Work.FTS.EllSol.EllPkgAux.TraceClass G`) and a radius `w > 0`,
the angular slice `θ ↦ ∂_θG(w,θ)` is controlled on the whole open interval `(0, π/2)` by its
value at the midpoint `π/4` and by the `L²`-energy of the second angular derivative:

  `|∂_θG(w,θ)| ≤ |∂_θG(w,π/4)| + √(π/2)·√(E2s G w)`,

where `E2s G w = ∫_{Iθ} (∂_θ²G(w,·))² σ_η` and `σ_η = sin(2θ)^{-η}`, `η = 99/100`.

The proof is the fundamental theorem of calculus for the `C²` slice `t ↦ G w t`
(`Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral`: the increment of `deriv` is the integral of
`deriv (deriv ·)`) together with the weighted Cauchy–Schwarz estimate
`Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted`
(`∫|h| ≤ √(π/2)·√(∫h²σ)`, whose constant `√(π/2)` is the worst-case size of `∫σ^{-1}` on
`[0,π/2]`, since `σ^{-1} = sin(2θ)^η ≤ 1` there).  No endpoint vanishing of `∂_θG` is used.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux

open MeasureTheory Set Filter

theorem pthSliceLeE2s (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    ∀ w : ℝ, 0 < w → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth G w θ| ≤ |Work.Spaces.pth G w (Real.pi / 4)|
        + Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := by
  intro w hw θ hθ0 hθ1
  obtain ⟨hsm, -, -, -, -, -, -, hhon⟩ := hT
  have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- The `θ`-slice `t ↦ G w t` is `C²` on the open interval `(0, π/2)`.
  have hC2 : ContDiffOn ℝ 2 (fun t : ℝ => G w t) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hw).of_le (by simp [Work.Stability.smoothOrder])
  -- Integrability of the weighted square of the second angular derivative.
  have hE2 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w t) ^ 2
        * Work.FTS.EllipticEst.thEta t) Work.Spaces.Iθ :=
    Work.FTS.EllSol.EllPkgAux.integrableOn_second_deriv hhon hw
  have hE2' : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w t) ^ 2
        * (Real.sin (2 * t)) ^ (-(99 / 100 : ℝ))) (Set.Icc 0 (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta] using hE2
  have hE2s_eq : Work.FTS.EllSol.EllPkgAux.E2s G w
      = ∫ t in Set.Icc (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.pth (Work.Spaces.pth G) w t) ^ 2 * (Real.sin (2 * t)) ^ (-(99 / 100 : ℝ)) := by
    simp only [Work.FTS.EllSol.EllPkgAux.E2s, Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
  -- Weighted Cauchy–Schwarz for the slice of `∂_θ²G`.
  have hCS : (∫ t in Work.Spaces.Iθ, |Work.Spaces.pth (Work.Spaces.pth G) w t|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := by
    have h := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
      (h := fun t : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w t) hE2'
    rw [← hE2s_eq] at h
    simpa only [Work.Spaces.Iθ] using h
  -- Integrability of `|∂_θ²G|` on the full interval.
  have habs : MeasureTheory.IntegrableOn
      (fun t : ℝ => |Work.Spaces.pth (Work.Spaces.pth G) w t|) Work.Spaces.Iθ :=
    Work.FTS.EllSol.EllPkgAux.integrableOn_abs_second_deriv hsm hhon hw
  -- Monotonicity of the integral over a subinterval of `[0, π/2]`.
  have hsubI : ∀ {c d : ℝ}, c ≤ d → 0 < c → d < Real.pi / 2 →
      (∫ t in c..d, |Work.Spaces.pth (Work.Spaces.pth G) w t|)
        ≤ ∫ t in Work.Spaces.Iθ, |Work.Spaces.pth (Work.Spaces.pth G) w t| := by
    intro c d hcd hc hd
    rw [intervalIntegral.integral_of_le hcd]
    refine MeasureTheory.setIntegral_mono_set habs
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) ?_
    filter_upwards with t ht using
      ⟨le_of_lt (lt_trans hc ht.1), le_of_lt (lt_of_le_of_lt ht.2 hd)⟩
  rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
  · -- ## Case `θ < π/4`
    have hftc : Work.Spaces.pth G w (Real.pi / 4) - Work.Spaces.pth G w θ
        = ∫ x in θ..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) w x :=
      Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral (h := fun t : ℝ => G w t)
        (ε := Real.pi / 2) hC2 hθ0 hlt.le hπ4lt
    have hdiff : Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)
        = -(∫ x in θ..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) w x) := by
      rw [← hftc]; ring
    have h1 : |Work.Spaces.pth G w θ|
        ≤ |Work.Spaces.pth G w (Real.pi / 4)|
          + |Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)| := by
      have h := abs_add_le (Work.Spaces.pth G w (Real.pi / 4))
        (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
      rwa [show Work.Spaces.pth G w (Real.pi / 4)
            + (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
          = Work.Spaces.pth G w θ from by ring] at h
    refine h1.trans ?_
    rw [hdiff, abs_neg]
    exact add_le_add_right ((intervalIntegral.abs_integral_le_integral_abs hlt.le).trans
      ((hsubI hlt.le hθ0 hπ4lt).trans hCS)) _
  · -- ## Case `θ = π/4`
    subst heq
    refine le_add_of_nonneg_right ?_
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · -- ## Case `π/4 < θ`
    have hftc : Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)
        = ∫ x in (Real.pi / 4)..θ, Work.Spaces.pth (Work.Spaces.pth G) w x :=
      Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral (h := fun t : ℝ => G w t)
        (ε := Real.pi / 2) hC2 hπ4pos hgt.le hθ1
    have h1 : |Work.Spaces.pth G w θ|
        ≤ |Work.Spaces.pth G w (Real.pi / 4)|
          + |Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)| := by
      have h := abs_add_le (Work.Spaces.pth G w (Real.pi / 4))
        (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
      rwa [show Work.Spaces.pth G w (Real.pi / 4)
            + (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
          = Work.Spaces.pth G w θ from by ring] at h
    refine h1.trans ?_
    rw [hftc]
    exact add_le_add_right ((intervalIntegral.abs_integral_le_integral_abs hgt.le).trans
      ((hsubI hgt.le hπ4pos hθ1).trans hCS)) _

end Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux
