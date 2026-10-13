import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set

/-- On the open angular interval `0 < θ < π/2` one has `sin(2θ) ∈ (0,1]`, hence
`thEta θ = sin(2θ)^{-η} ≥ 1` (for `η ≥ 0`).  At the two endpoints `sin(2θ) = 0` and the
totalised `rpow` returns `0`, which is why the comparison with the unweighted integral is
formulated only on the open interval. -/
theorem one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_pos.le
  have hspow : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := Real.rpow_le_one hs.le hs1 hη0
  have hpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs _
  rw [Real.rpow_neg hs.le, inv_eq_one_div]
  rw [le_div_iff₀ hpos, one_mul]
  exact hspow

theorem interval_sq_le_Itheta {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ x in a..b, h x ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  -- `[a,b] ⊆ (0,π/2) ⊆ Iθ`, since `0 < a` and `b < π/2`.
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt (ha.trans hx.1), le_of_lt (hx.2.trans_lt hb)⟩
  -- Rewrite the interval integral as a set integral over `(a,b]`.
  rw [intervalIntegral.integral_of_le hab]
  -- On `(a,b]` the weight satisfies `thEta ≥ 1`, so `h² ≤ h²·thEta` there.
  have hstep2 : ∫ x in Set.Ioc a b, h x ^ 2
      ≤ ∫ x in Set.Ioc a b, h x ^ 2 * Work.FTS.EllipticEst.thEta x := by
    refine setIntegral_mono_of_nonneg (fun x _ => sq_nonneg (h x)) (fun x hx => ?_)
      (hint.mono_set hsub)
    exact le_mul_of_one_le_right (sq_nonneg (h x))
      (one_le_thEta_of_mem_Ioo ⟨ha.trans hx.1, hx.2.trans_lt hb⟩)
  -- Enlarge the set of integration from `(a,b]` to `Iθ`, using that the integrand is
  -- nonnegative on `Iθ`.
  have hstep3 : ∫ x in Set.Ioc a b, h x ^ 2 * Work.FTS.EllipticEst.thEta x
      ≤ ∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · exact Filter.Eventually.of_forall fun x hx => hsub hx
  exact hstep2.trans hstep3

end Work.FTS.EllSol.EllPkgAux.MollDom
