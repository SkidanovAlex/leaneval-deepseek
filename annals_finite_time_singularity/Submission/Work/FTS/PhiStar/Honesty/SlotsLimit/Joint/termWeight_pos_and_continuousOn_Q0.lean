import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slot weight `termWeight α i` is positive on the open quadrant and continuous there

The weight of the `(j,i)`-term of `HkIntegrand` is

* `w(z)/sin(2θ)^{η/2}` for the pure `D_z`-slots (`i = 0`), and
* `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` for the mixed slots (`i ≥ 1`),

where `w(z) = (1+z)²/z²` is strictly positive for `z > 0` and `sin(2θ) > 0` for
`0 < θ < π/2`.  Hence `termWeight α i` is strictly positive on the open quadrant `Q0`, and it
is continuous there: the two building blocks
`Work.FTS.EllipticEst.continuousOn_wdivsin_Q0` (`i = 0`) and `continuousOn_Wt_Q0` (`i ≥ 1`)
are already the `ContinuousOn` statements of exactly these functions, and `Function.uncurry`
of the (constant) `if`-clause defining `termWeight` reduces to each of them.
-/

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.Joint

open scoped Real Topology
open MeasureTheory Set Filter

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-- **The mixed weight `Wt α = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant.** -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hth : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hth

/-- **`termWeight α i` is strictly positive on the open quadrant.** -/
theorem termWeight_pos (α : ℝ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 < termWeight α i z θ := by
  intro z θ hz hθ0 hθ1
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  rcases eq_or_ne i 0 with rfl | hne
  · have h0 : termWeight α 0
        = fun z θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := rfl
    rw [h0]
    exact div_pos hw (Real.rpow_pos_of_pos hs _)
  · simp only [termWeight]
    rw [ite_eq_right hne, Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_pos hw (Real.rpow_pos_of_pos hs _)

/-- **`termWeight α i` is continuous on the open quadrant.** -/
theorem termWeight_continuousOn_Q0 (α : ℝ) (i : ℕ) :
    ContinuousOn (Function.uncurry (termWeight α i)) Q0 := by
  rcases eq_or_ne i 0 with rfl | hne
  · have h : Function.uncurry (termWeight α 0)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
      funext p; simp [Function.uncurry, termWeight]
    rw [h]
    exact Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
  · have h : Function.uncurry (termWeight α i)
        = fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2 := by
      funext p
      simp only [Function.uncurry, termWeight]
      rw [ite_eq_right hne]
    rw [h]
    exact continuousOn_Wt_Q0 α

theorem termWeight_pos_and_continuousOn_Q0 (α : ℝ) (i : ℕ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        0 < Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i z θ) ∧
      ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Honesty.SlotsLimit.termWeight α i))
        Work.FTS.EllipticEst.Q0 :=
  ⟨termWeight_pos α i, termWeight_continuousOn_Q0 α i⟩

end Work.FTS.PhiStar.Honesty.SlotsLimit.Joint
