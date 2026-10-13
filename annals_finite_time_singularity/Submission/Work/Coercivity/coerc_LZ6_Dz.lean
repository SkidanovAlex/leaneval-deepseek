import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.coerc_LZ6_Dz_aux
import Submission.Work.Coercivity.Dz_near_zero_bound
import Submission.Work.Coercivity.box_deriv_ftc
import Submission.Work.Coercivity.slice_Z16

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem coerc_LZ6_Dz (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z16 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Spaces.Dz f z θ * Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (47 / 100) * EDz f ≤ wip Weta (Z16 f) (Spaces.Dz f) := by
  have hlimA : Tendsto (fun n : ℕ => (47 / 100 : ℝ) *
      (∫ z in Set.Ioo 0 (n : ℝ), ∫ θ in Spaces.Iθ,
        (Spaces.Dz f z θ) ^ 2 * Weta z θ)) atTop (𝓝 ((47 / 100 : ℝ) * EDz f)) :=
    ((continuous_const.mul continuous_id : Continuous fun x : ℝ => (47 / 100 : ℝ) * x).tendsto
      (EDz f)).comp (tendsto_EDz_trunc f hint2)
  refine le_of_tendsto_of_tendsto' hlimA (tendsto_wip_Z16_trunc f hint) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · exact box_bound f hsm hbd hint hint2 (by exact_mod_cast h)

end Work.Coercivity
