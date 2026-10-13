/-
# The `ℋ¹` inner product dominates the `ℋ¹` norm: `|f|²_{ℋ¹} ≤ (f,f)_{ℋ¹}`.

`H1IP α` is the paper's inner product on `ℋ¹` with *positive* coefficients
`10, 10^10, 10^17, 10^21` on the four weighted `L²`-terms

  `|D_z f · w/√sin^η|²`, `|f · w/√sin^η|²`, `|f · w|²`, `|D_θ f · w/√sin^γ|²`,

while `HkSq α 1 f` is the sum of the first three of these (the paper's `E_{z,θ}¹`,
see `Eztheta1_eq_HkSq_one`).  Since every coefficient is at least `1` and the pure
`|f·w|²`-term is nonnegative, the norm is dominated by the diagonal inner product.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.EfEta_eq_wip
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one

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

theorem H1IP_le_self (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 1 f)
    (hsm : Work.Spaces.SmoothNbhd f) : Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α f f := by
  -- `sin(2θ) ≥ 0` on the angular interval, so all the angular powers are nonnegative
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- nonnegativity of the three `wip`-terms that make up `HkSq α 1 f`
  have hA : 0 ≤ wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Spaces.Dz f) (Work.Spaces.Dz f) :=
    wip_self_nonneg (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hB : 0 ≤ wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      f f :=
    wip_self_nonneg (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hC : 0 ≤ wip (fun z _ => Work.Spaces.w z ^ 2) f f :=
    wip_self_nonneg (fun z _ _ => sq_nonneg _)
  have hD : 0 ≤ wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) :=
    wip_self_nonneg (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  -- the `ℋ¹` norm is the sum of three of the four inner-product terms
  have hshape : Work.Spaces.HkSq α 1 f = EDz f + EDth α f + EfEta f := by
    rw [← Eztheta1_eq_HkSq_one α f hmem hsm]
    rfl
  rw [hshape, EDz_eq_wip f, EDth_eq_wip α f, EfEta_eq_wip f]
  unfold H1IP
  linarith [hA, hB, hC, hD]

end Work.Coercivity
