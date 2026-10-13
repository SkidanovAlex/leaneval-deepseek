/-
# The `ℋ¹` inner product is bounded above by the `ℋ¹` norm.

`H1IP α` is the paper's inner product on `ℋ¹` with coefficients
`10, 10^10, 10^17, 10^21` on the four weighted `L²`-terms

  `|D_z f · w/√sin^η|²`, `|f · w/√sin^η|²`, `|f · w|²`, `|D_θ f · w/√sin^γ|²`,

while `HkSq α 1 f` is the sum of the first three of these (the paper's `E_{z,θ}¹`,
see `Eztheta1_eq_HkSq_one`).  Since the extra unweighted term `|f · w|²` is dominated
by the `η`-weighted term `|f · w/√sin^η|²` (`Ef_le_EfEta`), the inner product is
bounded above by a fixed multiple (`10^22`) of the norm.  Nothing here depends on `f`
beyond the hypothesis packages `HkMem`, `SmoothNbhd`, `CoerciveData`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.EfEta_eq_wip
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Coercivity.Ef_le_EfEta

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

theorem H1IP_upper (α : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Spaces.HkMem α 1 f →
    Work.Spaces.SmoothNbhd f → Work.Coercivity.CoerciveData α f →
      Work.Coercivity.H1IP α f f ≤ C * Work.Spaces.HkSq α 1 f := by
  refine ⟨(10 : ℝ) ^ 22, by norm_num, ?_⟩
  intro f hmem hsm hcd
  -- `sin(2θ) ≥ 0` on the angular interval, so the angular weights are nonnegative.
  have hsin : ∀ θ ∈ Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- The `ℋ¹` norm is the sum of three of the four inner-product terms.
  have hshape : Spaces.HkSq α 1 f = EDz f + EDth α f + EfEta f := by
    rw [← Eztheta1_eq_HkSq_one α f hmem hsm]
    rfl
  -- The unweighted term is dominated by the `η`-weighted one.
  have hle3 : wip (fun z _ => Spaces.w z ^ 2) f f
      ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) f f := by
    rw [← Ef_eq_wip f, ← EfEta_eq_wip f]
    exact Ef_le_EfEta α f hcd
  -- Nonnegativity of the three `wip`-terms that make up `HkSq α 1 f`.
  have hA : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz f) (Spaces.Dz f) :=
    wip_self_nonneg (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hB : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      f f :=
    wip_self_nonneg (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hD : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth f) (Spaces.Dth f) :=
    wip_self_nonneg (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  rw [hshape, EDz_eq_wip f, EDth_eq_wip α f, EfEta_eq_wip f]
  unfold H1IP
  linarith [hle3, hA, hB, hD]

end Work.Coercivity
