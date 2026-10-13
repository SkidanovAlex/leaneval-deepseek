/-
# The `ℋ¹` inner product is bounded above by the `ℋ¹` norm, in the open class

`H1IP α` is the paper's inner product on `ℋ¹` with coefficients `10, 10^10, 10^17, 10^21`
on the four weighted `L²`-terms

  `|D_z f · w/√sin^η|²`,  `|f · w/√sin^η|²`,  `|f · w|²`,  `|D_θ f · w/√sin^γ|²`,

while `HkSq α 1 f` is the sum of the first three of these (the paper's `E_{z,θ}¹`).  The
extra unweighted term `|f · w|²` is dominated by the `η`-weighted term `|f · w/√sin^η|²`
(that is the hypothesis `hef`), so the inner product is bounded above by the fixed
multiple `10^22` of the norm.

This is the open-quadrant version of `Work.Coercivity.H1IP_upper`: the only hypothesis
that changes is the regularity of `f` (`SmoothOpen` instead of `SmoothNbhd`), so the
`ℋ¹`-identity `HkSq α 1 f = EfEta f + EDz f + EDth α f` is taken from the open-class
version `Work.FTS.StrongPersist.HkSq_one_eq_SO` instead of
`Work.Coercivity.Eztheta1_eq_HkSq_one`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.EfEta_eq_wip
import Submission.Work.Coercivity.H1IP_nonneg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

theorem H1IP_upper_open {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    (hef : Work.Coercivity.Ef f ≤ Work.Coercivity.EfEta f) :
    Work.Coercivity.H1IP α f f ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 1 f := by
  -- `sin(2θ) ≥ 0` on the angular interval, so the angular weights are nonnegative.
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- The `ℋ¹` norm is the sum of three of the four inner-product terms (open class).
  have hshape : Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EfEta f + Work.Coercivity.EDz f + Work.Coercivity.EDth α f :=
    Work.FTS.StrongPersist.HkSq_one_eq_SO α hs hm
  -- The unweighted term is dominated by the `η`-weighted one.
  have hle3 : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) f f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f := by
    rw [← Work.Coercivity.Ef_eq_wip f, ← Work.Coercivity.EfEta_eq_wip f]
    exact hef
  -- Nonnegativity of the three `wip`-terms that make up `HkSq α 1 f`.
  have hA : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Spaces.Dz f) (Work.Spaces.Dz f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hB : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hD : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  rw [hshape, Work.Coercivity.EDz_eq_wip f, Work.Coercivity.EDth_eq_wip α f,
    Work.Coercivity.EfEta_eq_wip f]
  unfold Work.Coercivity.H1IP
  linarith [hle3, hA, hB, hD]

end Work.FTS.StrongEps.EpsE4Thr
