import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.NonlinRows.HkMem_mul_pth_flat
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.thD_reindex
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_notGood =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 15: the "first bad angular jet" of `𝒰(Φ̃_*)`

Row 15 of the nonlinear estimates (`N₂^{ss}`) is an `ℋ⁴`-estimate which, at those `z > 0` where
the angular derivatives of `𝒰(Φ̃_*)` vanish at `θ → 0⁺`, is supplied by the pointwise bound of
`Uop_PhiTs_bounds`; at the remaining `z` one instead needs the *lower* bound of `row15_bad`.  The
present lemma is the logical bookkeeping that separates the two cases:

> if all the iterated `z`-derivatives `∂_z^k 𝒰(Φ̃_*)` (`k ≤ 5`) have a limit at `θ → 0⁺`, and
> not all of `D_z^b 𝒰(Φ̃_*)` (`b ≤ 4`) tend to `0`, then there is a **first** index `k ≤ 4` at
> which `∂_z^k 𝒰(Φ̃_*)` fails to tend to `0`, and there it is *bounded away from zero*.

The mathematics is a triangular change of coordinates.  Since `𝒰(Φ̃_*)` is `C^∞` on the open
quadrant (`StarPkg.smooth`), its `z`-slices at interior angles are `C^∞`, and the Stirling
expansion of the operator `D_z = z∂_z` (`Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth`) reads

  `D_z^b 𝒰 = ∑_{k ≤ b} S(b,k)·z^k·∂_z^k 𝒰`     (`S = scoef`, Stirling numbers of the second kind)

in a neighbourhood of `θ = 0` inside `θ > 0` — a *triangular* linear combination of the jets
`∂_z^k 𝒰`, whose diagonal coefficient is `S(b,b) = 1`.  Hence passing to the limit `θ → 0⁺`
(which exists for `∂_z^k 𝒰`, `k ≤ 5`, by hypothesis, and is preserved by finite sums),

  `lim D_z^b 𝒰 = ∑_{k ≤ b} S(b,k) z^k · lim ∂_z^k 𝒰`,

so if every limit `L_k` (`k ≤ 4`) vanished then every `D_z^b 𝒰` (`b ≤ 4`) would tend to `0`,
against `hnotgood`.  Taking `k` minimal with `L_k ≠ 0`, every `L_j` (`j < k`) vanishes by
triangularity, and `L_k ≠ 0` makes `∂_z^k 𝒰` eventually bounded away from `0`.
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

open scoped Real Topology
open Filter Set MeasureTheory

set_option autoImplicit false



end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.IP4T1Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `SmoothOpen` is closed under products. -/
theorem SmoothOpen_mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hF.forall n
  have h2 : ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.Q0 := hG.forall n
  have hfun : (Function.uncurry fun z θ => F z θ * G z θ)
      = Function.uncurry F * Function.uncurry G := rfl
  rw [hfun]
  exact h1.mul h2



end Work.FTS.StrongPersist.N6Trans
end
