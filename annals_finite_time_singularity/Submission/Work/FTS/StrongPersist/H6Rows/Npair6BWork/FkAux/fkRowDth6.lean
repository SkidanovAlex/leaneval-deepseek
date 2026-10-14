import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingCore
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthShiftLow
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.one_le_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000

/-- **Fubini for a radial coefficient.**  For a product-integrable `p ↦ r p.1 · G p.1 p.2` with
`r` depending on `z` alone, the product integral is the iterated integral with `r z` pulled out of
the angular integral.  (`integral_const_mul` is unconditional, so no integrability of the slices
is needed.) -/
private lemma integral_prod_radial {r : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => r p.1 * G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ p, r p.1 * G p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z in Work.Spaces.Iz, r z * (∫ θ in Work.Spaces.Iθ, G z θ) := by
  rw [MeasureTheory.integral_prod _ hInt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact MeasureTheory.integral_const_mul (r z) (fun θ => G z θ)

/-- Elementary arithmetic: `(7)·(64·(A·X)) ≤ (448(A+1)+1)·a·X` for `A, X ≥ 0` and `a ≥ 1`
(the factor `64 = 2^6` bounds the binomial coefficients of the Leibniz expansion, and
`a = α^{-3} ≥ 1` is the `α`-power price). -/
private lemma final_arith {A X a : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) (ha : 1 ≤ a) :
    (7 : ℝ) * (64 * (A * X)) ≤ (448 * (A + 1) + 1) * a * X := by
  nlinarith [mul_nonneg hA hX, mul_nonneg (mul_nonneg hA hX) (sub_nonneg.mpr ha),
    sq_nonneg X]



end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
