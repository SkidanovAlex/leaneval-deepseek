import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.potIntegrable.integrable_qLHSBIntegrand_spec
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_eq_of_mem_farSet
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_farSet_le_tBwordB
import Submission.Work.UBBInputs8.A.exists_hlow_localised_of_bounded
import Submission.Work.UBBInputs8.A.qLHSwordB_integral_u_box
import Submission.Work.UBBInputs8.A.tBLocalisationInd_const
import Submission.Work.UBBInputs8.A.tBwordBInd_const_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1Aux

-- Adaptation of `Work.UBBInputs2.integrable_qLHSBIntegrand` (full measure `volume` on
-- `ℝ³ × X N`) to: real scale `d` (instead of `{d : ℕ}` with `(d : ℝ)`), free chemical
-- potential `μ` (instead of `Work.UBB.dens N L`), and a single scale `L : ℝ` with `0 < L`
-- (instead of `hL : 1 ≤ L` plus regime hypotheses `∀ L ≥ 1`).  All of its helper lemmas
-- already take `{ℓ d : ℝ}`, and `μ` occurs in `qLHSBIntegrand` only as a scalar factor of the
-- first summand (`Φ x ^ 2 * (- μ * Σ_i ∫_y wSmall1Pair … + (1/2) * Σ_q wSmallPair …)`), so its
-- proof carries over verbatim with `hR' := hR`, `hRχ := hRχ`, `(d : ℝ) ↦ d`,
-- `Work.UBB.dens N L ↦ μ` and `|Work.UBB.dens N L| ↦ |μ|` in the dominating function `K`.
theorem integrable_qLHSBIntegrand_real {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R0 μ d : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv1 : MeasureTheory.MemLp v 1) (M : ℕ) (hM : 1 ≤ M) (hd : 0 < d)
    {L : ℝ} (hL : 0 < L) (hR : R0 ≤ L * d / 16) (hRχ : R0 ≤ L * Submission.BoseGases.chiR0)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Φ p.1 p.2)
      (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N)) := by
  -- The statement is *identical* to `Work.BoseFixB1.potIntegrable.integrable_qLHSBIntegrand_spec`
  -- (full product measure, real `d`, free `μ`, single scale `L`), which the corpus already proves
  -- as the full-measure core of the box-restricted Urysohn transplant.
  exact Work.BoseFixB1.potIntegrable.integrable_qLHSBIntegrand_spec (h := h)
    hv_supp hR0 hv1 hM hL hd hR hRχ hΦc hΦs

end Work.BoseFixB1Aux
