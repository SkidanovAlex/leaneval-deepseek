import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.sliceBarSq2
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.FTS.EllipticEst.Honest.Yc.HonSliceRightTendstoYc
import Submission.Work.FTS.EllipticEst.H2W.AeProof.BarAux.hkMemBar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof.BarAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-- **The reduction of the target `aeBarHkMem` to the two `HkSq`-bounds**: for an `AeData`
datum with `HkMem α 0 u`,

`HkSq α 0 (u / cos θ) ≤ 1010000 * (HkSq α 0 u + HkSq α 0 (pthIter 2 u))`.

Route (all inputs proved): the slicewise chain `sliceBarLe` in
`Submission/Work/FTS/EllipticEst/H2W/AeProof/aeBarHkMem.lean`
(`∫(u/cos)²σ ≤ 1010000(∫u²σ + ∫(∂_θθu)²σ)` for `z > 0`, built from `Honest.sliceBarSq2` +
`Honest.sliceInterp` + the endpoint limit `sliceDivCosTendstoPiHalf`) multiplied by `w z ^ 2`,
together with the pointwise identity
`HkIntegrand α 0 g z θ = w z ^ 2 * (g z θ ^ 2 * sEta θ)` on `Iθ` (`barHkInt`/`innerEq` in the
same module), then `MeasureTheory.integral_mono_ae` against the integrable dominating function
`1010000 * (∫_θ HkIntegrand α 0 u z θ + ∫_θ HkIntegrand α 0 (pthIter 2 u) z θ)`
(integrable by `HkMem α 0 u` and `AeData.memAng2` respectively; the LHS is integrable by
`BarAux.hkMemBar`), plus `MeasureTheory.integral_const_mul` and
`MeasureTheory.integral_add`.  At `z = 0` both sides vanish because `w 0 = 0`. -/
theorem hkSqBar_le : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.Spaces.HkMem α 0 u →
      Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
        ≤ 1010000 * (Work.Spaces.HkSq α 0 u
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
  intro α u G h hmu
  -- the `ℋ⁰`-membership of the quotient, giving the integrability of the left-hand side
  have hmemv : Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) :=
    Work.FTS.EllipticEst.H2W.AeProof.BarAux.hkMemBar α u G h hmu
  -- `Iz` and `(0,∞)` differ by the null set `{0}`
  have hIzIoi : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  -- ## the slicewise bound, for `z > 0`
  have hbound : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => u z θ / Real.cos θ) z θ)
        ≤ 1010000 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)) := by
    intro z hz
    rw [Work.FTS.EllipticEst.H2W.AeProof.innerEq α (fun z θ => u z θ / Real.cos θ) z,
        Work.FTS.EllipticEst.H2W.AeProof.innerEq α u z,
        Work.FTS.EllipticEst.H2W.AeProof.innerEq α (Work.Spaces.pthIter 2 u) z]
    have hsb := Work.FTS.EllipticEst.H2W.AeProof.sliceBarLe α u G h hmu hz
    -- `∂_θθu` is definitionally the `pthIter 2` of `u`
    have heqB : (∫ θ in Work.Spaces.Iθ, deriv (fun t => deriv (fun θ' => u z θ') t) θ ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
            * Work.FTS.EllipticEst.sEta θ) := rfl
    rw [heqB] at hsb
    have hW : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    refine (mul_le_mul_of_nonneg_left hsb hW).trans (le_of_eq ?_)
    ring
  -- ## the same bound almost everywhere on `Iz`
  have haeb : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => u z θ / Real.cos θ) z θ)
      ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => 1010000 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ))) := by
    rw [hIzIoi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hbound
  -- ## integrate the pointwise bound
  have hmain := MeasureTheory.integral_mono_ae hmemv.2
    ((hmu.2.add h.memAng2.2).const_mul 1010000) haeb
  -- ## the right-hand side in integrated form
  have hrhs : (∫ z in Work.Spaces.Iz, 1010000 *
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)))
      = 1010000 * (Work.Spaces.HkSq α 0 u
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmu.2 h.memAng2.2]
    congr 1
  exact hmain.trans (le_of_eq hrhs)

end Work.FTS.EllipticEst.H2W.AeProof.BarAux
