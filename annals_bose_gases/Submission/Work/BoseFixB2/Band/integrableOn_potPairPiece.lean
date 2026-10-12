import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Band.PotSplit
import Submission.Work.BoseFixB2.Pot.potWordU_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Band.integrableOn_potPairPiece`

Integrability on the centred box `abox N ℓ` of a single two-body summand of the
localised potential word (`Work.BoseFixB2.Band.potPairPiece`), for an *arbitrary*
integrable numerator `v` — in particular with **no diluteness/support hypothesis**
relating the support radius of `v` to the box side `ℓ`.

The point (as in `Work.BoseFixB2.Pot.potWordU_integrable`) is that the two cutoff
factors `χ_ℓ` cancel the denominator `(χ⋆χ)_ℓ` in the *joint* integral, so no
pointwise bound is available or needed.  This file isolates the pair part of that
argument: rewrite `potPairPiece` as the two-slot function of `wPairC`, peel the two
slots with `lintegral_pair_abox`, and bound the resulting double cube integral by
the full double integral, which is finite by `lintegral_wPairC_le`.

The measurability half is `Work.BoseFixB2.Pot.aesm_wLoc_pair_X`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB2.Band

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem integrableOn_potPairPiece {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : MeasureTheory.Integrable v)
    (p : {p : Fin N × Fin N // p.1 < p.2}) :
    MeasureTheory.IntegrableOn (Work.BoseFixB2.Band.potPairPiece N v ℓ p)
      (Submission.BoseGases.abox N ℓ) := by
  have hij : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hℓnn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
  -- the uncurried kernel on `ℝ³ × ℝ³`
  have hvmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wPairC ℓ v q.1 q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    Work.BoseFixB2.Pot.aemeasurable_wPairC_prod hv.aestronglyMeasurable
  -- `potPairPiece` is the two-slot function of `wPairC`
  have hfun : Work.BoseFixB2.Band.potPairPiece N v ℓ p
      = fun x : Submission.BoseGases.X N =>
          Submission.BoseGases.wPairC ℓ v (x p.1.1) (x p.1.2) := by
    funext x
    exact Work.BoseFixB2.Pot.wLoc_zero_eq_wPairC ℓ v (x p.1.1) (x p.1.2)
  rw [hfun]
  have hbase : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.wPairC ℓ v (x p.1.1) (x p.1.2))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)) :=
    (Work.BoseFixB2.Pot.aesm_wLoc_pair_X (ℓ := ℓ) (u := 0)
      hv.aestronglyMeasurable p.1.1 p.1.2 hij).congr
      (Filter.Eventually.of_forall (fun x =>
        Work.BoseFixB2.Pot.wLoc_zero_eq_wPairC ℓ v (x p.1.1) (x p.1.2)))
  refine ⟨hbase.restrict, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_norm]
  -- cube-restricted integrals are bounded by the full integrals
  have hcube_le : ∀ f : EuclideanSpace ℝ (Fin 3) → ENNReal,
      (∫⁻ a : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ, f a)
        ≤ (∫⁻ a : EuclideanSpace ℝ (Fin 3), f a) := by
    intro f
    refine (lintegral_mono_set (Set.subset_univ (Submission.BoseGases.acube ℓ))).trans ?_
    exact le_of_eq (by simp [Measure.restrict_univ])
  -- finiteness of the double cube integral
  have hdouble : (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) < ⊤ := by
    have hstep : (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
          ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ))
          ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)))
        ≤ (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
            ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
            ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
      calc (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
            ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
            ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ))
            ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ)))
          ≤ (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
              ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
              ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))
              ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
            hcube_le (fun a : EuclideanSpace ℝ (Fin 3) =>
              ∫⁻ b : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
                ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ)
        _ ≤ (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
              ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
              ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
              ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
            lintegral_mono (fun a =>
              hcube_le (fun b : EuclideanSpace ℝ (Fin 3) =>
                ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ))
    have hfull : (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
          ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
        = (∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
            ‖Submission.BoseGases.wPairC ℓ v q.1 q.2‖ₑ
            ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
              (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) :=
      (MeasureTheory.lintegral_prod
        (f := fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          ‖Submission.BoseGases.wPairC ℓ v q.1 q.2‖ₑ) hvmeas.enorm).symm
    exact lt_of_le_of_lt (hstep.trans (le_of_eq hfull))
      (lt_of_le_of_lt (Work.BoseFixB2.Pot.lintegral_wPairC_le hℓ hv)
        ENNReal.ofReal_lt_top)
  calc (∫⁻ x : Submission.BoseGases.X N,
        ENNReal.ofReal ‖Submission.BoseGases.wPairC ℓ v (x p.1.1) (x p.1.2)‖
        ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)))
      = (∫⁻ x : Submission.BoseGases.X N,
          ‖Submission.BoseGases.wPairC ℓ v (x p.1.1) (x p.1.2)‖ₑ
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N ℓ))) :=
        lintegral_congr (fun x => by rw [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs])
    _ = ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.acube ℓ)) ^ (N - 2)
          * (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
              ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
              ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))
              ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))) :=
        Work.BoseFixB2.Pot.lintegral_pair_abox
          (φ := fun a b : EuclideanSpace ℝ (Fin 3) =>
            ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ) hℓ hij
          (show MeasureTheory.AEStronglyMeasurable
              (Function.uncurry (fun a b : EuclideanSpace ℝ (Fin 3) =>
                ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ))
              ((MeasureTheory.volume : MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin 3))).prod
                (MeasureTheory.volume : MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin 3)))) from hvmeas.enorm.aestronglyMeasurable)
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn))
        hdouble

end Work.BoseFixB2.Band
