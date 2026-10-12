import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dictBricks
import Submission.Work.BoseFixB1S.fibreVoidB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PCFU

open MeasureTheory
open scoped ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The slot peel of the centred box, `ℝ≥0∞` form.**

For `0 < ℓ`, `j : Fin n` and any `F : X n → ℝ≥0∞` which is a.e. measurable for the restricted box
measure,

  `∫⁻ x ∈ abox n ℓ, ∫⁻ u ∈ acube ℓ, F (x[j ↦ u])  =  ℓ³ · ∫⁻ x ∈ abox n ℓ, F x`.

The point is that averaging a function over the `j`-th slot is *exactly* the identity on
cube-supported data: the collapsing map `(x,u) ↦ x[j↦u]` pushes `μ ⊗ ν` forward to
`ν(univ) • μ = ℓ³ • μ` (`Work.BoseFixB1S.pushforward_update_abox`), and Tonelli converts the
iterated integral into the integral against that product measure.

(Note that the collapsing map is *not* injective and is *not* measure preserving on the box — its
fibres over the forgotten coordinate have measure `ℓ³`; the identity above is the correct
statement.) -/
theorem abox_cube_peel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    (F : Submission.BoseGases.X n → ENNReal)
    (hF : AEMeasurable F (MeasureTheory.Measure.restrict
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ))) :
    (∫⁻ x in Submission.BoseGases.abox n ℓ,
        ∫⁻ u in Submission.BoseGases.acube ℓ, F (Function.update x j u))
      = ENNReal.ofReal (ℓ ^ 3) * ∫⁻ x in Submission.BoseGases.abox n ℓ, F x := by
  classical
  -- the collapsing map and its pushforward identity
  have hΦm : Measurable
      (fun p : Submission.BoseGases.X n × E3 => Function.update p.1 j p.2) :=
    measurable_update'
  have hpush : Measure.map
        (fun p : Submission.BoseGases.X n × E3 => Function.update p.1 j p.2)
        (((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)).prod
          ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
      = ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ •
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    Work.BoseFixB1S.pushforward_update_abox (n := n) (ℓ := ℓ) hℓ j
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : Submission.BoseGases.X n × E3 => Function.update p.1 j p.2)
      (((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    ⟨hΦm, by rw [hpush]; exact Measure.smul_absolutelyContinuous⟩
  -- a.e. measurability of the joint integrand (the pushforward is absolutely continuous in `μ`)
  have hae : AEMeasurable (fun p : Submission.BoseGases.X n × E3 =>
        F (Function.update p.1 j p.2))
      (((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    AEMeasurable.comp_quasiMeasurePreserving hF hqmp
  -- the a.e. equality of the joint integrand with the joint integrand of a measurable
  -- representative of `F`
  have haeeq : (fun p : Submission.BoseGases.X n × E3 => F (Function.update p.1 j p.2))
      =ᵐ[(((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)).prod
            ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))]
      (fun p => AEMeasurable.mk F hF (Function.update p.1 j p.2)) :=
    hqmp.ae hF.ae_eq_mk
  -- Tonelli: the iterated integral is the integral against the product measure
  have hstep1 : (∫⁻ x in Submission.BoseGases.abox n ℓ,
        ∫⁻ u in Submission.BoseGases.acube ℓ, F (Function.update x j u))
      = ∫⁻ p : Submission.BoseGases.X n × E3, F (Function.update p.1 j p.2)
          ∂(((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)).prod
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    (MeasureTheory.lintegral_prod _ hae).symm
  -- the volume of the peeled cube
  have hνuniv : ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ
      = ENNReal.ofReal (ℓ ^ 3) := by
    rw [Measure.restrict_apply_univ]
    exact Submission.BoseGases.acube_volume ℓ hℓ.le
  calc (∫⁻ x in Submission.BoseGases.abox n ℓ,
        ∫⁻ u in Submission.BoseGases.acube ℓ, F (Function.update x j u))
      = ∫⁻ p : Submission.BoseGases.X n × E3, F (Function.update p.1 j p.2)
          ∂(((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)).prod
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := hstep1
    _ = ∫⁻ p : Submission.BoseGases.X n × E3,
          AEMeasurable.mk F hF (Function.update p.1 j p.2)
          ∂(((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)).prod
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
        lintegral_congr_ae haeeq
    _ = ∫⁻ y : Submission.BoseGases.X n, AEMeasurable.mk F hF y
          ∂(Measure.map (fun p : Submission.BoseGases.X n × E3 =>
              Function.update p.1 j p.2)
            (((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)).prod
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))) :=
        (lintegral_map hF.measurable_mk hΦm).symm
    _ = ∫⁻ y : Submission.BoseGases.X n, AEMeasurable.mk F hF y
          ∂(((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ •
            ((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) := by
        rw [hpush]
    _ = ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ *
          ∫⁻ y : Submission.BoseGases.X n, AEMeasurable.mk F hF y
            ∂((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)) := by
        rw [lintegral_smul_measure]; simp [smul_eq_mul]
    _ = ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ *
          ∫⁻ y : Submission.BoseGases.X n, F y
            ∂((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)) := by
        rw [← lintegral_congr_ae hF.ae_eq_mk]
    _ = ENNReal.ofReal (ℓ ^ 3) * ∫⁻ x in Submission.BoseGases.abox n ℓ, F x := by
        rw [hνuniv]

end Work.PCFU
