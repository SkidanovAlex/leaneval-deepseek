import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# One-coordinate peeling of the centred box `abox n ℓ`

`∫⁻_{abox n ℓ} G (x i) = (vol (acube ℓ))^{n-1} · ∫⁻_{acube ℓ} G` for a.e.-strongly-measurable
`G : ℝ³ → ℝ≥0∞`.

Proof: rewrite `volume.restrict (abox N ℓ)` as the product `Measure.pi (fun _ => volume↾acube ℓ)`
(`restrict_abox_eq_pi`), transport along the measure-preserving split
`MeasurableEquiv.piFinSuccAbove` isolating slot `i`
(`measurePreserving_coordSplitFinAcube` + `MeasurePreserving.lintegral_comp_emb`), apply
Tonelli (`lintegral_prod`), and evaluate the inner integral over the coordinate that the
integrand does not depend on (`lintegral_const`, `lintegral_mul_const'`).  The remaining
factor is `(volume.restrict (abox m ℓ)) Set.univ = vol (abox m ℓ) = ofReal ((ℓ³)^m) =
(vol (acube ℓ))^m` (`abox_volume`, `acube_volume`, `ENNReal.ofReal_pow`).
-/

open MeasureTheory

namespace Work.BoseFixB2.Pot

theorem lintegral_coord_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {G : EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∫⁻ x : Submission.BoseGases.X n, G (x i)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
      = ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.acube ℓ)) ^ (n - 1)
        * (∫⁻ a : EuclideanSpace ℝ (Fin 3), G a
            ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ))) := by
  cases n with
  | zero => exact (i.elim0 : False).elim
  | succ m =>
    have hmp : MeasurePreserving
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => EuclideanSpace ℝ (Fin 3)) i))
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)).prod
          ((volume : Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ))) := by
      have h1 := Submission.BoseGases.measurePreserving_coordSplitFinAcube (n := m) ℓ i
      simpa only [Submission.BoseGases.restrict_abox_eq_pi] using h1
    have hfin : ((volume : Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)) Set.univ ≠ ⊤ := by
      rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume m ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top
    have hνuniv : ((volume : Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)) Set.univ
        = ((volume : Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.acube ℓ)) ^ m := by
      rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume m ℓ hℓ.le,
        Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_pow (p := ℓ ^ 3) (by positivity) m
    have hA : (∫⁻ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m, G p.1
        ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)).prod
          ((volume : Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ))))
        = ((volume : Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) Set.univ
          * (∫⁻ a : EuclideanSpace ℝ (Fin 3), G a
              ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))) := by
      rw [lintegral_prod _
        ((hG.restrict (s := Submission.BoseGases.acube ℓ)).aemeasurable.comp_fst)]
      simp_rw [lintegral_const]
      rw [lintegral_mul_const' _ _ hfin, mul_comm]
    calc
      (∫⁻ x : Submission.BoseGases.X (m + 1), G (x i)
          ∂((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
            (Submission.BoseGases.abox (m + 1) ℓ)))
          = ∫⁻ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m, G p.1
              ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                  (Submission.BoseGases.acube ℓ)).prod
                ((volume : Measure (Submission.BoseGases.X m)).restrict
                  (Submission.BoseGases.abox m ℓ))) := by
            rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
              (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m => G p.1)]
            exact lintegral_congr fun x => rfl
      _ = ((volume : Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) Set.univ
          * (∫⁻ a : EuclideanSpace ℝ (Fin 3), G a
              ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))) := hA
      _ = ((volume : Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.acube ℓ)) ^ (m + 1 - 1)
          * (∫⁻ a : EuclideanSpace ℝ (Fin 3), G a
              ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))) := by
            rw [hνuniv, Nat.add_sub_cancel]

end Work.BoseFixB2.Pot
