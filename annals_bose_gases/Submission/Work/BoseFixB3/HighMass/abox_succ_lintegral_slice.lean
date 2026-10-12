import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.abox_succ_lintegral_slice` — Fubini/`piFinSuccAbove` slicing of `abox`

The box-restricted (`abox (m+1) ℓ`) integral of a nonnegative a.e.-measurable function is the
iterated integral over the `i`-th coordinate (`acube ℓ`) and the remaining `m` coordinates
(`abox m ℓ`), via the measure-preserving equivalence
`MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ³) i`.

The ingredients are the corpus's product-measure identity
`Submission.BoseGases.restrict_abox_eq_pi` (`volume ↾ abox N ℓ = πᵢ (volume ↾ acube ℓ)`) and
`measurePreserving_piFinSuccAbove`; the Tonelli step is `lintegral_prod_symm`, whose
a.e.-measurability hypothesis is transported along the measure-preserving equivalence.
-/

namespace Work.BoseFixB3.HighMass

open MeasureTheory

theorem abox_succ_lintegral_slice {m : ℕ} {ℓ : ℝ} (i : Fin (m + 1))
    (F : Submission.BoseGases.X (m + 1) → ENNReal)
    (hF : AEMeasurable F ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 1))).restrict
      (Submission.BoseGases.abox (m + 1) ℓ))) :
    ∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ, F x
      = ∫⁻ a in Submission.BoseGases.abox m ℓ, ∫⁻ b in Submission.BoseGases.acube ℓ,
          F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ³) i).symm (b, a)) := by
  -- the one-particle measure of a single sliced coordinate
  set μ : Measure ℝ³ := (volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ) with hμ
  set e : Submission.BoseGases.X (m + 1) ≃ᵐ (ℝ³ × Submission.BoseGases.X m) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ³) i with he
  -- the box measures are the product measures of the sliced coordinates
  have hpi : (Measure.pi fun _ : Fin (m + 1) => μ)
      = (volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ) := by
    simpa [hμ] using (Submission.BoseGases.restrict_abox_eq_pi (m + 1) ℓ).symm
  have hpim : (Measure.pi fun _ : Fin m => μ)
      = (volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ) := by
    simpa [hμ] using (Submission.BoseGases.restrict_abox_eq_pi m ℓ).symm
  have hFpi : AEMeasurable F (Measure.pi fun _ : Fin (m + 1) => μ) := by rw [hpi]; exact hF
  -- `piFinSuccAbove` is measure preserving (stated in the reverse direction)
  have hmp : MeasurePreserving e.symm (μ.prod (Measure.pi fun _ : Fin m => μ))
      (Measure.pi fun _ : Fin (m + 1) => μ) := by
    simpa [he, hμ] using (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i).symm
  have hAE : AEMeasurable (fun z : ℝ³ × Submission.BoseGases.X m => F (e.symm z))
      (μ.prod (Measure.pi fun _ : Fin m => μ)) :=
    hFpi.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have key1 : ∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ, F x
      = ∫⁻ x, F x ∂(Measure.pi fun _ : Fin (m + 1) => μ) := by rw [← hpi]
  have key2 : ∫⁻ x, F x ∂(Measure.pi fun _ : Fin (m + 1) => μ)
      = ∫⁻ z, F (e.symm z) ∂(μ.prod (Measure.pi fun _ : Fin m => μ)) :=
    (hmp.lintegral_comp_emb e.symm.measurableEmbedding F).symm
  have key3 : ∫⁻ z, F (e.symm z) ∂(μ.prod (Measure.pi fun _ : Fin m => μ))
      = lintegral (Measure.pi fun _ : Fin m => μ)
          (fun a : Submission.BoseGases.X m => lintegral μ (fun b : ℝ³ => F (e.symm (b, a)))) :=
    lintegral_prod_symm _ hAE
  have key4 : lintegral (Measure.pi fun _ : Fin m => μ)
        (fun a : Submission.BoseGases.X m => lintegral μ (fun b : ℝ³ => F (e.symm (b, a))))
      = ∫⁻ a in Submission.BoseGases.abox m ℓ, ∫⁻ b in Submission.BoseGases.acube ℓ,
          F (e.symm (b, a)) := by
    rw [← hpim]
  exact key1.trans (key2.trans (key3.trans key4))

end Work.BoseFixB3.HighMass
