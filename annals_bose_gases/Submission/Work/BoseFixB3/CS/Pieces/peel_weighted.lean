import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.PotWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.peel_weighted`

Weighted one-slot peel of the centred-box integral: if the weight `K` does not depend on the
slot-`i` coordinate (`hKi`), then

  `∫_{abox (m+1) ℓ} K·Ψ = ∫_{abox m ℓ} K (kcInsN m i (0,r)) · (∫_{acube ℓ} Ψ (kcInsN m i (y,r)))`.

The proof is the corpus peel `BoseGases.abox_integral_peel` (Fubini over the measure-preserving
insertion `kcInsN m i`), followed by `K (kcInsN m i (y,r)) = K (kcInsN m i (0,r))`
(`kcInsN_update_zero` + `hKi`) and linearity of the inner integral.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem peel_weighted {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (m + 1))
    {K Ψ : Submission.BoseGases.X (m + 1) → ℝ}
    (hKi : ∀ (x : Submission.BoseGases.X (m + 1)) (z : EuclideanSpace ℝ (Fin 3)),
      K (Function.update x i z) = K x)
    (hInt : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m =>
        K (Submission.BoseGases.kcInsN m i p) * Ψ (Submission.BoseGases.kcInsN m i p))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m ℓ)))) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ, K x * Ψ x)
      = ∫ r : Submission.BoseGases.X m,
          K (Submission.BoseGases.kcInsN m i (0, r))
            * (∫ y in Submission.BoseGases.acube ℓ,
                Ψ (Submission.BoseGases.kcInsN m i (y, r)))
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) := by
  -- Abbreviations for the peeled (product) measure and the box measure.
  let μ' : MeasureTheory.Measure E3 :=
    (MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ)
  let ν : MeasureTheory.Measure (Submission.BoseGases.X m) :=
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m ℓ)
  -- The insertion of slot `i` is measure preserving from the product measure to the box measure.
  have hmp : MeasureTheory.MeasurePreserving (⇑(Submission.BoseGases.kcInsN m i)) (μ'.prod ν)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ)) := by
    have h := MeasureTheory.MeasurePreserving.symm
      (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) i)
      (Submission.BoseGases.abox_peel_mp m ℓ i)
    simpa [Submission.BoseGases.kcInsN, μ', ν] using h
  -- Integrability of `K·Ψ` on the box, transported from `hInt` along the measure-preserving map.
  have hF : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (m + 1) => K x * Ψ x)
      (Submission.BoseGases.abox (m + 1) ℓ) MeasureTheory.volume := by
    have h2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X (m + 1) => K x * Ψ x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ)) :=
      (hmp.integrable_comp_emb
        (MeasurableEquiv.measurableEmbedding (Submission.BoseGases.kcInsN m i))
        (g := fun x : Submission.BoseGases.X (m + 1) => K x * Ψ x)).mp hInt
    exact h2
  rw [Submission.BoseGases.abox_integral_peel (i := i) (n := m)
    (F := fun x : Submission.BoseGases.X (m + 1) => K x * Ψ x) hF]
  -- Slot-`i` invariance of `K`, and linearity of the inner integral.
  trans ∫ r : Submission.BoseGases.X m,
      (∫ y in Submission.BoseGases.acube ℓ,
        K (Submission.BoseGases.kcInsN m i (0, r))
          * Ψ (Submission.BoseGases.kcInsN m i (y, r)))
      ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ))
  · refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with r
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
    intro y _
    have h1 : K (Submission.BoseGases.kcInsN m i (y, r))
        = K (Submission.BoseGases.kcInsN m i (0, r)) := by
      rw [Submission.BoseGases.kcInsN_update_zero i y r]
      exact hKi (Submission.BoseGases.kcInsN m i (0, r)) y
    show K (Submission.BoseGases.kcInsN m i (y, r)) * Ψ (Submission.BoseGases.kcInsN m i (y, r))
      = K (Submission.BoseGases.kcInsN m i (0, r)) * Ψ (Submission.BoseGases.kcInsN m i (y, r))
    rw [h1]
  · refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with r
    exact MeasureTheory.integral_const_mul (K (Submission.BoseGases.kcInsN m i (0, r)))
      (fun y : E3 => Ψ (Submission.BoseGases.kcInsN m i (y, r)))

end Work.BoseFixB3.CS.Pieces
