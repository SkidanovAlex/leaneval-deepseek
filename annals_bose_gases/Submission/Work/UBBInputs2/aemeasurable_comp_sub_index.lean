import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs2.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs2

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Please place this result in namespace `Work.UBBInputs2` (file
`Submission/Work/UBBInputs2/aemeasurable_comp_sub_index.lean`). Note the statement is written with
fully qualified `MeasureTheory.` names so that it elaborates without any `open`.

Delegated piece of `Work.UBBInputs2.integrable_qLHSBIntegrand`: a.e.-measurability of the composite
`p ↦ u (p.2 i - p.2 j)` on the product space `ℝ³ × X N`, for an a.e.-measurable `u : ℝ³ → ℝ`.
Here `Submission.BoseGases.X N = Fin N → ℝ³` and the measure on it is the product Lebesgue measure.

Proof sketch: let `w := AEMeasurable.mk u hu`, which is measurable (`AEMeasurable.measurable_mk`)
and satisfies `u =ᵐ w` (`AEMeasurable.ae_eq_mk`). The map `p ↦ w (p.2 i - p.2 j)` is measurable
(composition of a measurable map with the continuous map `p ↦ p.2 i - p.2 j`), hence
`AEStronglyMeasurable`. The two functions differ only on the preimage of a null set: take a
measurable null set `T ⊇ {y | u y ≠ w y}` (`MeasureTheory.exists_measurable_superset_of_null`),
then `{p | u (p.2 i - p.2 j) ≠ w (p.2 i - p.2 j)} ⊆ Set.univ ×ˢ {x : X N | x i - x j ∈ T}` and the
latter is null: `MeasureTheory.Measure.prod_prod` gives `volume Set.univ * volume {x | x i - x j ∈ T}`
and the second factor is `Submission.BoseGases.null_preimage_pair_whole` (defined in
`Submission/PairInt.lean`, which you may import) when `i ≠ j`; note `⊤ * 0 = 0`. When `i = j` the
function is constant on the whole space (its value is that of `u` at `0`), hence
`AEStronglyMeasurable` directly. Conclude with `MeasureTheory.AEStronglyMeasurable.congr`. -/
theorem aemeasurable_comp_sub_index {N : ℕ} {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : AEMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) (i j : Fin N) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N => u (p.2 i - p.2 j))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))) := by
  by_cases hij : i = j
  · -- When `i = j` the composite is the constant function `p ↦ u 0`.
    have hconst : (fun p : ℝ³ × Submission.BoseGases.X N => u (p.2 i - p.2 j)) = fun _ => u 0 := by
      funext p; simp [hij]
    rw [hconst]
    exact aestronglyMeasurable_const
  · -- Replace `u` by its measurable representative `w`, and compare on a null set.
    let w : ℝ³ → ℝ := AEMeasurable.mk u hu
    have hwm : Measurable w := AEMeasurable.measurable_mk hu
    have huw : u =ᵐ[volume] w := AEMeasurable.ae_eq_mk hu
    have hN : volume {y : ℝ³ | u y ≠ w y} = 0 := by
      simpa using MeasureTheory.ae_iff.mp huw
    obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null hN
    have hpre : volume {x : Submission.BoseGases.X N | x i - x j ∈ T} = 0 :=
      Submission.BoseGases.null_preimage_pair_whole hTm hT0 i j hij
    have hcont : Continuous (fun p : ℝ³ × Submission.BoseGases.X N => p.2 i - p.2 j) := by fun_prop
    have hmeas : Measurable (fun p : ℝ³ × Submission.BoseGases.X N => w (p.2 i - p.2 j)) :=
      hwm.comp hcont.measurable
    have hASM : AEStronglyMeasurable (fun p : ℝ³ × Submission.BoseGases.X N => w (p.2 i - p.2 j))
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X N))) :=
      hmeas.aestronglyMeasurable
    -- The two composites agree off the product-null set `Set.univ ×ˢ {x | x i - x j ∈ T}`.
    have hsub : {p : ℝ³ × Submission.BoseGases.X N | ¬ (w (p.2 i - p.2 j) = u (p.2 i - p.2 j))} ⊆
        Set.univ ×ˢ {x : Submission.BoseGases.X N | x i - x j ∈ T} := by
      intro p hp
      simp only [Set.mem_prod, Set.mem_univ, true_and]
      exact hTsub (fun h => hp h.symm)
    have hmeasuniv : ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X N)))
        (Set.univ ×ˢ {x : Submission.BoseGases.X N | x i - x j ∈ T}) = 0 := by
      rw [MeasureTheory.Measure.prod_prod, hpre, mul_zero]
    have hbad : ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X N)))
        {p : ℝ³ × Submission.BoseGases.X N | ¬ (w (p.2 i - p.2 j) = u (p.2 i - p.2 j))} = 0 :=
      measure_mono_null hsub hmeasuniv
    have hae : (fun p : ℝ³ × Submission.BoseGases.X N => w (p.2 i - p.2 j)) =ᵐ[
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X N)))]
        (fun p : ℝ³ × Submission.BoseGases.X N => u (p.2 i - p.2 j)) :=
      MeasureTheory.ae_iff.mpr hbad
    exact hASM.congr hae

end Work.UBBInputs2
