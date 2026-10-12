import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latTransfer_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lintegral_periodisation_boxL`

The `ENNReal`-valued "tiling" identity for the `ℓℤ³`-periodisation of `W`: integrating the
periodisation `∑'_m ‖W (z + ℓ • latVec m)‖ₑ` over the fundamental domain `boxL ℓ = [-ℓ/2,ℓ/2]³`
recovers the full `∫⁻ ‖W‖ₑ` (for a general `AEMeasurable W`, not just an `L¹` one).

The proof reuses the fundamental-domain `AddAction` of `latTransfer_integral` (the translations
`m +ᵥ z = z + ℓ • latVec m`, together with its `MeasurableConstVAdd` and `VAddInvariantMeasure`
instances) and the two half-open/closed comparisons:

* `boxL ℓ =ᵐ latChl ℓ` (`boxL_ae_eq_latChl`), transported to the measures by
  `Measure.restrict_congr_set`;
* `∑'_m` moved out of the integral by `lintegral_tsum` (each summand is a.e. measurable, being a
  `enorm` of a translate of the `AEMeasurable` `W`);
* the fundamental-domain identity `IsAddFundamentalDomain.lintegral_eq_tsum''` for the half-open
  domain `latChl ℓ` finishes, its `g +ᵥ x` being definitionally the translate `x + ℓ • latVec g`.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-! ## Two elementary lattice lemmas (again, as they are `private` in `latTransfer_integral`) -/

private lemma latVec_neg_per (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  rw [latVec_apply, Pi.neg_apply, Int.cast_neg]
  rfl

/-- The tile of the zero lattice vector is the cell itself. -/
private lemma latTile_zero_per (ℓ : ℝ) : latTile ℓ (0 : Fin 3 → ℤ) = LatFourier.latCell ℓ := by
  ext x
  rw [latTile_mem, LatFourier.mem_latCell, LatFourier.mem_latCell, LatFourier.latVec_zero,
    smul_zero, sub_zero]

-- The `ENNReal`-valued "tiling" identity for the `ℓℤ³`-periodisation of `W`: integrating the
-- periodisation `∑'_m ‖W (z + ℓ • latVec m)‖ₑ` over the fundamental domain `boxL ℓ = [-ℓ/2,ℓ/2]³`
-- recovers the full `∫⁻ ‖W‖ₑ` (note: for a general `AEMeasurable W`, not just an `L¹` one).
-- Route (all ingredients exist): `boxL ℓ =ᵐ latChl ℓ` (`boxL_ae_eq_latChl`) with
-- `Measure.restrict_congr_set`; `latChl ℓ` is a fundamental domain (`latTransfer_integral`:
-- `IsAddFundamentalDomain` for the `AddAction` `m +ᵥ z = z + ℓ • latVec m` and its
-- `MeasurableConstVAdd`/`VAddInvariantMeasure` instances); `lintegral_tsum` to move `∑'_m` out;
-- `MeasurePreserving.setLIntegral_comp_emb` (+ `measurableEmbedding_addRight`) for the translation
-- `z ↦ z + ℓ • latVec m`; `MeasureTheory.lintegral_sum_measure` and
-- `IsAddFundamentalDomain.sum_restrict` (`∑' m, volume.restrict (latChl ℓ + ℓ • latVec m) = volume`)
-- to finish.
theorem lintegral_periodisation_boxL {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : AEMeasurable W MeasureTheory.volume) :
    (∫⁻ z in Work.BoseK15.corpusBox.boxL ℓ,
        (∑' m : Fin 3 → ℤ, ‖W (z + ℓ • Work.BoseBoxFock.latVec m)‖ₑ))
      = ∫⁻ z, ‖W z‖ₑ := by
  -- the action of `ℤ³` on `E3` by the translations `x ↦ x + ℓ • latVec m` (as in
  -- `latTransfer_integral`, where it is local to the proof)
  let act : AddAction (Fin 3 → ℤ) E3 :=
    { vadd := fun m x => x + ℓ • latVec m
      zero_vadd := fun x => by
        show x + ℓ • latVec (0 : Fin 3 → ℤ) = x
        rw [LatFourier.latVec_zero, smul_zero, add_zero]
      add_vadd := fun m m' x => by
        show x + ℓ • latVec (m + m') = (x + ℓ • latVec m') + ℓ • latVec m
        rw [LatFourier.latVec_add, smul_add]; abel }
  letI := act
  haveI : MeasurableConstVAdd (Fin 3 → ℤ) E3 :=
    ⟨fun c => by show Measurable fun x : E3 => x + ℓ • latVec c; fun_prop⟩
  haveI : VAddInvariantMeasure (Fin 3 → ℤ) E3 (volume : Measure E3) :=
    ⟨fun c s hs => by
      show volume ((fun x : E3 => x + ℓ • latVec c) ⁻¹' s) = volume s
      exact MeasurePreserving.measure_preimage (measurePreserving_add_right volume (ℓ • latVec c))
        hs.nullMeasurableSet⟩
  -- the half-open cell `[0,ℓ)³` is a fundamental domain
  have hfdC : IsAddFundamentalDomain (Fin 3 → ℤ) (LatFourier.latCell ℓ) volume := by
    refine IsAddFundamentalDomain.mk'' (LatFourier.measurableSet_latCell ℓ).nullMeasurableSet
      (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · have hx : x ∈ ⋃ m : Fin 3 → ℤ, latTile ℓ m := by rw [latTile_cover ℓ hℓ]; trivial
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      refine ⟨-m, ?_⟩
      have hm' : x - ℓ • latVec m ∈ LatFourier.latCell ℓ := (latTile_mem ℓ m x).mp hm
      show x + ℓ • latVec (-m) ∈ LatFourier.latCell ℓ
      rw [latVec_neg_per, smul_neg]
      exact hm'
    · intro g hg
      have hd : Disjoint (g +ᵥ LatFourier.latCell ℓ) (LatFourier.latCell ℓ) := by
        have h : Disjoint (latTile ℓ g) (latTile ℓ (0 : Fin 3 → ℤ)) := latTile_disjoint ℓ hℓ hg
        rw [latTile_zero_per ℓ] at h
        exact h
      exact Disjoint.aedisjoint hd
    · intro g
      show Measure.QuasiMeasurePreserving (fun x : E3 => x + ℓ • latVec g) volume volume
      exact (measurePreserving_add_right volume (ℓ • latVec g)).quasiMeasurePreserving
  -- the centred half-open cube is its translate by `-latChlCtr ℓ`
  have hfdChl : IsAddFundamentalDomain (Fin 3 → ℤ) (latChl ℓ) volume := by
    have h := hfdC.preimage_of_equiv (s := LatFourier.latCell ℓ)
        (f := fun z : E3 => z + latChlCtr ℓ)
        (measurePreserving_add_right volume (latChlCtr ℓ)).quasiMeasurePreserving
        (e := id) Function.bijective_id (fun g x => by
          show (x + ℓ • latVec g) + latChlCtr ℓ = (x + latChlCtr ℓ) + ℓ • latVec g
          abel)
    rwa [← latChl_eq_preimage ℓ] at h
  -- the closed centred cube can be replaced by the half-open one
  have hbox : (∫⁻ z in Work.BoseK15.corpusBox.boxL ℓ,
        (∑' m : Fin 3 → ℤ, ‖W (z + ℓ • latVec m)‖ₑ))
      = ∫⁻ z in latChl ℓ, (∑' m : Fin 3 → ℤ, ‖W (z + ℓ • latVec m)‖ₑ) := by
    rw [← Measure.restrict_congr_set (boxL_ae_eq_latChl hℓ)]
  rw [hbox]
  -- move the sum out of the integral
  rw [lintegral_tsum (f := fun (m : Fin 3 → ℤ) (z : E3) => ‖W (z + ℓ • latVec m)‖ₑ) ?_]
  · -- the fundamental-domain identity, read backwards
    rw [IsAddFundamentalDomain.lintegral_eq_tsum'' hfdChl (fun z : E3 => ‖W z‖ₑ)]
    exact tsum_congr (fun g => rfl)
  · intro m
    exact AEMeasurable.restrict (measurable_enorm.comp_aemeasurable
      (hWm.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (ℓ • latVec m)).quasiMeasurePreserving))

end Work.BoseBoxFock
