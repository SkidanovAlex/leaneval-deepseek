import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPInd_adjoint_int
import Submission.Work.BoseFixB1.boxPInd_self_idem
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.boxPInd_pair_mixed_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BddSector.pairMixedBdd`

The mixed pair identity for the FS box projections `Pᵢ = Work.UBBInputs8.boxPInd volA A i`
(FS `eq:HBU`: `P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B` in slot `i`), in the *measurable/bounded* regularity
that the downstream sector argument needs (the corpus form `Q0C.pair_mixed_N` assumes `Φ`
continuous, which is not available here):

    ∫_{abox N ℓ} (PᵢΦ)·(PⱼΦ) = ∫_{abox N ℓ} (PᵢPⱼΦ)²        (i ≠ j, Φ measurable and bounded on the box).

## Math

Write `Q := PᵢPⱼΦ`.  `Pᵢ` and `Pⱼ` are orthogonal projections of `L²(abox N ℓ)`; the three
ingredients are

* **self-adjointness** `Work.BoseFixB1.boxPInd_adjoint_int`, available for a measurable
  bounded-on-the-box first argument and an `IntegrableOn` second argument (both `PⱼΦ` and `Q`
  are bounded measurable and the box has finite measure);
* **idempotence** `Work.BoseFixB1S.boxPInd_idem` (unconditional);
* **commutation** `Work.BoseFixB1S.boxPInd_boxPInd_comm_good` (`PⱼPᵢ = PᵢPⱼ` on the box), which
  holds for every `GoodState` (= measurable, bounded on the box) argument — proved there by the
  two-slot Fubini identity `twoMean_comm_good`, so no continuity is required.

Then

    ∫ (PᵢΦ)(PⱼΦ) = ∫ Φ·Q         [self-adjointness of Pᵢ, second slot PⱼΦ]
    ∫ Q²          = ∫ (PⱼΦ)·Q     [self-adjointness of Pᵢ, second slot Q, then PᵢQ = Q]
    ∫ (PⱼΦ)·Q     = ∫ Φ·Q         [self-adjointness of Pⱼ, then PⱼQ = Q by commutation + idem.]
-/

namespace Work.BoseFixB1.BddSector

open MeasureTheory

open scoped Real

theorem pairMixedBdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ B) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 := by
  have hB0 : (0 : ℝ) ≤ max B 0 := le_max_right _ _
  have hb' : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ max B 0 :=
    fun x hx => le_trans (hb x hx) (le_max_left _ _)
  have hmPi := Work.BoseFixB1S.measurable_boxPInd volA A hA i hm
  have hmPj := Work.BoseFixB1S.measurable_boxPInd volA A hA j hm
  have hmQ := Work.BoseFixB1S.measurable_boxPInd volA A hA i hmPj
  have hbPi := Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hb'
  have hbPj := Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc j hb'
  have hbQ := Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hbPj
  have hintPj : IntegrableOn (Work.UBBInputs8.boxPInd volA A j Φ)
      (Submission.BoseGases.abox N ℓ) := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
      hmPj.aestronglyMeasurable (max B 0) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs]; exact hbPj x hx)
  have hintQ : IntegrableOn
      (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ))
      (Submission.BoseGases.abox N ℓ) := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
      hmQ.aestronglyMeasurable (max B 0) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs]; exact hbQ x hx)
  -- `Pⱼ` fixes `PᵢPⱼΦ` on the box: `PⱼPᵢPⱼΦ = PᵢPⱼPⱼΦ = PᵢPⱼΦ`
  have hfix : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x := by
    intro x hx
    rw [Work.BoseFixB1S.boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij
        ⟨hmPj, max B 0, hbPj⟩ x hx,
      Work.BoseFixB1S.boxPInd_idem volA A hA hvolA (ne_of_gt hvol) j Φ]
  -- self-adjointness of `Pᵢ`, second argument `PⱼΦ`
  have hA1 : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x :=
    Work.BoseFixB1.boxPInd_adjoint_int hℓ hvol hA hvolA hAc i hm hB0 hb' hmPj hintPj
  -- self-adjointness of `Pᵢ`, second argument `Q = PᵢPⱼΦ`, then `PᵢQ = Q`
  have hB2 : (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A j Φ x
            * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x := by
    rw [show (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
              * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x from by
      apply integral_congr_ae; filter_upwards with x; ring]
    rw [Work.BoseFixB1.boxPInd_adjoint_int (f := Work.UBBInputs8.boxPInd volA A j Φ)
      (h := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ))
      hℓ hvol hA hvolA hAc i hmPj hB0 hbPj hmQ hintQ]
    apply integral_congr_ae
    filter_upwards with x
    rw [Work.BoseFixB1S.boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i
      (Work.UBBInputs8.boxPInd volA A j Φ)]
  -- self-adjointness of `Pⱼ`, second argument `Q`, then `PⱼQ = Q`
  have hC2 : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A j Φ x
          * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x := by
    rw [Work.BoseFixB1.boxPInd_adjoint_int (f := Φ)
      (h := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ))
      hℓ hvol hA hvolA hAc j hm hB0 hb' hmQ hintQ]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    rw [hfix x hx]
  exact hA1.trans (hC2.symm.trans hB2.symm)

end Work.BoseFixB1.BddSector
