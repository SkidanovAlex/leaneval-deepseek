import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSplit.pIndOrth
import Submission.Work.BoseSplit.sqSubAddSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.qInd_pInd_sq_split` — the Parseval splitting `‖QᵢΦ‖² + ‖PᵢΦ‖² = ‖1_A(· i)Φ‖²`

At the FS-faithful box projection `Pᵢ = P_{B,i}` (`Work.UBBInputs8.boxPInd`) and its complement
`Qᵢ = 1_{B,i} − Pᵢ` (`Work.UBBInputs8.boxQInd`), the two parts split the box mass:

  `∫_{abox N ℓ} (QᵢΦ)² + ∫_{abox N ℓ} (PᵢΦ)² = ∫_{abox N ℓ} (1_A(x i)·Φ x)²`.

This is Pythagoras for the orthogonal decomposition `1_A(· i)·Φ = QᵢΦ + PᵢΦ`.  The two ingredients
are

* `Work.BoseSplit.pIndOrth` — the orthogonality `∫ PᵢΦ·(1_A(· i)Φ − PᵢΦ) = 0`, i.e. the
  box mean is the `L²(A)`-orthogonal projection (proved from `Q0C.one_self_N`);
* `Work.BoseSplit.sqSubAddSq` — the abstract Pythagorean identity
  `∫(f−h)² + ∫h² = ∫f²` for `∫ h(f−h) = 0` (all integrands bounded on the finite box).
-/

noncomputable section

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ENNReal

/-- **The Parseval splitting of the box mass.** -/
theorem qInd_pInd_sq_split {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      + (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by
  haveI hfin : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le⟩
  -- bounds of `Φ` and of `PᵢΦ` on the box (compactness + `abs_boxPInd_le`)
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (Submission.BoseGases.zero_mem_abox hℓ.le))
  obtain ⟨B, hB0, hB⟩ := Work.BoseFixB1S.Q0C.abs_boxPInd_le hℓ hvol hA hAc hvolA i hΦc
  -- the a.e. bounds required by `sqSubAddSq`
  have hΦae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)), |Φ x| ≤ C := by
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    simpa [Real.norm_eq_abs] using hC x hx
  have hPae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)), |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ B := by
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    exact hB x hx
  have hfae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)),
      |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    filter_upwards [hΦae] with x hx
    rw [abs_mul]
    have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hmem : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hmem]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
          mul_le_mul hσ hx (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  -- a.e. strong measurability of the two factors
  have hf_aesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    ((measurable_const.indicator hA).comp (measurable_pi_apply i)).aestronglyMeasurable.mul
      hΦc.measurable.aestronglyMeasurable
  have hP_aesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i Φ x)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    Work.BoseFixB1S.Q0C.aem_boxPInd volA A hA i hΦc _
  -- orthogonality of the two parts
  have horth : (∫ x, (Work.UBBInputs8.boxPInd volA A i Φ x)
        * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
            - Work.UBBInputs8.boxPInd volA A i Φ x)
        ∂((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ))) = 0 := by
    simpa only [] using Work.BoseSplit.pIndOrth hℓ hvol hA hvolA hAc i hΦc
  -- Pythagoras
  have key : (∫ x, ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
          - Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)))
      + (∫ x, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)))
      = ∫ x, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) :=
    Work.BoseSplit.sqSubAddSq
      (μ := (volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
      (f := fun x => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      (h := fun x => Work.UBBInputs8.boxPInd volA A i Φ x)
      hf_aesm hP_aesm hfae hPae horth
  simpa only [Work.UBBInputs8.boxQInd] using key

end Work.BoseFixB1S
