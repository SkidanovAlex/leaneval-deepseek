import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxQIndSq_prodTransfer`

The `L²`-norm of FS's mean-free box projection `Q_{B,i} = 1_{B,i} − P_{B,i}`
(`Work.UBBInputs8.boxQInd`) computed on the **product measure**
`Measure.pi (fun _ : Fin (n+1) => volume.restrict (acube ℓ))`, expressed as an integral over the
peeled variables `p = (x i, x ∘ i.succAbove)` ranging over
`(volume.restrict (acube ℓ)).prod (Measure.pi (fun _ : Fin n => volume.restrict (acube ℓ)))`.

The proof is the measure-preserving change of variables
(`MeasureTheory.measurePreserving_piFinSuccAbove` for `MeasurableEquiv.piFinSuccAbove`) together
with the pointwise identification of `boxQInd` in the peeled coordinates, and the elementary
identity `∫ z, 1_A z · f z ∂(volume.restrict (acube ℓ)) = ∫ z in A, f z` for `A ⊆ acube ℓ`.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `MeasurableEquiv.piFinSuccAbove` in the slot `i` is `Fin.insertNth` in the slot `i`. -/
private lemma piFinSuccAbove_symm_eq_insertNth {n : ℕ} (i : Fin (n + 1)) (p : E3 × (Fin n → E3)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm p
      = Fin.insertNth i p.1 p.2 := by
  funext j
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]

/-- The `i`-th coordinate of `(piFinSuccAbove i).symm p` is `p.1`. -/
private lemma piFinSuccAbove_symm_apply_same {n : ℕ} (i : Fin (n + 1)) (p : E3 × (Fin n → E3)) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm p) i = p.1 := by
  rw [piFinSuccAbove_symm_eq_insertNth i p, Fin.insertNth_apply_same]

/-- Updating the `i`-th coordinate of `(piFinSuccAbove i).symm p` is inserting the new value and
keeping the remaining coordinates `p.2`. -/
private lemma update_piFinSuccAbove_symm {n : ℕ} (i : Fin (n + 1))
    (p : E3 × (Fin n → E3)) (z : E3) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm p) i z
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm (z, p.2) := by
  rw [piFinSuccAbove_symm_eq_insertNth i p, piFinSuccAbove_symm_eq_insertNth i (z, p.2)]
  exact Fin.update_insertNth (α := fun _ : Fin (n + 1) => E3) i p.1 z p.2

/-- For `A ⊆ acube ℓ`, integrating `1_A · f` against `volume.restrict (acube ℓ)` is the same as
integrating `f` over `A` (against `volume`). -/
private lemma setIntegral_eq_restrict_acube {ℓ : ℝ} {A : Set E3}
    (hAm : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ) {f : E3 → ℝ} :
    (∫ z, A.indicator (fun _ => (1 : ℝ)) z * f z
        ∂((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)))
      = ∫ z in A, f z := by
  have hg : (fun z => A.indicator (fun _ => (1 : ℝ)) z * f z) = A.indicator f := by
    funext z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  rw [hg]
  have hνA : (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
        (Submission.BoseGases.acube ℓ))).restrict A
      = (MeasureTheory.volume : MeasureTheory.Measure E3).restrict A := by
    rw [Measure.restrict_restrict hAm, Set.inter_eq_left.mpr hAc]
  calc ∫ z, A.indicator f z ∂(((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)))
      = ∫ z in A, f z ∂((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)) := integral_indicator hAm
    _ = ∫ z, f z ∂((((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ))).restrict A) := rfl
    _ = ∫ z, f z ∂((MeasureTheory.volume : MeasureTheory.Measure E3).restrict A) := by rw [hνA]
    _ = ∫ z in A, f z := rfl

theorem boxQIndSq_prodTransfer {n : ℕ} (i : Fin (n + 1)) {ℓ : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {volA : ℝ} (hvolA : volA = (MeasureTheory.volume A).toReal)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨc : Continuous Ψ) :
    (∫ x, (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2
        ∂(MeasureTheory.Measure.pi (fun _ : Fin (n + 1) =>
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ))))
      = ∫ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
          (A.indicator (fun _ => (1 : ℝ)) p.1 *
              Ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i).symm p)
            - (1 / volA) *
              (∫ z, A.indicator (fun _ => (1 : ℝ)) z *
                Ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i).symm (z, p.2))
                ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                  (Submission.BoseGases.acube ℓ)))
            * A.indicator (fun _ => (1 : ℝ)) p.1) ^ 2
          ∂(((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ)).prod
            (MeasureTheory.Measure.pi (fun _ : Fin n =>
              (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ)))) := by
  classical
  have hmp : MeasureTheory.MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i))
      (MeasureTheory.Measure.pi (fun _ : Fin (n + 1) =>
        (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin n =>
          (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube ℓ)))) :=
    MeasureTheory.measurePreserving_piFinSuccAbove
      (μ := fun _ : Fin (n + 1) => (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)) i
  have hpt : ∀ p : E3 × Submission.BoseGases.X n,
      Work.UBBInputs8.boxQInd volA A i Ψ
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm p)
        = A.indicator (fun _ => (1 : ℝ)) p.1 *
              Ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm p)
            - (1 / volA) *
                (∫ z, A.indicator (fun _ => (1 : ℝ)) z *
                  Ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm (z, p.2))
                  ∂((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
                    (Submission.BoseGases.acube ℓ)))
              * A.indicator (fun _ => (1 : ℝ)) p.1 := by
    intro p
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd,
      piFinSuccAbove_symm_apply_same i p]
    have hfun : (fun z => Ψ (Function.update
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm p) i z))
        = fun z => Ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i).symm
            (z, p.2)) := by
      funext z
      rw [update_piFinSuccAbove_symm]
    rw [hfun]
    rw [setIntegral_eq_restrict_acube hAm hAc]
  rw [← hmp.symm.integral_comp' (fun x => (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)]
  simp only [hpt]

end Work.BoseFixB1S
