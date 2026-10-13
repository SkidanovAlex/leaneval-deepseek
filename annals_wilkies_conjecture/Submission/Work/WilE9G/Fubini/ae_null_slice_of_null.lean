import Mathlib

open MeasureTheory

namespace Work.WilE9G.Fubini

/-- The measurable equivalence between a pair of tuples `(x, c)` and the concatenated tuple
`Fin.append x c`.  It is built as the composition of the measurable equivalence splitting a
function on a sum type into its two components (`MeasurableEquiv.sumPiEquivProdPi`) with the
reindexing of `Fin n ⊕ Fin k` as `Fin (n + k)` (`finSumFinEquiv`). -/
noncomputable def finAppendMeasurableEquiv (n k : ℕ) :
    ((Fin n → ℝ) × (Fin k → ℝ)) ≃ᵐ (Fin (n + k) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + k) => ℝ) finSumFinEquiv)

/-- `finAppendMeasurableEquiv` is measure preserving: the product measure on
`(Fin n → ℝ) × (Fin k → ℝ)` is sent to the Lebesgue measure on `Fin (n + k) → ℝ`. -/
lemma measurePreserving_finAppendMeasurableEquiv (n k : ℕ) :
    MeasurePreserving (finAppendMeasurableEquiv n k) volume volume :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin (n + k) => ℝ)
      finSumFinEquiv).comp
    (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin k => ℝ))

/-- The defining property of `finAppendMeasurableEquiv`: it concatenates the two tuples. -/
lemma finAppendMeasurableEquiv_apply (n k : ℕ) (x : Fin n → ℝ) (c : Fin k → ℝ) :
    finAppendMeasurableEquiv n k (x, c) = Fin.append x c := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · rw [Fin.append_left]
    unfold finAppendMeasurableEquiv
    rw [MeasurableEquiv.trans_apply]
    rw [show (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + k) => ℝ) finSumFinEquiv)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ℝ)).symm (x, c)) =
        (Equiv.piCongrLeft (fun _ : Fin (n + k) => ℝ) finSumFinEquiv)
        ((Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ℝ)).symm (x, c)) from rfl]
    rw [← finSumFinEquiv_apply_left]
    rw [Equiv.piCongrLeft_sumInl]
  · rw [Fin.append_right]
    unfold finAppendMeasurableEquiv
    rw [MeasurableEquiv.trans_apply]
    rw [show (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + k) => ℝ) finSumFinEquiv)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ℝ)).symm (x, c)) =
        (Equiv.piCongrLeft (fun _ : Fin (n + k) => ℝ) finSumFinEquiv)
        ((Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ℝ)).symm (x, c)) from rfl]
    rw [← finSumFinEquiv_apply_right]
    rw [Equiv.piCongrLeft_sumInr]

/-- Fubini for Lebesgue measure on `ℝ^{n+k}`: a null set has almost every slice null. -/
theorem ae_null_slice_of_null {n k : ℕ} (Z : Set (Fin (n + k) → ℝ))
    (hZ : MeasureTheory.volume Z = 0) :
    ∀ᵐ c : Fin k → ℝ, MeasureTheory.volume {x : Fin n → ℝ | Fin.append x c ∈ Z} = 0 := by
  -- Transport `Z` to a subset of the product `(Fin n → ℝ) × (Fin k → ℝ)`.
  have h1 : volume ((finAppendMeasurableEquiv n k) ⁻¹' Z) = 0 :=
    MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      (measurePreserving_finAppendMeasurableEquiv n k).quasiMeasurePreserving hZ
  -- Swap the two factors, so that the almost-everywhere statement is about the second factor.
  have h2 : volume (Prod.swap ⁻¹' ((finAppendMeasurableEquiv n k) ⁻¹' Z)) = 0 :=
    MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := (volume : Measure (Fin k → ℝ)))
        (ν := (volume : Measure (Fin n → ℝ)))).quasiMeasurePreserving h1
  have h3 := MeasureTheory.Measure.measure_ae_null_of_prod_null
    (μ := (volume : Measure (Fin k → ℝ))) (ν := (volume : Measure (Fin n → ℝ)))
    (s := Prod.swap ⁻¹' ((finAppendMeasurableEquiv n k) ⁻¹' Z)) h2
  refine h3.mono fun c hc => ?_
  rw [show {x : Fin n → ℝ | Fin.append x c ∈ Z} =
      Prod.mk c ⁻¹' (Prod.swap ⁻¹' ((finAppendMeasurableEquiv n k) ⁻¹' Z)) by
    ext x
    simp [finAppendMeasurableEquiv_apply]]
  exact hc

end Work.WilE9G.Fubini
