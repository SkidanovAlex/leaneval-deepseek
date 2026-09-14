import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open MeasureTheory Set
open scoped Pointwise

/-- **Splitting `ℝ^N` as `ℝ^i × ℝ^{N-i}`, measurably and measure-preservingly.**
There is a measurable equivalence `(Fin N → ℝ) ≃ᵐ (Fin i → ℝ) × (Fin (N-i) → ℝ)` which reads off
the first `i` coordinates and the last `N - i` coordinates and preserves the Lebesgue measure.

Suggested proof: reindex `Fin i ⊕ Fin (N-i) ≃ Fin (i + (N-i))` with `finSumFinEquiv` and
`Fin.cast` (`Nat.add_sub_cancel' hi`), and compose `MeasurableEquiv.piCongrLeft` with
`MeasurableEquiv.sumPiEquivProdPi`; use `volume_measurePreserving_piCongrLeft`,
`volume_measurePreserving_sumPiEquivProdPi` and `MeasurePreserving.trans`. -/
theorem measure_preserving_fin_split (i N : ℕ) (hi : i ≤ N) :
    ∃ e : (Fin N → ℝ) ≃ᵐ ((Fin i → ℝ) × (Fin (N - i) → ℝ)),
      MeasurePreserving e volume volume ∧
      (∀ x : Fin N → ℝ, (e x).1 = fun k : Fin i => x (Fin.castLE hi k)) ∧
      (∀ x : Fin N → ℝ, (e x).2 = fun k : Fin (N - i) => x ⟨i + k.val, by omega⟩) := by
  -- Reindex `Fin N` as `Fin i ⊕ Fin (N - i)` via `finSumFinEquiv` and the equality
  -- `i + (N - i) = N`.  This sends `inl k ↦ Fin.castLE hi k` and `inr k ↦ ⟨i + k, _⟩`.
  let σ : Fin i ⊕ Fin (N - i) ≃ Fin N :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hi))
  refine ⟨(MeasurableEquiv.piCongrLeft (fun _ : Fin i ⊕ Fin (N - i) => ℝ) σ.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin i ⊕ Fin (N - i) => ℝ)), ?_, ?_, ?_⟩
  · exact (volume_measurePreserving_piCongrLeft (fun _ : Fin i ⊕ Fin (N - i) => ℝ) σ.symm).trans
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin i ⊕ Fin (N - i) => ℝ))
  · intro x
    ext k
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply, MeasurableEquiv.coe_piCongrLeft]
    rw [← Equiv.symm_apply_apply σ (Sum.inl k), Equiv.piCongrLeft_apply_apply]
    congr 1
  · intro x
    ext k
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply, MeasurableEquiv.coe_piCongrLeft]
    rw [← Equiv.symm_apply_apply σ (Sum.inr k), Equiv.piCongrLeft_apply_apply]
    congr 1

end Commons.GeometryOfNumbers.SuccessiveMinima