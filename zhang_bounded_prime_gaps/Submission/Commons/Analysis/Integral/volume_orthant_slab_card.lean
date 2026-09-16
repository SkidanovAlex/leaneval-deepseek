import Mathlib
import Submission.Commons.Analysis.Integral.volume_orthant_slab_ge_one

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Commons.Analysis.Integral

noncomputable section

/-- The volume of the region `{t : ι → ℝ | tᵢ ≥ 0, a ≤ ∑ tᵢ ≤ c}` is `(c ^ n - a ^ n) / n!`,
where `n = card ι`.  This is the general-`ι` form of `volume_orthant_slab_ge_one`, obtained by
reindexing along a measurable equivalence `Fin (card ι) ≃ᵐ ι`. -/
theorem volume_orthant_slab_card {ι : Type*} [Fintype ι] (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c)
    (hι : 1 ≤ Fintype.card ι) :
    (MeasureTheory.volume {t : ι → ℝ | (∀ i, 0 ≤ t i) ∧ a ≤ ∑ i, t i ∧ ∑ i, t i ≤ c}).toReal
      = (c ^ (Fintype.card ι) - a ^ (Fintype.card ι)) / (Nat.factorial (Fintype.card ι) : ℝ) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hE : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) MeasureTheory.volume MeasureTheory.volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) ⁻¹'
        {t : ι → ℝ | (∀ i, 0 ≤ t i) ∧ a ≤ ∑ i, t i ∧ ∑ i, t i ≤ c}
      = {t : Fin (Fintype.card ι) → ℝ | (∀ i, 0 ≤ t i) ∧ a ≤ ∑ i, t i ∧ ∑ i, t i ≤ c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hx : ∀ j : Fin (Fintype.card ι),
        (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) x (e j) = x j :=
      fun j => MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e x j
    have hsum : ∑ i : ι, (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) x i
        = ∑ j : Fin (Fintype.card ι), x j := by
      rw [← Equiv.sum_comp e (fun i => (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) x i)]
      exact Finset.sum_congr rfl (fun j _ => hx j)
    have hnonneg : (∀ i : ι, 0 ≤ (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) x i)
        ↔ (∀ j : Fin (Fintype.card ι), 0 ≤ x j) := by
      constructor
      · intro h j
        have := h (e j)
        rwa [hx j] at this
      · intro h i
        rw [← e.apply_symm_apply i, hx (e.symm i)]
        exact h (e.symm i)
    rw [hnonneg, hsum]
  rw [← hE.measure_preimage_equiv
    {t : ι → ℝ | (∀ i, 0 ≤ t i) ∧ a ≤ ∑ i, t i ∧ ∑ i, t i ≤ c}, hpre]
  exact volume_orthant_slab_ge_one hι ha hac

end

end Commons.Analysis.Integral
