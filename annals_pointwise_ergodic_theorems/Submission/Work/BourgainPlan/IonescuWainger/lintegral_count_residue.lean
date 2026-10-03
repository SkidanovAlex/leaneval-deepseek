import Mathlib

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset
open scoped BigOperators ENNReal

theorem lintegral_count_residue {Q : ℕ} (hQ : 1 ≤ Q) (f : ℤ → ENNReal) :
    MeasureTheory.lintegral MeasureTheory.Measure.count f
      = ∑ r ∈ Finset.range Q, MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun N : ℤ => f ((Q : ℤ) * N + (r : ℤ))) := by
  have hQ0 : NeZero Q := ⟨by omega⟩
  -- Both sides as `∑'` against the counting measure on ℤ.
  have hR : (∑ r ∈ Finset.range Q, MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun N : ℤ => f ((Q : ℤ) * N + (r : ℤ))))
        = ∑ r ∈ Finset.range Q, ∑' N : ℤ, f ((Q : ℤ) * N + ((r : ℕ) : ℤ)) :=
    Finset.sum_congr rfl (fun r _ => MeasureTheory.lintegral_count _)
  rw [MeasureTheory.lintegral_count, hR]
  -- Turn the finite sum over `range Q` into a sum over `Fin Q`.
  rw [← Fin.sum_univ_eq_sum_range (fun r => ∑' N : ℤ, f ((Q : ℤ) * N + ((r : ℕ) : ℤ))) Q]
  -- Reindex `ℤ` by `ℤ × Fin Q` via Euclidean division.
  rw [← Equiv.tsum_eq (Int.divModEquiv Q).symm f]
  simp only [Int.divModEquiv_symm_apply]
  -- Split the double sum and swap the two summations.
  rw [show (∑' c : ℤ × Fin Q, f (c.1 * (Q : ℤ) + ((c.2 : ℕ) : ℤ)))
        = ∑' (N : ℤ), ∑' (i : Fin Q), f (N * (Q : ℤ) + ((i : ℕ) : ℤ)) from
      ENNReal.tsum_prod (f := fun (N : ℤ) (i : Fin Q) => f (N * (Q : ℤ) + ((i : ℕ) : ℤ)))]
  rw [ENNReal.tsum_comm]
  rw [tsum_fintype]
  -- Reconcile `N * Q` with `Q * N`.
  refine Finset.sum_congr rfl (fun i _ => tsum_congr (fun N => ?_))
  congr 1
  ring

end Work.BourgainPlan.IonescuWainger
