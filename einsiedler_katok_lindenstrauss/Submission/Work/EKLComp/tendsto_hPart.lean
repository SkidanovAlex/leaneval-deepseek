import Mathlib
import Submission.Work.EKLComp.Entropy

/-!
# `Hfam μ (⋁_{k<M} T^{-k} P) / M → h_μ(T,P)` (Fekete / Shannon–McMillan–Breiman setup)

The defining infimum of `hPart μ T P = ⨅_N Hfam μ (joinSets T P (N+1)) / (N+1)` is attained
as a limit: `N ↦ Hfam μ (⋁_{k<N} T^{-k} P)` is subadditive for a measure-preserving `T`
(`Work.EKLComp.Core.Hfam_joinSets_add_le`), so Fekete's lemma applies and the limit is the
infimum (`Work.EKLComp.Core.hPart_eq_lim`).

This is the unquotiented convergence statement used when setting up the Kolmogorov–Sinai
entropy of a measure-preserving transformation.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace Work.EKLComp

theorem tendsto_hPart {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {T : X → X} (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (P : Work.EKLContract.FinPart X) :
    Filter.Tendsto
      (fun M : ℕ => Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P M) / (M : ℝ))
      Filter.atTop (nhds (Work.EKLContract.hPart μ T P)) := by
  have hsub : Subadditive
      (fun N => Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P N)) :=
    fun m n => Work.EKLComp.Core.Hfam_joinSets_add_le μ hmp P m n
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P n) / (n : ℝ)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩
           exact div_nonneg (Work.EKLComp.Core.Hfam_nonneg μ _) (Nat.cast_nonneg n)⟩
  have hlim := hsub.tendsto_lim hbdd
  have heq := Work.EKLComp.Core.hPart_eq_lim μ hmp P hsub
  rw [heq]
  exact hlim

end Work.EKLComp
