import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.volume_eq_zero_of_dimH_lt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The low-dimensional case of Sard's theorem, localized

If `n < m` and `f : ℝⁿ → ℝᵐ` is `C¹` on an open set `U`, then `f '' U` is Lebesgue-null: a `C¹` map
on an open set is locally Lipschitz, and a locally Lipschitz map does not increase Hausdorff
dimension (`dimH_image_le_of_locally_lipschitzOn`), while `dimH U ≤ n < m` and a subset of `ℝᵐ` of
Hausdorff dimension `< m` is null.
-/

open scoped ContDiff MeasureTheory Topology ENNReal NNReal
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

/-- **The low-dimensional case of Sard's theorem, localized on an open set.** -/
theorem lowDimOn {n m : ℕ} (h : n < m)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    MeasureTheory.volume (f '' U) = 0 := by
  refine volume_eq_zero_of_dimH_lt (d := m) ?_
  have hloc : ∀ x ∈ U, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[U] x, LipschitzOnWith C f t := by
    intro x hx
    obtain ⟨C, t, ht, hCt⟩ := (hf.contDiffAt (hU.mem_nhds hx)).exists_lipschitzOnWith
    exact ⟨C, t, nhdsWithin_le_nhds ht, hCt⟩
  have h1 : dimH (f '' U) ≤ dimH U :=
    dimH_image_le_of_locally_lipschitzOn hloc
  have h2 : dimH U ≤ (n : ℝ≥0∞) := by
    have := dimH_mono (Set.subset_univ U)
    rwa [Real.dimH_univ_eq_finrank, finrank_euclideanSpace, Fintype.card_fin] at this
  refine lt_of_le_of_lt (le_trans h1 h2) ?_
  exact_mod_cast h

end Work.ThomBordism.Transversality.Sard
