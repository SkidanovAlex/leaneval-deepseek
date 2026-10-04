import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A smooth bump between a compact set and an open superset

For a compact `K ⊆ (ι → ℝ)` (`ι` finite) contained in an open set `S`, we produce

* an open neighbourhood `W` of `K` with `W ⊆ S`, and
* a smooth function `χ : (ι → ℝ) → ℝ` which is `1` on `W` and whose topological support
  `tsupport χ = closure (support χ)` is contained in `S`.

The construction is the smooth Urysohn lemma for finite-dimensional real normed spaces
(`exists_contDiff_support_eq_eq_one_iff`, from Mathlib's manifold partition-of-unity file):
normality (`normal_exists_closure_subset`) shrinks `S` twice, first to an open `u ⊇ K` with
`closure u ⊆ S`, then to an open `v ⊇ closure u` with `closure v ⊆ S`; the Urysohn function
supported exactly on `v` and equal to `1` exactly on `closure u` does the job.  The double
shrinking is what converts `support χ = v` into the topological-support bound `tsupport χ ⊆ S`.
-/

namespace Work.Diff.STE.B3.SymCalcStep8

/-- **Shrinking lemma.**  A compact set inside an open set of `ι → ℝ` (with `ι` finite) admits an
open neighbourhood `W` on which a smooth bump equal to `1` is supported inside the open set. -/
theorem exists_bump_tsupport_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set (ι → ℝ)) (hK : IsCompact K) (S : Set (ι → ℝ)) (hS : IsOpen S) (hKS : K ⊆ S) :
    ∃ W : Set (ι → ℝ), IsOpen W ∧ K ⊆ W ∧ W ⊆ S ∧
      ∃ χ : (ι → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ y ∈ W, χ y = 1) ∧ tsupport χ ⊆ S := by
  -- shrink `S` to an open set `u` whose closure is still inside `S` (`K` is closed: it is compact)
  obtain ⟨u, huopen, hKu, huc⟩ := normal_exists_closure_subset hK.isClosed hS hKS
  -- shrink once more: an open `v ⊇ closure u` with `closure v ⊆ S`
  obtain ⟨v, hvopen, huv, hvc⟩ := normal_exists_closure_subset isClosed_closure hS huc
  -- smooth Urysohn: a smooth function supported exactly on `v`, equal to `1` exactly on `closure u`
  obtain ⟨χ, hχdiff, -, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (s := v) (t := closure u)
      hvopen isClosed_closure huv
  refine ⟨u, huopen, hKu, subset_closure.trans huc, χ, hχdiff, ?_, ?_⟩
  · -- `χ = 1` on `u`, since `u ⊆ closure u`
    intro y hy
    exact (hχone y).mp (subset_closure hy)
  · -- `tsupport χ = closure (support χ) = closure v ⊆ S`
    rw [tsupport, hχsupp]
    exact hvc

end Work.Diff.STE.B3.SymCalcStep8
