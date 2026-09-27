import Mathlib
import Submission.Work.Projection.Basic
import Submission.Work.Projection.Defs
import Submission.Work.Projection.exists_good_direction
import Submission.Work.Projection.dimH_badImmCharts_sharp
import Submission.Work.Projection.compact_embedding

/-!
# Immersions of a compact manifold into `ℝ^{2n}`

The "immersion-bad" directions of a projection have Hausdorff dimension at most `2n-1`
(`dimH_badImmCharts_sharp`), so a projection from `ℝ^{2n+1}` to `ℝ^{2n}` can be chosen so that
it preserves the immersion property.  Starting from the embedding of a compact `n`-manifold in
`ℝ^{2n+1}` (`exists_embedding_euclidean_of_compact`) this gives an immersion into `ℝ^{2n}`,
the starting point of the classical proof of the strong Whitney embedding theorem.
-/

open scoped Manifold ContDiff
open Topology MeasureTheory

namespace Work.Projection

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- **Existence of a good projection direction for immersions.**  Given an immersion
`f : M → ℝ^{k+1}` with `2n ≤ k` and a countable chart cover, there is a direction `u : ℝ^k`
such that `projVec u ∘ f` is again an immersion. -/
theorem exists_good_direction_immersion (hn : 1 ≤ n) (hk : 2 * n ≤ k)
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (k+1)) f x))
    (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    ∃ u : EuclideanSpace ℝ (Fin k),
      ∀ x, Function.Injective (projVec u ∘L mfderiv (𝓡 n) (𝓡 (k+1)) f x) := by
  have hbound : dimH (badImmCharts (n := n) (k := k) f p) ≤ 2 * n - 1 :=
    dimH_badImmCharts_sharp f hf p
  have hn' : 0 < n := hn
  have hlt : dimH (badImmCharts (n := n) (k := k) f p) <
      dimH (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := by
    rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
    refine lt_of_le_of_lt hbound ?_
    have h2 : 2 * n - 1 < k := by omega
    exact_mod_cast h2
  obtain ⟨u, hu⟩ : ∃ u, u ∉ badImmCharts (n := n) (k := k) f p := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    have : badImmCharts (n := n) (k := k) f p =
        (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := Set.eq_univ_iff_forall.2 h
    rw [this] at hlt
    exact lt_irrefl _ hlt
  exact ⟨u, injective_projVec_comp_mfderiv f hf himm hcov hu⟩

/-- **Immersion theorem for compact manifolds.**  A compact smooth `n`-manifold immerses into
`ℝ^{2n}`. -/
theorem exists_immersion_euclidean_of_compact (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨fun _ => 0, contMDiff_const, fun x => ?_⟩
    haveI : Subsingleton (TangentSpace (𝓡 0) x) :=
      show Subsingleton (EuclideanSpace ℝ (Fin 0)) from inferInstance
    exact fun a b _ => Subsingleton.elim a b
  · rcases isEmpty_or_nonempty M with hM | hM
    · haveI : IsEmpty M := hM
      exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
    · haveI := hM
      obtain ⟨e₀, hsm₀, -, himm₀⟩ := exists_embedding_euclidean_of_compact n (M := M)
      obtain ⟨p, hcov⟩ := exists_countable_chart_cover n M
      obtain ⟨u, hu⟩ :=
        exists_good_direction_immersion (n := n) hn (k := 2 * n) le_rfl e₀ hsm₀ himm₀ p hcov
      refine ⟨⇑(projVec u) ∘ e₀, contMDiff_comp_clm (projVec u) e₀ hsm₀, fun x => ?_⟩
      rw [mfderiv_comp_clm (projVec u) e₀ hsm₀ x]
      exact hu x

end Work.Projection
