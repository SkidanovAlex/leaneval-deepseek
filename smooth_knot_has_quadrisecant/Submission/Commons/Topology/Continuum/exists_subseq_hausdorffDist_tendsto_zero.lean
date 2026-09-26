import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.MetricSpace.Closeds

namespace Commons.Topology.Continuum

/-- Any sequence of nonempty subsets of a fixed closed ball in `ℂ` has a subsequence which
converges in Hausdorff distance to some set `L`. This is the Blaschke selection principle for
subsets of a compact ball: replacing each set by its closure gives a sequence of nonempty compact
subsets of a compact space, and the hyperspace of nonempty compact subsets of a compact space is
compact. -/
theorem exists_subseq_hausdorffDist_tendsto_zero {E : ℕ → Set ℂ} {R : ℝ}
    (hne : ∀ n, (E n).Nonempty) (hsub : ∀ n, E n ⊆ Metric.closedBall (0 : ℂ) R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : Set ℂ,
      Filter.Tendsto (fun n => Metric.hausdorffDist (E (φ n)) L) Filter.atTop (nhds 0) := by
  -- The closed ball is compact (in a proper space such as `ℂ`).
  have hball : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  -- The closure of every `E n` is a nonempty compact subset of the closed ball.
  have hclos_sub : ∀ n, closure (E n) ⊆ Metric.closedBall (0 : ℂ) R := by
    intro n
    calc closure (E n) ⊆ closure (Metric.closedBall (0 : ℂ) R) := closure_mono (hsub n)
      _ = Metric.closedBall (0 : ℂ) R := Metric.isClosed_closedBall.closure_eq
  have hcomp : ∀ n, IsCompact (closure (E n)) := fun n =>
    hball.of_isClosed_subset isClosed_closure (hclos_sub n)
  -- Package the closures as elements of the hyperspace of nonempty compact subsets.
  let G : ℕ → TopologicalSpace.NonemptyCompacts ℂ := fun n =>
    ⟨⟨closure (E n), hcomp n⟩, (hne n).closure⟩
  have hGmem : ∀ n,
      G n ∈ {K : TopologicalSpace.NonemptyCompacts ℂ | (K : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) R} :=
    fun n => hclos_sub n
  -- The set of nonempty compact subsets contained in a compact set is compact (Blaschke).
  have hS : IsCompact {K : TopologicalSpace.NonemptyCompacts ℂ | (K : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) R} :=
    TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hball
  -- Extract a convergent subsequence in the Hausdorff metric on the hyperspace.
  obtain ⟨K, _hKmem, φ, hφmono, hφlim⟩ := hS.tendsto_subseq hGmem
  refine ⟨φ, hφmono, (K : Set ℂ), ?_⟩
  -- Convergence in the hyperspace is convergence of Hausdorff distances to `0`.
  have hdist : Filter.Tendsto (fun n => dist (G (φ n)) K) Filter.atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hφlim
  -- The distance in the hyperspace is the Hausdorff distance of the underlying sets, and
  -- replacing a set by its closure does not change the Hausdorff distance.
  have heq : (fun n => dist (G (φ n)) K)
      = (fun n => Metric.hausdorffDist (E (φ n)) (K : Set ℂ)) := by
    funext n
    simp only [Metric.NonemptyCompacts.dist_eq]
    have hG : (G (φ n) : Set ℂ) = closure (E (φ n)) := rfl
    rw [hG, Metric.hausdorffDist_closure₁]
  rw [heq] at hdist
  exact hdist

end Commons.Topology.Continuum