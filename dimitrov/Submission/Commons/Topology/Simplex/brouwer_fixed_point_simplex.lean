import Submission.Commons.Topology.Simplex.brouwer_stdSimplex

namespace Commons.Topology.Simplex

/-- **Brouwer's fixed point theorem for the standard simplex.**

For `n ≥ 1`, every continuous self-map `f` of the standard `(n-1)`-simplex
`{x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}` has a fixed point.

This is the form of the theorem needed for Dimitrov's bound on the house of a nonzero
algebraic integer that is not a root of unity (McKee–Smyth, Chapter 4, Theorem 4.1).

The shared commons contains the full combinatorial development (Sperner's lemma on the
Freudenthal triangulation of the simplex grid, `sperner_grid_nat`, its quantitative
consequence `exists_approx_fixed_point_stdSimplex`, and the theorem itself as
`brouwer_stdSimplex`), so we reduce to that. -/
theorem brouwer_fixed_point_simplex (n : ℕ) (hn : 0 < n) (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : Continuous f)
    (hmaps : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1) :
    ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ f x = x :=
  brouwer_stdSimplex n hn f hf hmaps

end Commons.Topology.Simplex
