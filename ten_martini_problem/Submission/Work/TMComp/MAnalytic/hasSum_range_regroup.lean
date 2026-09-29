import Mathlib

namespace Work.TMComp.MAnalytic

/-- Regrouping a summable family `g : ℕ × ℕ → ℂ` by anti-diagonals: summing
`g (k, N - k)` for `k ∈ range (N + 1)` over all `N` recovers `∑' p, g p`. -/
theorem hasSum_range_regroup {g : ℕ × ℕ → ℂ} (hg : Summable g) :
    HasSum (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), g (k, N - k)) (∑' p : ℕ × ℕ, g p) := by
  -- Reindex `ℕ × ℕ` as the disjoint union of its anti-diagonals.
  have h1 : HasSum (fun x : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      g (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd x)) (∑' p : ℕ × ℕ, g p) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr hg.hasSum
  -- Fubini over the anti-diagonal fibres (each fibre is finite).
  have h2 : HasSum (fun n : ℕ => ∑ c : ↥(Finset.HasAntidiagonal.antidiagonal n),
      g (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd ⟨n, c⟩)) (∑' p : ℕ × ℕ, g p) :=
    h1.sigma fun n => hasSum_fintype (fun c : ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      g (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd ⟨n, c⟩))
  -- Identify each fibre sum with the corresponding `range` sum.
  have key : ∀ n : ℕ, (∑ c : ↥(Finset.HasAntidiagonal.antidiagonal n),
      g (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd ⟨n, c⟩))
      = ∑ k ∈ Finset.range (n + 1), g (k, n - k) := by
    intro n
    have hcast : (∑ c : ↥(Finset.HasAntidiagonal.antidiagonal n),
        g (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd ⟨n, c⟩))
        = ∑ c : ↥(Finset.HasAntidiagonal.antidiagonal n), g (c : ℕ × ℕ) :=
      Finset.sum_congr rfl (fun c _ =>
        by rw [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply])
    rw [hcast, ← Finset.sum_subtype (Finset.HasAntidiagonal.antidiagonal n) (fun x => Iff.rfl) g,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [funext key] at h2
  exact h2

end Work.TMComp.MAnalytic
