import Submission.Work.Deep.GKO.Defs

/-!
# Combining matchings: the final bookkeeping of the reduction

The reduction colours the edges of `G` with `Δ(G)` colours by
* removing `k` spanning linear forests `F_1, …, F_k` (two colours each), leaving a regular
  graph `G_k` of degree `r = Δ - 2k`, and
* decomposing `G_k` into `r` perfect matchings.

This module contains the reindexing bookkeeping: a 1-factorization is a matching
decomposition, and a perfect matching is a one-part matching decomposition.  Together
with `Work.Deep.GKO.colorable_of_matchingDecomposition` this turns a partition of `E(G)`
into `Δ(G)` matchings into a `Δ(G)`-edge-colouring of the hypergraph.

We also record the monotonicity of robust expansion in its range parameter `τ`, used to
relate the explicit robust expansion guaranteed by lower regularity to the (weaker)
hypothesis of the Kühn–Osthus result.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## Robust expansion is monotone in the range parameter -/

/-- If `G` is a robust `(ν,τ₁)`-expander and `τ₁ ≤ τ₂` then it is a robust `(ν,τ₂)`-expander:
the condition at a smaller `τ` is the stronger one.  Consequently, if lower regularity
yields robust expansion at an explicit parameter `τ_min`, then the Kühn–Osthus theorem
applies as soon as its own threshold `τ(α)` is at least `τ_min`. -/
theorem robustExpander_mono_tau {G : SimpleGraph (Fin n)} {ν τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂)
    (hG : RobustExpander G ν τ₁) : RobustExpander G ν τ₂ := by
  intro S h1 h2
  exact hG S (le_trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)) h1)
    (le_trans h2 (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)))

/-- Robust expansion at a smaller robustness parameter is weaker: `RobustExpander G ν₁ τ`
implies `RobustExpander G ν₂ τ` for `ν₂ ≤ ν₁`. -/
theorem RobustExpander.mono_nu {G : SimpleGraph (Fin n)} {ν₁ ν₂ τ : ℝ} (h : ν₂ ≤ ν₁)
    (hG : RobustExpander G ν₁ τ) : RobustExpander G ν₂ τ := by
  intro S h1 h2
  have hsub : robustNbrs G ν₁ S ⊆ robustNbrs G ν₂ S := by
    intro x hx
    exact le_trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)) hx
  have hcard : ((robustNbrs G ν₁ S).ncard : ℝ) ≤ ((robustNbrs G ν₂ S).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
  have hmain := hG S h1 h2
  have hle : ν₂ * (n : ℝ) ≤ ν₁ * (n : ℝ) := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)
  linarith

/-! ## From factorizations to matching decompositions -/

/-- A 1-factorization is a matching decomposition. -/
theorem hasMatchingDecomposition_of_oneFactorization {G : SimpleGraph (Fin n)} {r : ℕ}
    (h : HasOneFactorization G r) : HasMatchingDecomposition G r := by
  classical
  obtain ⟨M, hMp, hdisj, hcov⟩ := h
  exact ⟨M, fun i v w w' hw hw' => ((hMp i).2 v).unique hw hw', fun i => (hMp i).1,
    hdisj, hcov⟩

/-- A perfect matching (viewed as a graph on all of `Fin n`) is a one-part matching
decomposition of itself. -/
theorem hasMatchingDecomposition_self_of_perfectMatching (M : SimpleGraph (Fin n))
    (h : ∀ v : Fin n, ∃! w : Fin n, M.Adj v w) : HasMatchingDecomposition M 1 := by
  classical
  refine ⟨fun _ => M, fun i v w w' hw hw' => (h v).unique hw hw', fun i => le_rfl, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro e he
    exact ⟨0, he⟩

end

end Work.Deep.GKO
