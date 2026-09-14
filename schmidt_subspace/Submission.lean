import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Subspace.Stage2Assembly
import Submission.Subspace.RealRank.LowRank

/-!
# Schmidt's subspace theorem

The challenge statement is derived from the classical affine subspace theorem in
"normals form" (`Submission.Subspace.subspaces_imp_normals`,
`Submission.Subspace.normals_imp_challenge`, both already proved), which in turn follows
from the proper-`ℚ`-subspace form `Submission.Subspace.SubspaceTheoremSubspaces`.

That last statement is reduced here to the single deep input
`Submission.Subspace.RankDescent` (the "rank descent" / Roth-machinery heart of Schmidt's
theorem) by

    Submission.Subspace.subspaceTheoremSubspaces_of_rankDescent
    = subspaces_of_rankDescent ∘ Stage2Assembly.stage2Output

so the only remaining gap in the whole development is `RankDescent` itself.
-/

namespace Submission

theorem schmidt_subspace (σ : Type*) [Fintype σ] (hσ : 2 ≤ Fintype.card σ)
    (L : σ → σ → ℂ)
    (alg : ∀ i j, IsAlgebraic ℚ (L i j)) (ind : LinearIndependent ℂ L)
    (ε : ℝ) (pos : 0 < ε) :
    ∃ s : Finset (σ → ℤ), 0 ∉ s ∧ ∀ x : σ → ℤ,
      ‖∏ i, ∑ j, L i j * x j‖ < ‖x‖ ^ (-ε) → ∃ c ∈ s, ∑ i, c i * x i = 0 := by
  have hRD : Submission.Subspace.RankDescent (σ := σ) L := by
    classical
    refine Submission.Subspace.rankDescent_of_rankDescentReal_algebraic L alg ind ?_
    intro M hMalg hMdet
    exact Submission.Subspace.RealRank.rankDescentReal_of_card_ge_two hσ M hMdet hMalg
  exact Submission.Subspace.normals_imp_challenge σ hσ L
    (Submission.Subspace.subspaces_imp_normals σ L
      (Submission.Subspace.subspaceTheoremSubspaces_of_rankDescent hσ L alg ind hRD)) ε pos

end Submission
