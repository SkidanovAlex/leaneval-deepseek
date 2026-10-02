import Mathlib
import Submission.Work.ThomBordism.PontryaginThom.Geometry
import Submission.Work.ThomBordism.PontryaginThom.Pad

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

Mathlib has `exists_embedding_euclidean_of_compact` (Mathlib/Geometry/Manifold/WhitneyEmbedding.lean): for a
compact T2 C^∞ manifold there are n and e : M → EuclideanSpace ℝ (Fin n) with CMDiff ∞ e, IsClosedEmbedding e,
and injective mfderiv everywhere — exactly the fields of EmbeddingData V n (Geometry.lean). Man8 is compact,
T2, C^∞ over 𝓡 8. Then pad the target to 8 + k for any k ≥ max k₀ (n − 8) by composing with the linear
isometric inclusion ℝⁿ → ℝ^{8+k} (Submission/Work/ThomBordism/PontryaginThom/Pad.lean has padCLM and the
padding lemmas for immersions; a linear isometric embedding preserves smoothness, closed embedding and
injectivity of mfderiv). This removes the need for Whitney's immersion BOUND (ImmersionBound) in the
Pontryagin–Thom chapter: the codimension is chosen per finite family.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Function Topology
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

/-- **Embedding data in a prescribed codimension**: for every closed oriented smooth `8`-manifold `V`
and every lower bound `k₀` on the codimension, there is `k ≥ k₀` with an embedding of `V` into
`ℝ^{8+k}` (closed, `C^∞`, injective derivative).

This is Mathlib's Whitney embedding theorem (`exists_embedding_man8`), which yields an embedding into
`ℝⁿ` for some `n`, composed with the zero padding `ℝⁿ ↪ ℝ^{8+k}` of `Pad.lean` for
`k = max k₀ (n - 8) ≥ n - 8`.  Padding preserves smoothness, being a closed embedding and the
injectivity of the derivative (`EmbeddingData.pad`). -/
theorem embeddingData_exists (V : Work.ThomBordism.Man8) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ Nonempty (Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) := by
  obtain ⟨n, ⟨E⟩⟩ := embeddingData_of_mathlib V
  refine ⟨max k₀ (n - 8), le_max_left _ _, ?_⟩
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ 8 + max k₀ (n - 8))
  rw [ht]
  exact ⟨E.pad t⟩

end

end Work.ThomBordism.PontryaginThom
