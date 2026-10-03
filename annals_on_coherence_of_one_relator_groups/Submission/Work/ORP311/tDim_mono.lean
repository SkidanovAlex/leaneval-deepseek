/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: ORP311 area (monotonicity of the transversal dimension)

# Monotonicity of the transversal dimension

The transversal dimension (`Work.ORP311.tDim`) of a subspace
`M ⊆ ⊕_{i : Fin n} ℓ²(G)` is the sum of the squared norms of the projections of the
coordinate vectors `e_i ⊗ δ_g` (`g ∈ s`) onto `M`:

  `tDim n s M = ∑ g ∈ s, ∑ i : Fin n, ‖M.starProjection (hinclude n i (δ_g))‖ ^ 2`.

It is monotone in the subspace: if `M ≤ N` then `tDim n s M ≤ tDim n s N`.  The pointwise
input is the monotonicity of the norm of the orthogonal projection, `‖P_M x‖ ≤ ‖P_N x‖` for
`M ≤ N`, which holds because `P_M ∘ P_N = P_M` (`Submodule.orthogonalProjectionOnto_starProjection_of_le`)
and `P_M` is norm-non-increasing (`Submodule.norm_starProjection_apply_le`).
-/
import Mathlib
import Submission.Work.ORP311.LuckDim

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

/-- **Monotonicity of the norm of the orthogonal projection.**

If `M ≤ N` then `P_M ∘ P_N = P_M`, i.e. `P_M (P_N x) = P_M x`, because `P_M x ∈ M ≤ N` and
`P_N` fixes `N`.  Since the orthogonal projection is norm-non-increasing,
`‖P_M x‖ = ‖P_M (P_N x)‖ ≤ ‖P_N x‖`. -/
theorem norm_starProjection_mono {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {M N : Submodule 𝕜 E} [M.HasOrthogonalProjection]
    [N.HasOrthogonalProjection] (h : M ≤ N) (x : E) :
    ‖M.starProjection x‖ ≤ ‖N.starProjection x‖ := by
  have h1 : M.starProjection (N.starProjection x) = M.starProjection x := by
    simpa only [Submodule.starProjection_apply] using
      congrArg Subtype.val (Submodule.orthogonalProjectionOnto_starProjection_of_le h x)
  rw [← h1]
  exact M.norm_starProjection_apply_le _

/-- **Monotonicity of the transversal dimension**: `tDim n s M ≤ tDim n s N` for `M ≤ N`.

Termwise consequence of `norm_starProjection_mono` applied to each `hinclude n i (δ_g)`. -/
theorem tDim_mono {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (s : Finset G) {M N : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)} [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] (h : M ≤ N) : Work.ORP311.tDim (G := G) n s M ≤ Work.ORP311.tDim (G := G) n s N := by
  rw [tDim_apply, tDim_apply]
  refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_starProjection_mono h _) 2

end Work.ORP311
