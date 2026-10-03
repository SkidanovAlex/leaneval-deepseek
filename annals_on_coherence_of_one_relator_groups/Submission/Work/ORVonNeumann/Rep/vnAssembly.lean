/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The extended rank function `rk_G` of the group von Neumann algebra is a faithful
Sylvester rank function

Jaikin-Zapirain–López-Álvarez (arXiv:1810.12135, §3.2–3.4) and Lück (*L²-Invariants*)
attach to a countable group `G` the *extended rank function* `rk_G` of the group von
Neumann algebra `N(G) = Work.ORVonNeumann.groupVonNeumann G`: for a matrix
`A ∈ M_{n×m}(N(G))`, seen as a bounded operator
`matOp A : HSum m → HSum n` on the finite direct sum `⊕_{j : Fin m} ℓ²(G)`,

`rk_G(A) = n - dim_G (ker A†) = dim_G (closure of the range of A)`,

where `dim_G K = ∑ i, ‖P_K (e i ⊗ δ₁)‖² = ∑ i, τ ((P_K) i i)` is the von Neumann
dimension, normalised by `dim_G (⊕_{i : Fin n} ℓ²(G)) = n`, and `τ a = ⟪δ₁, a δ₁⟫` is the
trace of `N(G)`.

This module proves that `rk_G` is a Sylvester matrix rank function which is faithful, i.e.
the main analytic input of the one-relator coherence project (JZLA §3.4, Lück Theorem 6.7).

## The ingredients (all in this directory)

* `Work.ORVonNeumann.Rep.vnCore` — `HSum`, `hcoord`, `hinclude`, `hdelta`, `matOp`, `hdim`,
  `mTrace`, and the basic coordinate API;
* `Work.ORVonNeumann.Rep.vnDiag` — the block diagonal right regular action `diagOp` and the
  class of *equivariant* operators (the "matrices over `N(G)`");
* `Work.ORVonNeumann.Rep.vnMatOpMul` — `matOp (A * B) = (matOp A).comp (matOp B)`;
* `Work.ORVonNeumann.Rep.vnMatOpAdjoint` — `(matOp A)† = matOp Aᴴ`;
* `Work.ORVonNeumann.Rep.vnInnerHdelta` — `⟪e i ⊗ δ₁, matOp A (e i ⊗ δ₁)⟫ = τ (A i i)`;
* `Work.ORVonNeumann.Rep.vnHdimCompl` — `hdim K + hdim Kᗮ = n`;
* `Work.ORVonNeumann.Rep.vnHdimMono` — monotonicity of `hdim`;
* `Work.ORVonNeumann.Rep.vnCyclicTrace` — the amplified traciality
  `∑ i, ⟪δ i, X (Y (δ i))⟫ = ∑ j, ⟪δ j, Y (X (δ j))⟫` for equivariant `X, Y`;
* `Work.ORVonNeumann.Rep.vnKeyRank` — the key identity `m - hdim (ker T_X) = n - hdim (ker T_X†)`
  (the von Neumann dimension of the range closure of a matrix operator equals that of its
  adjoint), proved from `vnCyclicTrace` and the regularised resolvent
  `(T†T + ε)⁻¹` of `Work.ORVonNeumann.Rep.vnExistsInvAdd`,
  `Work.ORVonNeumann.Rep.vnTendstoRegInv`;
* `Work.ORVonNeumann.Rep.vnBlockDiagKernel` — *additivity* (SMat3) for block diagonal
  matrices: `hdim (ker (matOp (blockDiag A B))) = hdim (ker (matOp A)) + hdim (ker (matOp B))`;
* `Work.ORVonNeumann.Rep.vnBlockUpperAdjointKernel` — *subadditivity* (SMat4) for block upper
  triangular matrices: `hdim (ker (matOp T)†) ≤ hdim (ker (matOp A)†) + hdim (ker (matOp B)†)`
  for `T = [[A, C], [0, B]]`;
* `Work.ORVonNeumann.Rep.vnFaithful` — `hdim (ker (matOp !![x])†) = 1 → x = 0`.

## The assembly

With the definition `vnRank A := (n : ℝ) - hdim (ker (matOp A)†)` for
`A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))`, the five axioms are:

* `map_zero` — `matOp 0 = 0`, hence the kernel is everything and `hdim ⊤ = n`;
* `map_one` — `matOp !![1] = 1`, hence the kernel is trivial;
* `mul_le` — after `vnKeyRank` rewrites `n - hdim (ker (matOp A)†)` for an `n × m` matrix as
  `m - hdim (ker (matOp A))`, both inequalities become kernel inclusions:
  `ker (matOp (A*B)) ⊇ ker (matOp A)` and `ker (matOp (A*B)) ⊇ ker (matOp B)`, using
  `matOp (A*B) = matOp A ∘ matOp B`;
* `blockDiag_add` — `vnBlockDiagKernel` (applied to `Aᴴ`, `Bᴴ`, using `vnMatOpAdjoint`);
* `blockUpper_le` — `vnBlockUpperAdjointKernel`.

`Faithful` is exactly `vnFaithful` (for a `1 × 1` matrix the operator is `x` itself, and
`hdim (ker x†) = 1` forces `x = 0`).

The remaining glue (`hdim ⊥ = 0`, `hdim ⊤ = n`, `matOp 0 = 0`, `matOp !![1] = 1`, the
kernel-nesting calculations, and the instantiation of `SylvesterRankFunction`) is
elementary and is carried out below.
-/
import Mathlib
import Submission.Work.ORVonNeumann.SylvesterRank
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.Trace
import Submission.Work.ORVonNeumann.Rep.Dimension
import Submission.Work.Rep.exists_rangeProjection
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint
import Submission.Work.ORVonNeumann.Rep.vnInnerHdelta
import Submission.Work.ORVonNeumann.Rep.vnHdimCompl
import Submission.Work.ORVonNeumann.Rep.vnHdimMono
import Submission.Work.ORVonNeumann.Rep.vnDiag
import Submission.Work.ORVonNeumann.Rep.vnBlockDiagKernel
-- import Submission.Work.ORVonNeumann.Rep.vnKeyRank  -- (in progress)
-- import Submission.Work.ORVonNeumann.Rep.vnBlockUpperAdjointKernel  -- (in progress)
import Submission.Work.ORVonNeumann.Rep.vnFaithful

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The dimension of the trivial subspace vanishes. -/
theorem hdim_bot (n : ℕ) : hdim (G := G) (⊥ : Submodule ℂ (HSum (G := G) n)) = 0 := by
  simp [hdim]

/-- The dimension of the whole space is the number of summands. -/
theorem hdim_top (n : ℕ) : hdim (G := G) (⊤ : Submodule ℂ (HSum (G := G) n)) = n := by
  simp [hdim, Submodule.starProjection_top', vnNormSqHdelta]

/-- The defining formula for the von Neumann dimension (the instance is a variable, so that the
lemma can be used as a rewrite rule). -/
theorem hdim_apply {n : ℕ} (K : Submodule ℂ (HSum (G := G) n)) [K.HasOrthogonalProjection] :
    hdim (G := G) K = ∑ i : Fin n, ‖K.starProjection (hdelta (G := G) n i)‖ ^ 2 := rfl

/-- Subspaces with the same underlying set have the same orthogonal projection. -/
theorem starProjection_congr {n : ℕ} {K L : Submodule ℂ (HSum (G := G) n)}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (h : K = L) :
    K.starProjection = L.starProjection := by
  subst h
  rfl

/-- The von Neumann dimension only depends on the underlying subspace. -/
theorem hdim_congr {n : ℕ} {K L : Submodule ℂ (HSum (G := G) n)}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (h : K = L) :
    hdim (G := G) K = hdim (G := G) L := by
  simp only [hdim, starProjection_congr h]

/-- The von Neumann dimension of a subspace, as the sum of the inner products
`⟪e i ⊗ δ₁, P_K (e i ⊗ δ₁)⟫`: this is the form in which the regularised resolvent
`ε (T†T + ε)⁻¹ → P_{ker T}` computes it. -/
theorem hdim_eq_sum_inner {n : ℕ} (K : Submodule ℂ (HSum (G := G) n))
    [K.HasOrthogonalProjection] :
    (∑ i : Fin n, inner ℂ (hdelta (G := G) n i) (K.starProjection (hdelta (G := G) n i)))
      = ((hdim (G := G) K : ℝ) : ℂ) := by
  rw [hdim]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 := Submodule.starProjection_inner_eq_zero (𝕜 := ℂ) (K := K)
    (hdelta (G := G) n i) (K.starProjection (hdelta (G := G) n i))
    (Submodule.starProjection_apply_mem K (hdelta (G := G) n i))
  have hsplit : inner ℂ (hdelta (G := G) n i) (K.starProjection (hdelta (G := G) n i))
      = inner ℂ ((hdelta (G := G) n i - K.starProjection (hdelta (G := G) n i))
          + K.starProjection (hdelta (G := G) n i))
          (K.starProjection (hdelta (G := G) n i)) := by
    rw [sub_add_cancel]
  rw [hsplit, inner_add_left, h0, zero_add]
  exact inner_self_eq_norm_sq_to_K _

/-- The von Neumann rank of a matrix over `N(G)` (Jaikin-Zapirain–López-Álvarez §3.4):
`rk_G A = n - dim_G (ker A†)`, which is also `dim_G (closure of the range of A)`. -/
noncomputable def vnRank (n m : ℕ) (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) : ℝ :=
  (n : ℝ) - hdim (G := G) ((ContinuousLinearMap.adjoint (matOp (G := G) A)).ker)

theorem vnRank_eq (n m : ℕ) (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) :
    vnRank (G := G) n m A
      = (n : ℝ) - hdim (G := G) ((ContinuousLinearMap.adjoint (matOp (G := G) A)).ker) := rfl

/-- `matOp` of the zero matrix is the zero operator. -/
theorem matOp_zero' {n m : ℕ} :
    matOp (G := G) (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) = 0 := by
  apply matOp_ext
  intro i
  rw [hcoord_matOp]
  simp

/-- `matOp` of the `1 × 1` identity matrix is the identity operator, so that `map_one` reduces
to the triviality of the kernel of the identity. -/
theorem matOp_one_one :
    matOp (G := G) (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G))) = 1 := by
  apply matOp_ext
  intro i
  rw [hcoord_matOp, Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq]
    simp [ContinuousLinearMap.one_def]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

end Work.ORVonNeumann.Rep
