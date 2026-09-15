import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Bounding a continuous multilinear map by its values on the standard basis

For a continuous `𝕜`-multilinear map `T` on `m` copies of `ι → 𝕜` (with `ι` finite and
`𝕜` a `RCLike` field, so the norm on `ι → 𝕜` is the supremum norm), the operator norm of
`T` is bounded by the sum of the norms of its values on the tuples of standard basis
vectors `Pi.single (I j) 1`.

The proof expands an arbitrary tuple `x` in the standard basis of `ι → 𝕜` and uses
`ContinuousMultilinearMap.map_sum` together with `ContinuousMultilinearMap.map_smul_univ`.
-/

open scoped BigOperators

namespace Commons.Analysis.Calculus.Multilinear

theorem norm_le_sum_apply_basis {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] (m : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin m => (ι → 𝕜)) G) :
    ‖T‖ ≤ ∑ I : Fin m → ι, ‖T (fun j => Pi.single (I j) (1 : 𝕜))‖ := by
  classical
  refine T.opNorm_le_bound (Finset.sum_nonneg fun I _ => norm_nonneg _) fun x => ?_
  -- Expand each coordinate of `x` in the standard basis of `ι → 𝕜`.
  have hx : (fun j : Fin m => ∑ i : ι, (Pi.single i (x j i) : ι → 𝕜)) = x := by
    funext j
    exact LinearMap.sum_single_apply (fun _ : ι => 𝕜) (x j)
  -- Multilinear expansion of `T x` over all choices of a basis vector in each coordinate.
  have hTx : T x = ∑ r : Fin m → ι, T (fun j => Pi.single (r j) (x j (r j))) := by
    conv_lhs => rw [← hx]
    rw [ContinuousMultilinearMap.map_sum (α := fun _ : Fin m => ι)
          (g := fun j i => (Pi.single i (x j i) : ι → 𝕜))]
  -- Factor the scalar coefficient out of each summand.
  have hterm : ∀ r : Fin m → ι,
      ‖T (fun j => Pi.single (r j) (x j (r j)))‖
        = (∏ j, ‖x j (r j)‖) * ‖T (fun j => Pi.single (r j) (1 : 𝕜))‖ := by
    intro r
    have hsmul : (fun j => Pi.single (r j) (x j (r j)) : Fin m → (ι → 𝕜))
        = fun j => (x j (r j)) • (Pi.single (r j) (1 : 𝕜) : ι → 𝕜) := by
      funext j
      conv_lhs => rw [show x j (r j) = (x j (r j)) • (1 : 𝕜) by rw [smul_eq_mul, mul_one]]
      rw [Pi.single_smul]
    rw [hsmul, ContinuousMultilinearMap.map_smul_univ, norm_smul, norm_prod]
  calc ‖T x‖
      = ‖∑ r : Fin m → ι, T (fun j => Pi.single (r j) (x j (r j)))‖ := by rw [hTx]
    _ ≤ ∑ r : Fin m → ι, ‖T (fun j => Pi.single (r j) (x j (r j)))‖ := norm_sum_le _ _
    _ ≤ ∑ r : Fin m → ι, (∏ j, ‖x j‖) * ‖T (fun j => Pi.single (r j) (1 : 𝕜))‖ := by
          apply Finset.sum_le_sum
          intro r _
          rw [hterm r]
          apply mul_le_mul_of_nonneg_right
          · exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
              (fun j _ => norm_le_pi_norm (x j) (r j))
          · exact norm_nonneg _
    _ = (∑ r : Fin m → ι, ‖T (fun j => Pi.single (r j) (1 : 𝕜))‖) * ∏ j, ‖x j‖ := by
          rw [← Finset.mul_sum, mul_comm]

end Commons.Analysis.Calculus.Multilinear