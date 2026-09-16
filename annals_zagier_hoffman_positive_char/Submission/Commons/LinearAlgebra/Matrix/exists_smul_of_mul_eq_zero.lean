import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Matrix

/-- Let `K` be a field, `ℓ ≥ 2`, `ϑ : Matrix (Fin ℓ) (Fin (ℓ-1)) K` with `K`-linearly independent
columns, and `ρ ≠ 0` a row vector with `Matrix.vecMul ρ ϑ = 0`.  Then every row vector `x` with
`Matrix.vecMul x ϑ = 0` is a scalar multiple of `ρ`. -/
theorem exists_smul_of_mul_eq_zero {K : Type*} [Field K] {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) K}
    (hind : LinearIndependent K (fun i : Fin (ℓ - 1) => fun j : Fin ℓ => ϑ j i))
    {ρ x : Fin ℓ → K} (hρ : Matrix.vecMul ρ ϑ = 0) (hρ0 : ρ ≠ 0)
    (hx : Matrix.vecMul x ϑ = 0) :
    ∃ a : K, x = a • ρ := by
  classical
  -- The row map `ψ : K^ℓ → K^(ℓ-1)`, `v ↦ v ᵥ ϑ`, i.e. multiplication by the transpose.
  set ψ : (Fin ℓ → K) →ₗ[K] (Fin (ℓ - 1) → K) := ϑ.transpose.mulVecLin with hψ
  have hψ_apply : ψ = ϑ.vecMulLinear := by
    rw [hψ, Matrix.mulVecLin_transpose]
  have hρψ : ψ ρ = 0 := by
    rw [hψ_apply, Matrix.vecMulLinear_apply]; exact hρ
  have hxψ : ψ x = 0 := by
    rw [hψ_apply, Matrix.vecMulLinear_apply]; exact hx
  -- The range of `ψ` (the row space of `ϑ`) has dimension `ℓ - 1`.
  have hcol : LinearIndependent K ϑ.col := by
    have h : ϑ.col = (fun i : Fin (ℓ - 1) => fun j : Fin ℓ => ϑ j i) := by
      funext i j; rw [Matrix.col_apply]
    rw [h]; exact hind
  have hrange : Module.finrank K (LinearMap.range ψ) = ℓ - 1 := by
    rw [hψ, Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
    rw [Matrix.rank_transpose, Matrix.rank_eq_finrank_span_cols]
    rw [finrank_span_eq_card hcol, Fintype.card_fin]
  -- Hence the kernel is one-dimensional.
  have hker : Module.finrank K (LinearMap.ker ψ) = 1 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker ψ
    have hV : Module.finrank K (Fin ℓ → K) = ℓ := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hV, hrange] at hdim
    omega
  -- `ρ` spans the kernel, since it is a nonzero element of it.
  have hρmem : ρ ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]; exact hρψ
  have hle : Submodule.span K {ρ} ≤ LinearMap.ker ψ :=
    Submodule.span_le.mpr (by rwa [Set.singleton_subset_iff])
  have hsing : Module.finrank K (Submodule.span K {ρ}) = 1 := finrank_span_singleton hρ0
  have heq : Submodule.span K {ρ} = LinearMap.ker ψ :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hsing, hker])
  have hxmem : x ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]; exact hxψ
  have hxspan : x ∈ Submodule.span K {ρ} := by
    rw [heq]; exact hxmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxspan
  exact ⟨a, ha.symm⟩

end Commons.LinearAlgebra.Matrix