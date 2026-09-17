import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open scoped TensorProduct

namespace Commons.LinearAlgebra.TensorProduct

/-- Over a field, if `a : ι → M` is a linearly independent family and `∑ i, a i ⊗ₜ[R] b i = 0` in
`M ⊗[R] N`, then every `b i` vanishes: apply the dual functionals of the `a i`.
(The `CommRing` version is false -- `ℤ`-example: `3 ⊗ₜ (1 : ZMod 3) = 0`.) -/
theorem linearIndependent_tmul_sum {R M N ι : Type*} [Field R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Fintype ι] {a : ι → M} (ha : LinearIndependent R a)
    (b : ι → N) (h : ∑ i, a i ⊗ₜ[R] b i = 0) : ∀ i, b i = 0 := by
  classical
  intro j
  -- `a j` is not in the span of the other vectors, so a functional separates it.
  have hj : a j ∉ Submodule.span R (a '' {j}ᶜ) := ha.notMem_span j
  obtain ⟨f, hfj, hfmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (R := R) hj (by infer_instance)
  -- normalize so that `f' (a j) = 1`
  set f' : M →ₗ[R] R := (f (a j))⁻¹ • f with hf'_def
  have hf'j : f' (a j) = 1 := by
    rw [hf'_def, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfj]
  have hf'i : ∀ i, i ≠ j → f' (a i) = 0 := by
    intro i hij
    have hi : a i ∈ Submodule.span R (a '' {j}ᶜ) :=
      Submodule.subset_span (Set.mem_image_of_mem a (by simpa using hij))
    have hmem : f (a i) ∈ (Submodule.span R (a '' {j}ᶜ)).map f := Submodule.mem_map_of_mem hi
    rw [hfmap, Submodule.mem_bot] at hmem
    rw [hf'_def, LinearMap.smul_apply, hmem, smul_zero]
  -- apply `f' ⊗ id` followed by the canonical identification `R ⊗ N ≃ N`
  let g : M ⊗[R] N →ₗ[R] N := (TensorProduct.lid R N).toLinearMap.comp (f'.rTensor N)
  have hg : ∀ i, g (a i ⊗ₜ[R] b i) = f' (a i) • b i := by
    intro i
    simp [g, TensorProduct.lid_tmul]
  have key : g (∑ i, a i ⊗ₜ[R] b i) = b j := by
    rw [map_sum]
    simp only [hg]
    rw [Finset.sum_eq_single j]
    · simp [hf'j]
    · intro i _ hij; simp [hf'i i hij]
    · intro hj'; exact absurd (Finset.mem_univ j) hj'
  rw [h, map_zero] at key
  exact key.symm

end Commons.LinearAlgebra.TensorProduct