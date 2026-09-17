import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.TensorProduct

/-- Over a field, the pure tensor `a ⊗ₜ b` is non-zero as soon as both factors are. -/
theorem tmul_ne_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {a : M} {b : N} (ha : a ≠ 0) (hb : b ≠ 0) :
    a ⊗ₜ[K] b ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K ha
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one K hb
  intro h
  have key : (TensorProduct.lid K K) (TensorProduct.map f g (a ⊗ₜ[K] b)) = 1 := by
    rw [TensorProduct.map_tmul, hf, hg, TensorProduct.lid_tmul]
    simp
  rw [h, map_zero, map_zero] at key
  exact one_ne_zero key.symm

end Commons.LinearAlgebra.TensorProduct