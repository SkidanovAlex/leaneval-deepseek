/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Setup for Milne's Lemma 3.2 (descent from `ℝ` to `ℚ`)

Milne, *Class Field Theory*, Lemma 3.2 (as used in Lemmas 3.4–3.5): if two finite-dimensional
`ℚ[G]`-modules become isomorphic after extending scalars to `ℝ`, they are already isomorphic over
`ℚ`.  In the matrix form used for Milne's Proposition 3.1 (the `S`-unit computation) the content is

> a system of linear equations with **rational** coefficients, which has an **invertible real**
> solution, has an **invertible rational** solution.

The elementary core is `ker_baseChange_eq` below: the real solutions of a rational homogeneous
linear system are the real linear combinations of its rational solutions.  The main descent
statement is `NK.GlobalCFTdeep.exists_det_ne_zero_of_map_solution`
(`Herbrand/Descent/exists_det_ne_zero_of_map_solution.lean`).

## Main results

* `NK.GlobalCFTdeep.ker_baseChange_eq`: `ker (f.baseChange ℝ) = (ker f).baseChange ℝ` for a
  `ℚ`-linear map `f`.
-/

set_option autoImplicit false

noncomputable section

namespace NK.GlobalCFTdeep

/-- **Base change of the kernel.** For a `ℚ`-linear map `f`, the kernel of its scalar extension to
`ℝ` is the `ℝ`-span of the kernel of `f`: the kernel of a rational homogeneous linear system base
changes.  This is the elementary core of Milne, *CFT*, Lemma 3.2. -/
theorem ker_baseChange_eq {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N]
    [Module ℚ N] (f : M →ₗ[ℚ] N) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker,
      show (TensorProduct.mk ℚ ℝ M) 1 y = (1 : ℝ) ⊗ₜ[ℚ] y from rfl,
      LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hy, TensorProduct.tmul_zero]
  · have h2 := Module.Flat.lTensor_exact ℝ (LinearMap.exact_subtype_ker_map f)
    rw [LinearMap.exact_iff] at h2
    intro x hx
    have hx' : x ∈ (LinearMap.ker (LinearMap.lTensor ℝ f) : Set _) := hx
    rw [h2] at hx'
    exact hx'

end NK.GlobalCFTdeep
