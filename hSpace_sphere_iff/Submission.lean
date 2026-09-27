/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Adams: `Sⁿ` is an H-space iff `n = 0, 1, 3, 7`

`hSpace_sphere_iff` is Adams' Hopf-invariant-one theorem in its H-space form, stated against
Mathlib's `HSpace` class (Serre's strictly pointed notion: a continuous multiplication `⋀` with a
point `e` such that `e ⋀ e = e` and the two unit laws hold up to homotopy relative to `{e}`).

The **reverse direction** is complete and unconditional (see `Submission/Assembly.lean`): for
`n = 0, 1, 3, 7` the sphere `Sⁿ` is the unit sphere of the normed (division) algebra `ℝ`, `ℂ`,
`ℍ` or `𝕆`, where the product has strictly multiplicative norm and strict two-sided unit; the
resulting H-space structure on the unit sphere is transported along a linear isometry equivalence
to the Euclidean sphere `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`.
Mathlib has no octonions, so `n = 7` requires building the Cayley–Dickson double of the
quaternions: see `Submission/Work/Octonion/` (norm multiplicativity, strict unit laws,
continuity, and the isometry with `ℝ⁸`).

The **forward direction** is Adams' theorem.  Its even-dimensional part is the classical cup
product argument: an H-space structure `μ` on `X` makes `μ^*` a ring homomorphism of cohomology
rings, `H^*(X) → H^*(X) ⊗ H^*(X)`, with `μ^*(x) = x ⊗ 1 + 1 ⊗ x`, so for `X = Sⁿ`
(`n > 0` even) `0 = μ^*(x²) = (μ^*x)² = 2 (x ⊗ x)`, contradicting `x ⊗ x ≠ 0` over a coefficient
ring with `2 ≠ 0`.  The odd-dimensional part is the full Hopf-invariant-one non-existence of
Adams (equivalently Adams–Atiyah's K-theoretic argument with the `ψ²`, `ψ³` operations).

Neither is available in the current Mathlib, so both are built here: the even case in
`Submission/Work/Sphere/`, the odd case in `Submission/Work/KT/` (`K₀` of commutative `ℂ`-algebras,
Bott periodicity for `C(X × S², ℂ)`, `K̃(Sⁿ)`, the Adams operations `ψ²`, `ψ³`, the Hopf construction
and the Adams–Atiyah divisibility `2^m ∣ 3^m - 1`); see `Work.KT.hSpace_odd_case`.
-/
import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Assembly
import Submission.Work.Sphere.EvenCase
import Submission.Work.KT.OddCase

namespace Submission

/-- **Adams' Hopf-invariant-one theorem** (H-space form). The sphere `𝕊ⁿ` admits an H-space
structure if and only if `n = 0`, `1`, `3`, or `7`. -/
theorem hSpace_sphere_iff (n : ℕ) :
    Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ↔
      n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7 := by
  constructor
  · -- Adams' theorem.  The **even** case is complete (`Submission.Sphere.not_hSpace_sphere_even`):
    -- for even `n ≥ 2` the sphere `Sⁿ` is not an H-space, by the cup-product argument on
    -- `H^*(Sⁿ × Sⁿ; ℚ)`.  The **odd** case (`n > 1` odd, `n ∉ {3,7}`) is Adams'
    -- Hopf-invariant-one theorem in its K-theoretic form (the Adams operations `ψ²`, `ψ³`),
    -- `Work.KT.hSpace_odd_case`.
    intro h
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k, hk⟩ := he
      subst hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exact Or.inl (by omega)
      · have hn2 : 2 ≤ k + k := by omega
        exact absurd h
          (Submission.Sphere.not_hSpace_sphere_even_uncond (k + k) hn2 ⟨k, rfl⟩)
    · -- odd `n`: Adams' Hopf-invariant-one theorem via K-theory (Adams operations `ψ²`, `ψ³`).
      exact Work.KT.hSpace_odd_case n ho h
  · -- The reverse direction, complete: see `Submission.hSpace_sphere_of_mem`.
    exact hSpace_sphere_of_mem n

end Submission
