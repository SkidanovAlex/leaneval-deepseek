import Mathlib
import Submission.Work.WilG4c.c1RealFD

namespace Work.WilG4c

/-- `HasFDerivAt φ L x`, for `φ : ℝ^N → ℝ` and `L` a continuous linear functional, is
equivalently tested by the *polynomial* (`ℓ²`, squared) `ε`-`δ` condition

`∑ i, (y i - x i)^2 < δ^2  →  (φ y - φ x - L (y - x))^2 ≤ ε^2 · ∑ i, (y i - x i)^2`.

Indeed, every `L : (Fin N → ℝ) →L[ℝ] ℝ` is `linMap c` for its coefficient vector
`c = linCoeff L` (`linMap_linCoeff`), and the `ℓ²`-`ε`-`δ` predicate `HasFDerivEps φ x c`
(which is exactly the displayed condition, since `∑ i, c i * (y i - x i) = L (y - x)`) is the
same as `HasFDerivAt φ (linMap c) x` (`c1RealFD`): the sup-norm balls and the `ℓ²` balls
generate the same filter on `Fin N → ℝ`, with the two elementary norm comparisons
`‖z‖² ≤ ∑ i, z i²` and `∑ i, z i² ≤ max N 1 · ‖z‖²`. -/
theorem hasFDerivAt_iff_epsPoly {N : ℕ} (φ : (Fin N → ℝ) → ℝ)
    (L : (Fin N → ℝ) →L[ℝ] ℝ) (x : Fin N → ℝ) :
    HasFDerivAt φ L x ↔
      ∀ ε > 0, ∃ δ > 0, ∀ y : Fin N → ℝ,
        (∑ i, (y i - x i) ^ 2 < δ ^ 2) →
        (φ y - φ x - L (y - x)) ^ 2 ≤ ε ^ 2 * ∑ i, (y i - x i) ^ 2 := by
  -- `L` is `linMap` of its coefficient vector.
  have hL : ∀ y : Fin N → ℝ, (∑ i : Fin N, linCoeff L i * (y i - x i)) = L (y - x) := by
    intro y
    have h1 : L (y - x) = linMap (linCoeff L) (y - x) := by rw [linMap_linCoeff]
    rw [h1]
    simp only [linMap_apply, Pi.sub_apply]
  -- `c1RealFD` identifies the `ℓ²`-predicate `HasFDerivEps` with `HasFDerivAt` for `linMap c`.
  have h := c1RealFD (g := φ) (y := x) (c := linCoeff L)
  rw [linMap_linCoeff] at h
  rw [← h]
  constructor
  · intro hE ε hε
    obtain ⟨δ, hδ, hδp⟩ := hE ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    simpa only [← hL y] using hδp y hy
  · intro hP ε hε
    obtain ⟨δ, hδ, hδp⟩ := hP ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    simpa only [← hL y] using hδp y hy

end Work.WilG4c
