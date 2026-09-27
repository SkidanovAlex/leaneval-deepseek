import Mathlib

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-- **The derivative of a flow at time `0` in the space direction is the identity.**

If `Φ : ℝ × M → M` is smooth and `Φ (0, x) = x` for all `x` (e.g. `Φ` is the flow of a vector
field, evaluated at time `t`), then the total derivative of `Φ` at `(0, x)`, applied to a purely
spatial tangent vector `(0, v)` (zero time component), returns `v`.

This is the statement that the time-`0` slice of the flow is the identity, together with the fact
that the total derivative in two variables splits as the sum of the two partial derivatives
(`mfderiv_prod_eq_add_apply`). -/
theorem mfderiv_flow_zero_snd {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (Φ : ℝ × M → M) (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (h0 : ∀ x : M, Φ (0, x) = x) (x : M) (v : TangentSpace (𝓡 2) x) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) Φ (0, x) ((0 : ℝ), v) = v := by
  -- Smoothness gives differentiability at `(0, x)`.
  have hmd : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) Φ (0, x) :=
    hΦ.contMDiffAt.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  -- The tangent vector `(0, v)`, packaged as a `let` so that its product structure is visible to
  -- the elaborator (`TangentSpace` is deliberately irreducible, see `TangentSpace` in Mathlib).
  let w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) ((0 : ℝ), x) := ((0 : ℝ), v)
  -- The total derivative in two variables is the sum of the two partial derivatives.
  have h := mfderiv_prod_eq_add_apply (f := Φ) (p := ((0 : ℝ), x)) (v := w) hmd
  refine h.trans ?_
  -- Unfold `w` (and with it its two components `w.1 = 0`, `w.2 = v`).
  simp only [w]
  -- The derivative in the *time* direction is a continuous linear map on `ℝ`, so it kills `0`.
  have h1 : (mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) (fun z : ℝ => Φ (z, x)) 0) (0 : ℝ) = 0 := map_zero _
  rw [h1, zero_add]
  -- The time-`0` slice of the flow is the identity, so its derivative is the identity.
  have h2 : (fun z : M => Φ (0, z)) = id := funext h0
  rw [mfderiv_congr h2, mfderiv_id]
  rfl

end Work.Drive.N2
