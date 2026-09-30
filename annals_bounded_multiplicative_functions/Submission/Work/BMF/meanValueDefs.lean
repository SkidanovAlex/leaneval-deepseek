import Mathlib
import Submission.Vinogradov.Orthogonality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the mean-value identity `Work.BMF.meanValue_eq_J`

Shared vocabulary for the proof that the `2s`-th mean value of the Weyl sum
`Σ_{h ≤ X} e(α₁ h + ⋯ + α_k h^k)` over the unit cube equals `J_{s,k}(X)`: the cube Weyl sum
`weylCube`, the moment monomial families `mom` / `wmom`, and the two torus Weyl sums
`weylTor` (`Σ_h ∏_{j<m} fourier (h^{j+1}) θ_j`) and `weylTor0` (`Σ_h ∏_{j<m} fourier (h^j) θ_j`,
i.e. with the degree-`0` coordinate included).

The relation proved in `Work.BMF.meanValue_eq_J` is
`ExpSum s k X θ = (weylTor0 (k+1) X θ)^s`, `weylTor0 (k+1) X θ = fourier 1 (θ 0) * weylTor k X (θ ∘ succ)`
and `weylTor m X (fun i => (x i : UnitAddCircle)) = weylCube m X x`.
-/

namespace Work.BMF

open scoped BigOperators

/-- The Weyl sum `Σ_{1 ≤ h ≤ X} e(α₁ h + ⋯ + α_k h^k)` on the unit cube. -/
noncomputable def weylCube (k X : ℕ) (α : Fin k → ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 X,
    Complex.exp (((2 * Real.pi * (∑ j : Fin k, α j * (h:ℝ) ^ ((j:ℕ)+1)) : ℝ) : ℂ) * Complex.I)

/-- The moment monomials of degrees `0, 1, …, m-1`. -/
def mom (m : ℕ) (h : ℕ) : Fin m → ℤ := fun j => (h : ℤ) ^ (j : ℕ)

/-- The moment monomials of degrees `1, 2, …, m`. -/
def wmom (m : ℕ) (h : ℕ) : Fin m → ℤ := fun j => (h : ℤ) ^ ((j : ℕ) + 1)

/-- The torus Weyl sum `Σ_{1 ≤ h ≤ X} ∏_{j<m} fourier (h^{j+1}) θ_j` with exponents `1,…,m`. -/
noncomputable def weylTor (m X : ℕ) (θ : UnitAddTorus (Fin m)) : ℂ :=
  ∑ h ∈ Finset.Icc 1 X, UnitAddTorus.mFourier (wmom m h) θ

/-- The torus Weyl sum `Σ_{1 ≤ h ≤ X} ∏_{j<m} fourier (h^j) θ_j` with exponents `0,…,m-1`. -/
noncomputable def weylTor0 (m X : ℕ) (θ : UnitAddTorus (Fin m)) : ℂ :=
  ∑ h ∈ Finset.Icc 1 X, UnitAddTorus.mFourier (mom m h) θ

end Work.BMF
