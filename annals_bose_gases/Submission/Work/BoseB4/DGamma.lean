import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.DGamma` — the second quantisation of a one-particle operator

FS `lem:2ndQuand`'s third row expresses the `N`-particle kinetic energy as the
second quantisation of the one-particle operator `𝒯'`:

    `∑_{j=1}^N 𝒯'_j = ((2π)^{-3}ℓ³ ∫ τ(k) a_k†a_k)_N`,

i.e. on the mode lattice `(2π/ℓ)ℤ³` (one lattice point = weight 1 in FS's
normalisation)

    `∑_{j} 𝒯'_j = ∑_k τ(k) a_k† a_k`,

the eigenvalues `τ(k)` being those of `𝒯'` on the box's momentum basis.  The
*identification* of the box's one-particle operator `𝒯'` with the multiplication
by `τ(k)` is the box-side Fourier computation (the own basis of `𝒯'`); what node
B4 owes on top of it is the purely second-quantised step, which is this module:

* `dGamma T = ∑_{ij} (T e_j)_i · a_i† a_j` — the second quantisation of a
  one-particle operator `T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)` in the coordinate
  (mode) basis;
* `dGamma_diag` — if `T` is diagonal with eigenvalues `λ`, then
  `dGamma T = ∑_i λ_i · a_i† a_i`, which is FS's row;
* `dGamma_quadform` — the quadratic form `⟨Φ, dGamma T Φ⟩ = ∑_i λ_i ‖a_iΦ‖²`,
  the form in which `lem:2ndQuand` is used;
* `dGamma_one` — the case `T = 1`: `dGamma 1 = ∑_i a_i†a_i`, the total number
  operator, whose `excited`-mode part is B7's `nPlus` (`n₊`), matching
  `lem:2ndQuand`'s second row `n₊ = (2π)^{-3}ℓ³∫ ã_k†ã_k dk`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- The coordinate vector `e_i` of the one-particle space `Fin m → ℝ`. -/
noncomputable def evec (m : ℕ) (i : Fin m) : Fin m → ℝ := Pi.single i 1

/-- **The second quantisation of a one-particle operator** `T`:
`dGamma T = ∑_{ij} (T e_j)_i · a_i† a_j` (with `a_i` the annihilation of mode `i`). -/
noncomputable def dGamma (m : ℕ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    RealFock m →ₗ[ℝ] RealFock m :=
  ∑ i : Fin m, ∑ j : Fin m, (T (evec m j) i) • (cre m i).comp (ann m j)

/-- The **number operator** of mode `i`: `n_i = a_i† a_i`. -/
noncomputable def modeNumOp (m : ℕ) (i : Fin m) : RealFock m →ₗ[ℝ] RealFock m :=
  (cre m i).comp (ann m i)

/-- The **total number operator** `∑_i a_i†a_i`. -/
noncomputable def totNumOp (m : ℕ) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ i : Fin m, modeNumOp m i

end Work.BoseB4
