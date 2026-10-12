import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.RealFock` — the **real** bosonic Fock space over `m` modes

Node B4 must not only prove the `c`-number substitution, it must *inhabit*
node B7's Fock interface `Work.BoseB7.FockData` (`Submission/Work/BoseB7/FockDefs.lean`):
a mode system over `(2π/ℓ)ℤ³` with the box commutator
`[a_k, a_{k'}†] = χ̂²((k-k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)`, a Fock form `bp`, and `a† = a*`.
B7's interface is stated over **real** vector spaces, so this module builds the
real bosonic Fock space in its occupation-number (monomial-coefficient) model:

* `H m := (Fin m →₀ ℕ) →₀ ℝ` — the free `ℝ`-module on the multi-indices, i.e. the
  space of *finitely supported* polynomials `Σ_α p_α x^α` in `m` indeterminates;
* `ann m l = ∂/∂x_l` — annihilation of mode `l`, `(ann f) α = (α_l)·f(α−e_l)`;
* `cre m l = multiplication by x_l`, `(cre f) α = f(α−e_l)`;
* `bomb m` — the **Bombieri (Fock) form** `⟪p,q⟫ = Σ_α p_α q_α α!`, which makes
  the *normalised* monomials `x^α/√(α!)` an orthonormal basis; in particular
  `cre m l` is the `bomb`-adjoint of `ann m l`, i.e. `a_l† = (a_l)*`.

Both `ann` and `cre` are *defined* through `Finsupp.lsum`/`toSpanSingleton`, so the
linearity in the state is by construction; the content of the module is the
form's positivity/definiteness, its symmetry, the integration-by-parts
adjointness and the CCR — `Work.BoseB4.RealFockBomb`, `Work.BoseB4.RealFockCCR`.

`Work.BoseB4.ModeFock` then assembles an arbitrary family of "mode vectors"
`f : Mode → Fin m → ℝ` (as annihilation/creation of superpositions) and
`Work.BoseB4.B7Instance` inhabits `Work.BoseB7.FockData` with
`ccrK i j = Σ_l f i l * f j l` — the Gram matrix of the one-particle mode
vectors, which is the box kernel once the mode vectors are FS's
`Q(e^{ikx}χ_Λ)`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-! ## 1. The state space and the Bombieri form -/

/-- The **real bosonic Fock space** over `m` modes, in the monomial-coefficient
model: finitely supported functions on the multi-indices `Fin m →₀ ℕ`
(`p α` is the coefficient of `x^α`). -/
abbrev RealFock (m : ℕ) : Type := (Fin m →₀ ℕ) →₀ ℝ

/-- The multi-index factorial `α! = ∏_l (α_l)!` — the weight making the
normalised monomials `x^α/√(α!)` orthonormal. -/
noncomputable def mfac {m : ℕ} (α : Fin m →₀ ℕ) : ℝ :=
  α.prod fun _ k => (k.factorial : ℝ)

/-- The unit vector `e_l` of the multi-index monoid. -/
noncomputable def e (m : ℕ) (l : Fin m) : Fin m →₀ ℕ := Finsupp.single l 1

/-- **The Bombieri (Fock) form** `⟪p, q⟫ = Σ_α p_α q_α α!` on `RealFock m`,
packaged as a bilinear form (linear in the second argument of the first map). -/
noncomputable def bomb (m : ℕ) :
    RealFock m →ₗ[ℝ] RealFock m →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ fun α : Fin m →₀ ℕ =>
    LinearMap.toSpanSingleton ℝ _ ((mfac α) • Finsupp.lapply α)

/-! ## 2. Annihilation and creation of one mode -/

/-- **Annihilation** of mode `l`: the formal derivative `∂/∂x_l`, with the
monomial-coefficient convention `(∂_l p) α = (α_l) · p (α - e_l)`. -/
noncomputable def ann (m : ℕ) (l : Fin m) : RealFock m →ₗ[ℝ] RealFock m :=
  Finsupp.lsum ℝ fun α : Fin m →₀ ℕ =>
    LinearMap.toSpanSingleton ℝ _ ((α l : ℝ) • Finsupp.single (α - e m l) (1 : ℝ))

/-- **Creation** of mode `l`: multiplication by `x_l`, with the convention
`(x_l · p) α = p (α - e_l)`. -/
noncomputable def cre (m : ℕ) (l : Fin m) : RealFock m →ₗ[ℝ] RealFock m :=
  Finsupp.lsum ℝ fun α : Fin m →₀ ℕ => Finsupp.lsingle (α + e m l)

end Work.BoseB4
