import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.l2FormDef` — the ℓ² form on finitely supported sequences

`l2Form ι f g = ∑_m f m * g m` is the ℓ² inner product of the finitely supported
real functions on `ι`.  It is the Fock inner product of the occupation-number
representation (`Work.BoseB7.boseDefs`), where the Fock space is the algebraic
core `ι →₀ ℝ` and the sum is finite because `f` has finite support.

It is written as a `LinearMap ℝ (ι →₀ ℝ) (LinearMap ℝ (ι →₀ ℝ) ℝ)`: the sum over
the support of `f` of `f m • (evaluation at m)`, so that linearity in the first
argument is automatic; the symmetry (`l2Form_symm`), positivity and definiteness
(`l2Form_posDef`) and the computational rules (`l2Form_single`, `l2Form_self`)
are proved in the sibling modules.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

universe u

/-- **The ℓ² form on finitely supported sequences**: `l2Form ι f g = ∑_m f m * g m`.

Concretely `l2Form ι f = ∑_{m ∈ f.support} f m • (· ↦ · m)`, the sum being finite
because `f` is finitely supported. -/
def l2Form (ι : Type u) : (ι →₀ ℝ) →ₗ[ℝ] (ι →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ (fun m : ι =>
    LinearMap.toSpanSingleton ℝ ((ι →₀ ℝ) →ₗ[ℝ] ℝ) (Finsupp.lapply m))

end Work.BoseB7
