import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.KafzSym
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KafzGauge` — the particle-number gauge on `cfock X`

For `u : ℂ` the **gauge operator** `gaugeC X u` multiplies the monomial `β` by
`u ^ (Σ β)`, i.e. it is the diagonal operator `u^{n₊}` (with the occupation number
`n₊ = Σ β`).  Its defining property is

    `gaugeC u (annC j w) = u • annC j (gaugeC u w)`,
    `gaugeC u (creC j w) = u⁻¹ • creC j (gaugeC u w)`  (`u ≠ 0`),

so that for a word `K` with `a` annihilations and `c` creations

    `gaugeC u (K w) = u ^ (a - c) • K (gaugeC u w)`.

The dictionary slots `KvecF i` all satisfy `a - c = q_i - p_i` (KafzSym's
`pvecF`/`qvecF`), which turns the general-`z` symbol into the real-`r` one:

    `gaugeC u (symC z w) = symR r (gaugeC u w)`   whenever `z = r*u`.

This is FS's "in the operator we can replace `a_{±k}` by `e^{iφ}a_{±k}`" — the step
of the proof of `thm:Kafz` that reduces a complex coherent parameter to a
nonnegative one, and the reason no `r³`-sized phase errors appear in the
comparison of `KafzSym.symR` with `KzOpC`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The gauge `u^{−n₊}` on the complex Fock core `(X →₀ ℕ) →₀ ℂ` (the module
underlying `cfock X`): the monomial `β` is multiplied by `u ^ (−(Σ β))`.  The sign
is chosen so that `annC j` gets `u` and `creC j` gets `u⁻¹`, which is the
convention under which the dictionary slot `KvecF i` (raising `n₊` by `p i − q i`)
gets the phase `u ^ (q i − p i)`. -/
noncomputable def gaugeF (X : Type*) [DecidableEq X] (u : ℂ) :
    ((X →₀ ℕ) →₀ ℂ) →ₗ[ℂ] ((X →₀ ℕ) →₀ ℂ) :=
  Finsupp.lsum ℂ fun β : X →₀ ℕ =>
    LinearMap.toSpanSingleton ℂ _
      ((u ^ (-(β.sum fun _ k => k) : ℤ)) • Finsupp.single β (1 : ℂ))

/-- The gauge `u^{n₊}` on `cfock X`. -/
noncomputable def gaugeC (X : Type*) [DecidableEq X] (u : ℂ) : cfock X →ₗ[ℂ] cfock X :=
  (toCFock X).toLinearMap.comp ((gaugeF X u).comp (toCFock X).symm.toLinearMap)

@[simp] lemma gaugeF_single (X : Type*) [DecidableEq X] (u : ℂ) (β : X →₀ ℕ) (c : ℂ) :
    gaugeF X u (Finsupp.single β c)
      = (u ^ (-(β.sum fun _ k => k) : ℤ) * c) • Finsupp.single β (1 : ℂ) := by
  rw [gaugeF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]

end Work.BoseBoxFock
