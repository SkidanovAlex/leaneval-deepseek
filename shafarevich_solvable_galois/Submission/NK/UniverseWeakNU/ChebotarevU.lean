/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Čebotarev input at an arbitrary universe: definitions

Universe-polymorphic copies of the `Prop`s of `Submission/Work/ChebotarevGeneral/Defs.lean` that are
needed to discharge `NK.UniverseWeakNU.ChebotarevFrobeniusInputU` from the abelian case of
Čebotarev's density theorem at `Type u`:

* `NK.UniverseWeakNU.AbelianChebotarevDensityU` — the abelian case in density form, at `Type u`
  (copy of `NK.ChebotarevGeneral.AbelianChebotarevDensity`);
* `NK.UniverseWeakNU.ChebotarevInfiniteU` — the existence form of (the general) Čebotarev's
  theorem, at `Type u` (copy of `NK.ChebotarevGeneral.ChebotarevInfinite`).

The two results proved from them are

* `NK.UniverseWeakNU.chebotarevInfiniteU_of_abelianU :
    AbelianChebotarevDensityU → ChebotarevInfiniteU`
  (the cyclic case implies the general case, in existence form; the ascent half of Deuring's
  transfer);
* `NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_abelianU :
    AbelianChebotarevDensityU → ChebotarevFrobeniusInputU`,

so that the Čebotarev leaf of the polymorphic weak-Neukirch–Uchida chain is reduced, at `Type u`
exactly as at `Type 0`, to the abelian case of the density theorem.  (The analytic input that
discharges the abelian case, `NK.Chebotarev.AbelianChebotarevOfLFunctions`, is that chapter's
responsibility; see `README.md` §5.)
-/

import Mathlib
import Submission.NK.ChebotarevGeneral.Infinity
import Submission.NK.ChebotarevGeneral.RatLevel
import Submission.NK.UniverseWeakNU.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UniverseWeakNU

noncomputable section

universe u

open NK.Chebotarev

/-- **The abelian case of Čebotarev's density theorem**, at an arbitrary universe.  Copy of
`NK.ChebotarevGeneral.AbelianChebotarevDensity`.

For an abelian finite Galois extension `N/K` of number fields at `Type u` and `σ : Gal(N/K)`, the
primes of `K` whose Frobenius is `σ` have Dirichlet density `1/|Gal(N/K)|`. -/
def AbelianChebotarevDensityU : Prop :=
  ∀ (K N : Type u) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N],
    (∀ a b : Gal(N/K), a * b = b * a) → ∀ σ : Gal(N/K),
      NumberField.Set.HasDirichletDensity
        (NK.ChebotarevGeneral.frobSet (K := K) (N := N) σ)
        (1 / (Nat.card (Gal(N/K)) : ℝ))

/-- **The existence form of Čebotarev's theorem**, in the form needed to derive
`NK.UniverseWeakNU.ChebotarevFrobeniusInputU`: for a finite Galois extension `N/K` of number fields
with the **base field `K` in the bottom universe** and the top field `N` in `Type u`, every
`σ : Gal(N/K)` is a Frobenius element at infinitely many primes of `K`.

### Why the base field is not also moved to `Type u`

The naive copy of `NK.ChebotarevGeneral.ChebotarevInfinite` would quantify over `K : Type u` and
`N : Type u`.  That statement is *not* sufficient for the purpose of this directory: the final step
`NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_infiniteU` has to instantiate it at the base field
`ℚ`, and `ℚ : Type 0`, so for `u ≥ 1` the line `h ℚ N σ` of the universe-0 proof
(`NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_infinite`) is a universe error against a
hypothesis quantified over `K : Type u`.  Moving the *base* field to the bottom universe removes
exactly that obstruction while keeping the *top* field — the one that the polymorphic
Uchida/WeakNU chain of this directory works with — in `Type u`; the ascent argument proving this
statement applies the abelian case to the extension `N/↥M` with `M = N^{⟨σ⟩}`, where `↥M` is a
`Type u` field, so `NK.UniverseWeakNU.AbelianChebotarevDensityU` (base and top in `Type u`) is
exactly the hypothesis consumed.

The statement is universally quantified over `K : Type`, so instantiating it at `K = ℚ` is
legitimate. -/
def ChebotarevInfiniteU : Prop :=
  ∀ (K : Type) (N : Type u) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] (σ : Gal(N/K)),
    (NK.ChebotarevGeneral.frobSet (K := K) (N := N) σ).Infinite

end

end NK.UniverseWeakNU
