import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Submission.Work.SSGRoute.prop5.magnusLieDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The algebra map on `FreeAssoc` induced by a permutation of the generators

`FreeAssoc X = ℤ[FreeMonoid X]`, and there was no action of a permutation of `X` on it in the
workspace.  This file supplies it.  The companion simp lemma
`freeAssocMap σ (wordEl w) = wordEl (w.map σ)` (needed to prove the `σ`-compatibility
`lnMon (w.map σ) = freeAssocMap σ (lnMon w)` of the nested commutator monomial by `induction w`)
reduces, after `simp only [freeAssocMap, wordEl, MonoidAlgebra.mapDomainRingHom_apply,
Equiv.refl_apply]` and `congr 1`, to `(FreeMonoid.map σ) w = List.map σ w`, i.e. to the fact that
`FreeMonoid.map` *is* `List.map` (`FreeMonoid X` is `List X` definitionally) — that final step is
the only thing left, and it is a one-liner.
-/

noncomputable section

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- The algebra endomorphism of `FreeAssoc X` induced by a permutation `σ` of the generators. -/
noncomputable def freeAssocMap (σ : X ≃ X) : FreeAssoc X →+* FreeAssoc X :=
  MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map σ)

end Work.SSGRoute.prop5
