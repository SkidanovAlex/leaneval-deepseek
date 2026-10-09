import Mathlib
import Submission.Work.SSGRoute.E1aClean.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the named coefficient-change map `extPostIsoHom`

`E1aClean/Transport.lean` builds the local transport of the E1a comparison square out of three
*named* additive maps — `coeffStep` (postcomposition with a fixed coefficient iso), `groupStep`
(functoriality along `Rep.res eG.symm`) and `finalStep` (postcomposition with `resResIsoIso`).

Item (2) of the local dictionary's assembly is that `localExtTransport` is *natural in the first
variable* `X` (i.e. commutes with precomposition `mk₀ g ∘ ·`).  For `groupStep` that is the
functoriality of `mapExt`; for `coeffStep`/`finalStep` it is the associativity of `Ext.comp`,
recorded here for `extPostIsoHom` (which is exactly `coeffStep`/`finalStep`).  Postcomposition is
covariant and precomposition contravariant, so they commute on the nose.

Two traps, both paid for once already:

* the composed element `(mk₀ g).comp y _` lives in `Ext M₂ N n`, so `extPostIsoHom` must be applied
  at `M₂`, not `M₁` (the indices go the *other* way round than one first writes);
* `Ext.comp_assoc_of_third_deg_zero`'s degree slot is the `0 + n = ·` one — pass `zero_add n`, not
  a `0 + 0 = 0`.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory

noncomputable section

/-- **Naturality of `extPostIsoHom` in the first variable.**  Postcomposition with a fixed
coefficient change commutes with precomposition. -/
theorem extPostIsoHom_natural {G : Type} [Group G] {N N' : Rep.{0} SSGRoute.PTExt.Coeff G}
    (e : N ≅ N') {M₁ M₂ : Rep.{0} SSGRoute.PTExt.Coeff G} (g : M₂ ⟶ M₁) (n : ℕ)
    (y : CategoryTheory.Abelian.Ext M₁ N n) :
    extPostIsoHom e M₂ n ((CategoryTheory.Abelian.Ext.mk₀ g).comp y (zero_add n))
      = (CategoryTheory.Abelian.Ext.mk₀ g).comp (extPostIsoHom e M₁ n y) (zero_add n) := by
  rw [extPostIsoHom_apply, extPostIsoHom_apply]
  exact CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
    (CategoryTheory.Abelian.Ext.mk₀ g) y (CategoryTheory.Abelian.Ext.mk₀ e.hom)
    (zero_add n)

end

end Work.SSGRoute.E1aClean
