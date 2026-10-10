import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniqueness of the extension of a henselian valuation to a finite separable extension

Let `V` be a henselian valuation subring of a field `F` and let `F'/F` be a finite
separable extension.  Then `V` has *at most one* extension to a valuation subring of `F'`:
if `W₁, W₂ : ValuationSubring F'` both pull back to `V` along `algebraMap F F'`, then
`W₁ = W₂`.

This is an immediate consequence of the general algebraic statement
`Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic`, since a finite dimensional
field extension is algebraic (the separability hypothesis is therefore not needed and is
kept only to match the requested signature).
-/

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

theorem unique_extension_of_henselian_finite {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (V : ValuationSubring F)
    [HenselianLocalRing V] (W₁ W₂ : ValuationSubring F')
    (h₁ : W₁.comap (algebraMap F F') = V) (h₂ : W₂.comap (algebraMap F F') = V) : W₁ = W₂ := by
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'
  exact eq_of_comap_eq_of_isAlgebraic V W₁ W₂ h₁ h₂

end Commons.RingTheory.Valuation
