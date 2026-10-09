import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Span.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `S`-span of a set is contained in its `R`-span when `S → R` is a scalar tower

If `M` is simultaneously an `S`-module and an `R`-module, `R` is an `S`-algebra, and
the two actions are compatible (`IsScalarTower S R M`), then for `s : S` and `m : M`
the compatibility gives `s • m = (algebraMap S R s) • m`. Consequently any
`S`-submodule of `M` which is closed under the `R`-action (such as the `R`-span of a
set) is also an `S`-submodule, so the `S`-span is contained in the `R`-span.
-/

namespace Commons.Algebra.Module

lemma span_subset_span_of_isScalarTower {S R M : Type*} [CommRing S] [CommRing R]
    [AddCommGroup M] [Algebra S R] [Module S M] [Module R M] [IsScalarTower S R M] (T : Set M) :
    (Submodule.span S T : Set M) ⊆ (Submodule.span R T : Set M) := by
  exact Submodule.span_subset_span (R := S) (S := R) T

end Commons.Algebra.Module