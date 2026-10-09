import Mathlib
import Submission.Work.HilbertSymbolGeneral.hilbertReciprocityTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local-norm "bad indicator" is a character of `Kˣ`

For a quadratic extension `L/K` of number fields and a place `v` of `K`, the local norm subgroup of
`K_vˣ` has index dividing `2` (`Work.HilbertSymbolGeneral.localNormSubgroup_index_dvd_two`), so the
indicator of its complement is additive: `x * y` fails to be a local norm at `v` exactly when
exactly one of `x`, `y` does.

This is the multiplicativity of the bad set in its *element* variable — the form in which the
product formula `HilbertReciprocityTwo` is applied in the `μ₂` local Tate system.  It is a direct
consequence of `Work.HilbertSymbolGeneral.notMem_bad_of_mul` together with the dictionary
`Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup` between the local norm condition and
the local norm subgroup of the idèle-theoretic formulation.
-/

namespace Work.SSGRoute.ZDataTwo

/-- **The bad indicator is a character.**  For a quadratic extension `L/K` of number fields,
`x * y` is not a local norm at `v` exactly when exactly one of `x`, `y` is not. -/
theorem isLocalNorm_mul_iff_bad {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x y : Kˣ) (v : NK.GlobalCFT.Place K) :
    (¬ NK.NUV2.LC.IsLocalNorm K L (x * y) v) ↔
      ((¬ NK.NUV2.LC.IsLocalNorm K L x v) ∧ NK.NUV2.LC.IsLocalNorm K L y v) ∨
        (NK.NUV2.LC.IsLocalNorm K L x v ∧ ¬ NK.NUV2.LC.IsLocalNorm K L y v) := by
  rw [Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := K) (L := L) (x * y) v,
    Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := K) (L := L) x v,
    Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := K) (L := L) y v]
  refine (Work.HilbertSymbolGeneral.notMem_bad_of_mul h2 x y v).trans ?_
  tauto

end Work.SSGRoute.ZDataTwo
