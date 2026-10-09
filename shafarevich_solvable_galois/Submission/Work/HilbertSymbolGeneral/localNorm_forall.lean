import Submission.Work.HilbertSymbolGeneral.localNorm_not_singleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `∀ v` form of the "one place omitted" reciprocity

`Work.HilbertSymbolGeneral.localNorm_not_singleton` says that a single place of local-norm failure
is no failure at all.  This module records the form in which the local–global principle consumes it
— if `x` is a local norm at every place outside `v₀`, it is a local norm at *every* place — matching
the conclusion of the conditional `NK.NUV2.LC.HilbertReciprocityTwo.eq_empty_of_subset_singleton`,
but now unconditionally (no `HilbertReciprocityTwo` hypothesis), hence immediately usable by
`NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_of_hilbertReciprocityTwo`
and its consumers.
-/

open scoped Classical

namespace Work.HilbertSymbolGeneral

/-- **A single place of local-norm failure is no failure at all**, in the form consumed downstream:
if the quadratic extension `L / K` of number fields and `x ∈ Kˣ` satisfy the local-norm condition at
every place other than `v₀`, then `x` is a local norm at every place. -/
theorem localNorm_forall_of_forall_ne
    (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (h2 : Nat.card (L ≃ₐ[K] L) = 2)
    (x : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → NK.NUV2.LC.IsLocalNorm K L x v) :
    ∀ v : NK.GlobalCFT.Place K, NK.NUV2.LC.IsLocalNorm K L x v := by
  intro v
  by_cases hv : v = v₀
  · rw [hv]
    exact localNorm_not_singleton K L h2 x v₀ h
  · exact h v hv

end Work.HilbertSymbolGeneral
