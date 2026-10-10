import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Map
import Submission.Work.SSGRoute.lnMon_map_perm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The induced algebra map preserves the nested span

`nestedSpan X j` is the `ℤ`-span of the left-nested bracket monomials `lnMon w` of degree `j`
inside the free associative `ℤ`-algebra `FreeAssoc X = ℤ[FreeMonoid X]`, and `freeAssocMap σ` is
the `ℤ`-algebra endomorphism of `FreeAssoc X` induced by a permutation `σ` of the generators.

The claim of this file is that `freeAssocMap σ` maps `nestedSpan j` into itself.  Indeed
`freeAssocMap σ` is additive (in fact `ℤ`-linear), so it suffices to see that it sends each
spanning monomial `lnMon w` with `w.length = j` into `nestedSpan j`; by the `σ`-compatibility
`lnMon (w.map σ) = freeAssocMap σ (lnMon w)` of `lnMon_map_perm` it sends it to
`lnMon (w.map σ)`, and `w.map σ` again has length `j`.
-/

noncomputable section

namespace Work.SSGRoute

open Work.SSGRoute.prop5

theorem freeAssocMap_mem_nestedSpan {X : Type*} (σ : X ≃ X) (j : ℕ)
    {a : Work.SSGRoute.prop5.FreeAssoc X}
    (ha : a ∈ Work.SSGRoute.prop5.nestedSpan (X := X) j) :
    Work.SSGRoute.prop5.freeAssocMap σ a ∈ Work.SSGRoute.prop5.nestedSpan (X := X) j := by
  -- `freeAssocMap σ` is an additive map; view it as a `ℤ`-linear one.
  let f : FreeAssoc X →ₗ[ℤ] FreeAssoc X :=
    (freeAssocMap σ : FreeAssoc X →+ FreeAssoc X).toIntLinearMap
  -- it suffices to check the spanning monomials
  have hle : nestedSpan (X := X) j ≤ Submodule.comap f (nestedSpan (X := X) j) := by
    rw [nestedSpan]
    refine Submodule.span_le.2 ?_
    rintro b ⟨w, hw, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    show freeAssocMap σ (lnMon w) ∈
      Submodule.span ℤ {a : FreeAssoc X | ∃ w : List X, w.length = j ∧ a = lnMon w}
    rw [← lnMon_map_perm σ w]
    exact Submodule.subset_span ⟨w.map σ, by simpa using hw, rfl⟩
  exact hle ha

end Work.SSGRoute
