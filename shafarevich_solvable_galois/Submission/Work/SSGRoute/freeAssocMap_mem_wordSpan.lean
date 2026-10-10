import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Map
import Submission.Work.SSGRoute.freeAssocMap_wordEl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The induced algebra map preserves the word span

`wordSpan X j` is the `ℤ`-span of the basis words `wordEl w` with `w.length = j` inside the free
associative `ℤ`-algebra `FreeAssoc X = ℤ[FreeMonoid X]`, and `freeAssocMap σ` is the
`ℤ`-algebra endomorphism of `FreeAssoc X` induced by a permutation `σ` of the generators.

The claim of this file is that `freeAssocMap σ` maps `wordSpan j` into itself.  Indeed
`freeAssocMap σ` is additive (in fact `ℤ`-linear), so it suffices to see that it sends each
spanning word `wordEl w` with `w.length = j` into `wordSpan j`; by the computation
`freeAssocMap σ (wordEl w) = wordEl (w.map σ)` it sends it to `wordEl (w.map σ)`, and `w.map σ`
again has length `j`.
-/

noncomputable section

namespace Work.SSGRoute

open Work.SSGRoute.prop5

theorem freeAssocMap_mem_wordSpan {X : Type*} (σ : X ≃ X) (j : ℕ)
    {a : Work.SSGRoute.prop5.FreeAssoc X}
    (ha : a ∈ Work.SSGRoute.prop5.wordSpan (X := X) j) :
    Work.SSGRoute.prop5.freeAssocMap σ a ∈ Work.SSGRoute.prop5.wordSpan (X := X) j := by
  -- view the algebra endomorphism as a `ℤ`-linear endomorphism
  let f : FreeAssoc X →ₗ[ℤ] FreeAssoc X :=
    (freeAssocMap σ : FreeAssoc X →+ FreeAssoc X).toIntLinearMap
  -- it suffices to check the spanning words
  have hle : wordSpan (X := X) j ≤ Submodule.comap f (wordSpan (X := X) j) := by
    rw [wordSpan]
    refine Submodule.span_le.2 ?_
    rintro b ⟨w, hw, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    show freeAssocMap σ (wordEl w) ∈
      Submodule.span ℤ {a : FreeAssoc X | ∃ w : List X, w.length = j ∧ a = wordEl w}
    rw [freeAssocMap_wordEl]
    exact Submodule.subset_span ⟨w.map σ, by simpa using hw, rfl⟩
  exact hle ha

end Work.SSGRoute
