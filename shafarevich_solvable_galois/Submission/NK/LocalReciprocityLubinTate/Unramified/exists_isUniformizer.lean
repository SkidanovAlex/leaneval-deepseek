import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The existence of a uniformiser

A nonarchimedean local field has a uniformiser, and Mathlib has the raw material for this
(`Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`, which needs the value group of the
valuation to be cyclic and nontrivial — exactly the content of `IsNonarchimedeanLocalField`).
This file records the consequence in the chapter's own vocabulary
(`NK.LocalReciprocityLubinTate.IsUniformizer`, i.e. Mathlib's `Valuation.IsUniformizer` for
`ValuativeRel.valuation F`), in the unit-group form `∃ π : Fˣ, IsUniformizer F (π : F)` in which
the chapter's theorems (`Unramified.hondaReciprocity`,
`Unramified.nonempty_lubinTateTower_adicCompletion`, …) consume it.

The point is that the boundary theorem
`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` should not carry a *chosen*
uniformiser as a hypothesis: it is a statement about `ArtinReciprocity`, which does not mention any
uniformiser, and a uniformiser always exists.

## Main results

* `NK.LocalReciprocityLubinTate.exists_isUniformizer`;
* `NK.LocalReciprocityLubinTate.exists_isUniformizer_adicCompletion`.
-/

namespace NK.LocalReciprocityLubinTate

universe u

/-- **Every nonarchimedean local field has a uniformiser**, as a unit of the field.

The element produced by Mathlib lies in the valuation subring and generates the maximal ideal;
its valuation is nonzero, so it is a unit of `F`. -/
theorem exists_isUniformizer (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : ∃ π : Fˣ, IsUniformizer F (π : F) := by
  obtain ⟨π, hπ⟩ := Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial
    (ValuativeRel.valuation F)
  exact ⟨Units.mk0 (π : F) hπ.ne_zero, hπ⟩

/-- The same for a `p`-adic field `Q.adicCompletion K`, in the form used by the boundary
theorem. -/
theorem exists_isUniformizer_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ π : (Q.adicCompletion K)ˣ, IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K) :=
  exists_isUniformizer (Q.adicCompletion K)

end NK.LocalReciprocityLubinTate
