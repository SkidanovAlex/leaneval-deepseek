import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.exists_isNonarchimedeanLocalField_intermediateField
import Submission.NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Honda's reciprocity law over a subfield of the maximal abelian extension

The chapter proves Honda's explicit reciprocity law
`NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity` for an *arbitrary* nonarchimedean local
field of characteristic zero.  A finite-dimensional subfield `L` of `F^{ab}`
(`F = Q.adicCompletion K`) is again such a field, by
`NK.LocalReciprocityLubinTate.Eval.exists_isNonarchimedeanLocalField_intermediateField`; so Honda's law
applies *over the base field `L`* as soon as the two instances are supplied from that existential.

This is the "base-change" rung of the explicit-reciprocity route to the chapter's remaining canonicity
(README §21.13, Route A): the Lubin–Tate symbol over `F`, restricted to `L`, has to be compared with the
Lubin–Tate symbol over `L`, and the norm-group input for the latter is exactly Honda's law over `L`.

## Main result

* `NK.LocalReciprocityLubinTate.Eval.hondaReciprocity_intermediateField`.
-/

open scoped Classical ValuativeRel

namespace NK.LocalReciprocityLubinTate.Eval

universe u

/-- **Honda's reciprocity law over a finite subfield of the maximal abelian extension.**

For a finite-dimensional subfield `L` of `F^{ab}` (`F = Q.adicCompletion K`), equipped with the
nonarchimedean local field structure supplied by
`NK.LocalReciprocityLubinTate.Eval.exists_isNonarchimedeanLocalField_intermediateField`, and a
uniformiser `π_L` of `L`, Honda's explicit reciprocity law holds over the base field `L`:

  `N_{L(Λ_n)/L} L(Λ_n)ˣ = ⟨π_L⟩ · U_L^n`   for all `n ≥ 1`,

where `Λ_n` are the division points of the Lubin–Tate group of `L` with parameter `π_L`. -/
theorem hondaReciprocity_intermediateField {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : IntermediateField (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)))
    [FiniteDimensional (Q.adicCompletion K) L]
    [ValuativeRel ↥L] [TopologicalSpace ↥L] [IsNonarchimedeanLocalField ↥L]
    (πL : (↥L)ˣ) (hπL : NK.LocalReciprocityLubinTate.IsUniformizer ↥L (πL : ↥L)) :
    NK.LocalReciprocityLubinTate.HondaReciprocity ↥L πL
      (NK.LocalReciprocityLubinTate.higherUnits ↥L)
      (NK.LocalReciprocityLubinTate.residueCard ↥L) :=
  NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity ↥L πL hπL

end NK.LocalReciprocityLubinTate.Eval
