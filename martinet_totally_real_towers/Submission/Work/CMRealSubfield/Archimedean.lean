import Mathlib

/-!
# Archimedean places: real places restrict, complex places propagate

This module records the archimedean input of the real-subfield reduction (item 4 of the
subproject): a real place of an extension field restricts to a real place of the base, hence
**if the base field has no real place, no extension field has one** — every archimedean place
of the extension is complex.  In the CM setting this is the standard statement that the real
places of the maximal real subfield `K⁺` all become complex in `K` (and that the levels of a
tower over a totally imaginary base are totally imaginary).

The content is essentially Mathlib's `NumberField.isTotallyComplex_of_algebra` (which itself
rests on `InfinitePlace.IsComplex.of_comap` / `InfinitePlace.IsReal.comap`); we state it in the
forms used by the reduction, in particular the *pointwise* form on `InfinitePlace`, which is
what "every archimedean place of `L` is complex" means.
-/

open NumberField

namespace Work.CMRealSubfield

/-- **Real places restrict to real places.**  If `φ : F →+* K` and `w` is a real place of
`K`, then the place `w ∘ φ` of `F` is real.  (Contrapositive: a complex place of the base
cannot lift to a real place.) -/
theorem isReal_comap_of_isReal {F K : Type*} [Field F] [Field K] (φ : F →+* K)
    {w : NumberField.InfinitePlace K} (hw : w.IsReal) : (w.comap φ).IsReal :=
  InfinitePlace.IsReal.comap φ hw

/-- **The tower bridge (pointwise form).**  If `F` has no real place (`IsTotallyComplex F`),
then every archimedean place of any extension field `K` of `F` is complex. -/
theorem isComplex_of_isTotallyComplex_base {F K : Type*} [Field F] [Field K] [Algebra F K]
    [NumberField.IsTotallyComplex F] (w : NumberField.InfinitePlace K) : w.IsComplex :=
  InfinitePlace.IsComplex.of_comap (algebraMap F K)
    (NumberField.IsTotallyComplex.isComplex (w.comap (algebraMap F K)))

/-- **The tower bridge (`IsTotallyComplex` form).**  Total complexness propagates up every
field extension.  This is Mathlib's `NumberField.isTotallyComplex_of_algebra`, restated for
the reduction; it applies in particular to every level of a tower over a totally imaginary
base field. -/
theorem isTotallyComplex_of_isTotallyComplex_base (F K : Type*) [Field F] [Field K]
    [Algebra F K] [NumberField.IsTotallyComplex F] : NumberField.IsTotallyComplex K :=
  NumberField.isTotallyComplex_of_algebra F K

/-- Every infinite place of a totally real field is real (the defining property, restated
pointwise). -/
theorem isReal_of_isTotallyReal (K : Type*) [Field K] [NumberField.IsTotallyReal K]
    (w : NumberField.InfinitePlace K) : w.IsReal :=
  NumberField.IsTotallyReal.isReal w

/-- Every infinite place of a totally complex field is complex (the defining property,
restated pointwise).  In particular every infinite place of a CM field is complex, so a CM
field is never totally real. -/
theorem isComplex_of_isTotallyComplex (K : Type*) [Field K] [NumberField.IsTotallyComplex K]
    (w : NumberField.InfinitePlace K) : w.IsComplex :=
  NumberField.IsTotallyComplex.isComplex w

end Work.CMRealSubfield
