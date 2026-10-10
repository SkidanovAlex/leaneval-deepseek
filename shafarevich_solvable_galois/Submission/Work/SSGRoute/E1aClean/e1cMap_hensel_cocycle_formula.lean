import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts
import Submission.Work.SSGRoute.E1aClean.e1cMapCocycleFormula
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `E1c` dictionary in cocycle form at the henselian (level-2) datum — **(BC)** ingredient

`e1cMap_eq_H1π_of_cocycle_lift` (`ExtChain.E1cGeneric`) is stated over an arbitrary base field `k`
and an arbitrary finite Galois `K/k`.  This file records its *level-2* instantiation, i.e. at the
henselisation datum of the finite place `A`

  `k ↦ ↥(decompField k Ω A)` (the decomposition field `k^h = Ω^{D_A}`),  `K ↦ henselOverDecomp k Ω K A`

with level-2 coefficients `Rep.res φ R` for a group hom
`φ : Gal(K^h/k^h) →* Gal(K/k)` (the restriction along `K ≤ K^h`).

This is the shape in which **(BC)** `dict_baseChange_decomp` — the last unclaimed ingredient of the
S6 dictionary `E1aClean.localDictionary_natural_family_arch` — consumes the dictionary at level 2:
there the level-2 cocycle is `ñ ∘ ι`, `ι` the canonical comparison of the free covers
`Rep.free Coeff (K^h ≃ₐ[↥k^h] K^h) X.V → Rep.free Coeff (K ≃ₐ[k] K) X.V`.

Note (measured, and flagged by both reviewers of the statement): **no `NumberField ↥(henselOverDecomp
k Ω K A)` is needed, and none is available** — `k^h = Ω^{D_A}` has infinite degree over `ℚ` (its
Galois group is the decomposition group `D_A`, closed but not open).  The four instances the
instantiation needs are `CharZero`, `IsAlgClosure ↥(decompField k Ω A) Ω`,
`FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)` and
`IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)` — exactly the datum facts of
`E1aClean/decompDatumFacts.lean`.  Likewise `IsFinPlace k A` is *not* used. -/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.E1aClean

/-- **The `E1c` dictionary in cocycle form at the level-2 (henselian) datum.** -/
theorem e1cMap_hensel_cocycle_formula
    {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
            ↥(henselOverDecomp k Ω K A)) →* (K ≃ₐ[k] K))
    [CharZero ↥(decompField k Ω A)]
    [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
        (Rep.res φ R))))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := ↥(decompField k Ω A)) (Ω := Ω)
      (K := henselOverDecomp k Ω K A) (Rep.res φ R))
    (hñ : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := ↥(decompField k Ω A)) (Ω := Ω)
          (K := henselOverDecomp k Ω K A) (Rep.res φ R) (c.1 g)
        = Work.GroupCohomology.d0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := ↥(decompField k Ω A)) (Ω := Ω)
              (K := henselOverDecomp k Ω K A) (Rep.res φ R)) ñ g)
    (y : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) (Rep.res φ R))
      (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) 0)
    (hy : (Work.SSGRoute.ExtChain.E1cGeneric.piH (k := ↥(decompField k Ω A)) (Ω := Ω)
          (K := henselOverDecomp k Ω K A) (Rep.res φ R) ñ
        : Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := ↥(decompField k Ω A)) (Ω := Ω)
              (K := henselOverDecomp k Ω K A) (Rep.res φ R)))
        = ↑(Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := ↥(decompField k Ω A)) (Ω := Ω)
            (K := henselOverDecomp k Ω K A)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := ↥(decompField k Ω A)) (Ω := Ω)
              (K := henselOverDecomp k Ω K A) (Rep.res φ R)) y)) :
    Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) (Rep.res φ R)
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := ↥(decompField k Ω A)) (Ω := Ω)
          (K := henselOverDecomp k Ω K A) (Rep.res φ R) y)
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
            (Rep.res φ R)) c :=
  Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_eq_H1π_of_cocycle_lift
    (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) (Rep.res φ R)
    c ñ hñ y hy

end Work.SSGRoute.E1aClean
