import Mathlib
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.InertiaArithImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Notation for the wild inertia subgroup of a finite place

`k` a number field, `Ω` a field with a `k`-algebra structure, `A ≤ Ω` a valuation subring whose
restriction to `k` is a finite place.  This file fixes the notation

* `Work.SSGRoute.PT.placePrime k Ω A hA` — the prime `𝔭` of `𝓞 k` below `A`;
* `Work.SSGRoute.PT.resQ k Ω A hA` — the residue characteristic of the completion at `𝔭`;
* `locField`, `locClosure`, `locGal` — the local field `κ = k_𝔭`, a separable closure `κ̄` and
  its absolute Galois group;
* `locV`, `locI` — the wild inertia `V_κ` (the maximal closed normal pro-`q` subgroup of
  `Gal(κ̄/κ)`) and the inertia subgroup `I_κ`.

All of them are `abbrev`s, so they are definitionally equal to the `NK.*` expressions they wrap.
-/

open scoped Pointwise

namespace Work.SSGRoute.PT

section Abbrevs

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- The prime of `𝓞 k` below the place `A`. -/
noncomputable abbrev placePrime (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
  Submission.NeukirchUchida.primeOf A hA

/-- The residue characteristic at the place `A`. -/
noncomputable abbrev resQ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : ℕ :=
  NK.TameStructureDeep.Tame.resCharAt (placePrime k Ω A hA)

/-- The local field of the place `A`: the `𝔭`-adic completion of `k`. -/
noncomputable abbrev locField (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : Type _ :=
  (placePrime k Ω A hA).adicCompletion k

/-- A separable closure of the local field of `A`. -/
noncomputable abbrev locClosure (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : Type _ :=
  SeparableClosure (locField k Ω A hA)

/-- The absolute Galois group of the local field of `A`. -/
noncomputable abbrev locGal (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : Type _ :=
  Gal(locClosure k Ω A hA / locField k Ω A hA)

/-- The **wild inertia** `V_κ` of the local field. -/
noncomputable abbrev locV (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Subgroup (locGal k Ω A hA) :=
  NK.LocalTame.wildInertiaSubgroup (κ := locField k Ω A hA) (K' := locClosure k Ω A hA)
    (resQ k Ω A hA)

/-- The **inertia subgroup** `I_κ` of the local field. -/
noncomputable abbrev locI (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Subgroup (locGal k Ω A hA) :=
  NK.LocalAnabelian.inertiaSubgroup (κ := locField k Ω A hA) (K' := locClosure k Ω A hA)
    (resQ k Ω A hA)

end Abbrevs

end Work.SSGRoute.PT
