import Mathlib
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.GlobalCFT.NormGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The statement of Hilbert reciprocity in the "one place omitted" form

This module contains the *vocabulary* shared by the deliverable
`NK.CFTLib.IdeleHasse.onePlace_localFaithful`
(`Submission/Work/CFTLib/IdeleHasse/onePlace_localFaithful.lean`) and by the lemma it reduces to,
`NK.CFTLib.IdeleHasse.HilbertReciprocityCyclic`.

* `NK.CFTLib.IdeleHasse.localImageAt v x` — the image of `x : Kˣ` in the completion `K_v`;
* `NK.CFTLib.IdeleHasse.HilbertReciprocityCyclic` — Hilbert reciprocity in the form
  "the set of places at which `x ∈ Kˣ` fails to be a local norm is never a singleton", i.e. Milne,
  *CFT*, VIII.2 Example 2.2(ii) (equivalently VII.8.1(a) / V.5.3(a)).

The point of splitting this off is that the deliverable's reduction
(`NK.CFTLib.IdeleHasse.localFaithful_onePlace_of_onePlace`, proved, in
`Submission/Work/CFTLib/IdeleHasse/localFaithful_onePlace.lean`) consumes exactly this statement, so
the arithmetic content can be delegated without importing the deliverable.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT

/-- The image of `x : Kˣ` in the completion of `K` at the place `v`. -/
def localImageAt {K : Type} [Field K] [NumberField K] (v : Place K) (x : Kˣ) :
    (Place.localField K v)ˣ :=
  Units.map (algebraMap K (Place.localField K v)).toMonoidHom x

/-- **Hilbert reciprocity for cyclic extensions of number fields, "one place omitted" form.**

A global element `x ∈ Kˣ` of a number field which is a local norm at every place of `K` except
possibly `v₀` is a local norm at `v₀` as well: *the set of places at which `x` fails to be a local
norm is never a singleton*.  Equivalently, the product `∏_v θ_v(x)` of the local Artin maps is
trivial on `Kˣ` (Milne, *CFT*, VII.8.1(a)), equivalently Hilbert's reciprocity law
`∑_v inv_v(x) = 0` (Milne, *CFT*, VII.8.1(b) / VIII.4).

This is the arithmetic content of the deliverable
`NK.CFTLib.IdeleHasse.onePlace_localFaithful`; the equivalence is proved in
`Submission/Work/CFTLib/IdeleHasse/localFaithful_onePlace.lean`
(`localFaithful_onePlace_of_onePlace`). -/
def HilbertReciprocityCyclic : Prop :=
  ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L)) (x : Kˣ)
    (v₀ : NK.GlobalCFT.Place K),
    (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.HassePrinciple.onePlace v
        (Units.map (algebraMap K (NK.GlobalCFT.Place.localField K v)).toMonoidHom x) ∈
        NK.GlobalCFT.Idele.normImage K L) →
    NK.HassePrinciple.onePlace v₀
      (Units.map (algebraMap K (NK.GlobalCFT.Place.localField K v₀)).toMonoidHom x) ∈
      NK.GlobalCFT.Idele.normImage K L

end NK.CFTLib.IdeleHasse
