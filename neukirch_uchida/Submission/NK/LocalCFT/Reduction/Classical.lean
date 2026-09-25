import Submission.NK.LocalCFT.Reduction.Defs
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw
import Submission.NK.LocalCFT.Reduction.existenceTheorem_of_abstract

/-!
# The corrected Lubin–Tate input from the two classical inputs

The two halves of local class field theory, in their classical form, are

* `NK.LocalCFT.ReciprocityLaw F F'` — the canonical *compatible* reciprocity isomorphisms
  `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` at the finite abelian levels of `F^{ab}` (Lubin–Tate formal groups
  plus Honda's explicit reciprocity law, or an equivalent route);
* `NK.LocalCFT.ExistenceTheoremAbstract F` — the *existence theorem*: every finite-index subgroup
  of `Fˣ` contains the norm group of a finite abelian extension of `F` (Lubin–Tate's existence
  theorem, i.e. the fact that the abelian extensions of `F` are as numerous as the finite quotients
  of `Fˣ` allow).

This file records that together they give the corrected reciprocity datum, i.e. the corrected
`LubinTateInput` of `Submission/Work/LocalReciprocity/LubinTate.lean` (with the target of the Artin
map corrected from `Gal(F'/F)` to `Gal(F^{ab}/F)`; see `README.md`).
-/

open scoped Classical

namespace NK.LocalCFT

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']

/-- **The corrected Lubin–Tate input from the reciprocity law and the abstract existence theorem.**
This is the form in which the two classical theorems of local class field theory (Lubin–Tate) are
consumed: no separate Artin map has to be produced, and no condition on the non-abelian quotients of
`G_F` is imposed. -/
theorem nonempty_artinReciprocity_of_classical {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsSepClosure F F'] (hlaw : ReciprocityLaw F F')
    (hex : ExistenceTheoremAbstract F) :
    Nonempty (ArtinReciprocity F F') :=
  haveI : IsGalois F F' := inferInstance
  NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw hlaw
    (NK.LocalCFT.Reduction.existenceTheorem_of_abstract hex)

/-- The same, stated as the corrected `LubinTateInput`. -/
theorem lubinTateInput_of_classical {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsSepClosure F F'] (hlaw : ReciprocityLaw F F')
    (hex : ExistenceTheoremAbstract F) :
    LubinTateInput F F' :=
  nonempty_artinReciprocity_of_classical hlaw hex

end NK.LocalCFT
