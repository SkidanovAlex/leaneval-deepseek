/-
Copyright: subproject `OROneRel`.

Shared setup for the transport of the Freiheitssatz along an injective relabelling of the generators
(`Work.OROneRel.freiheitssatzAt_of_restrict`): the two-element family of groups and its group
instance, used to phrase the splitting `⟨γ | s⟩ ≃* ⟨Z | sz⟩ ∗ F(γ \ Z)` in the indexed-coproduct
form `Monoid.CoprodI`.
-/
import Mathlib

namespace Work.OROneRel

universe u

/-- The two-element family of types with `true ↦ M` and `false ↦ N`.  (Its definitional unfolding
makes `Monoid.CoprodI (CoprodTwoFam M N)` the "binary free product written as an indexed
coproduct", for which Mathlib's normal-form theory `Monoid.CoprodI.Word` is available.) -/
abbrev CoprodTwoFam (M N : Type u) : Bool → Type u := fun b => cond b M N

instance instGroupCoprodTwoFam {M N : Type u} [Group M] [Group N] :
    (b : Bool) → Group (CoprodTwoFam M N b)
  | true => inferInstanceAs (Group M)
  | false => inferInstanceAs (Group N)

end Work.OROneRel
