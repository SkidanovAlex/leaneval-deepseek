import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
import Submission.NK.LocalReciprocityLubinTate.LubinTate.FormalGroup
import Submission.NK.LocalReciprocityLubinTate.LubinTate.existsUnique_lubinTate_solution
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ModuleStructure

/-!
# The Lubin–Tate module of a Lubin–Tate series

Milne, *Classical Field Theory*, §I.1 (Propositions I.2.12 and I.2.14): for a Lubin–Tate series
`f` for `(π, q)` over a commutative ring `A` there is a Lubin–Tate module structure on `A` whose
`π`-multiplication series is `f` itself.

The construction is carried out in `ModuleStructure.lean`: the group law is the unique formal
group law of `existsUnique_lubinTate_groupLaw` with `F ≡ X + Y (mod deg 2)` of which `f` is an
endomorphism, and the `A`-module structure `a ↦ [a]` is given by the `a`-multiplication series
`mulSeries` (`ModuleAux.lean`), the unique solution of `f ∘ φ = φ ∘ f` with `φ ≡ aX (mod deg 2)`.
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

theorem nonempty_lubinTateModule {A : Type u} [CommRing A] {π : A} {q : ℕ}
    (hπ : NK.LocalReciprocityLubinTate.IsLubinTateCoeff π q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower π q)
    {f : MvPowerSeries (Fin 1) A} (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f) :
    ∃ M : NK.LocalReciprocityLubinTate.LubinTateModule A π q, M.toLaw.piEndo = f :=
  nonempty_lubinTateModule' hπ hpow hf

end NK.LocalReciprocityLubinTate.LubinTate
