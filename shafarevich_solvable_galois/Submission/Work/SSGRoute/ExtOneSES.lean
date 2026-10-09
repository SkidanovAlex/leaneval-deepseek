import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ExtOneDefs
import Submission.Work.SSGRoute.ExtOnePre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dual short complex of the internal hom

For a short complex `S : 0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` and a `G`-module `N`, applying
the (contravariant, exact) functor `Hom_ℤ(-,N)` — the internal hom `Work.SSGRoute.homRep` of
`Submission.Work.SSGRoute.homRep` — gives the short complex

`0 → Hom_ℤ(X₃,N) → Hom_ℤ(X₂,N) → Hom_ℤ(X₁,N) → 0`.

The maps are the precomposition maps `Work.SSGRoute.homRepPre`.  This file only defines the short
complex; the substantive fact (that it is *short exact* when `N` is divisible, i.e. an injective
`ℤ`-module) is proved elsewhere.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

noncomputable section

variable {G : Type} [Group G]

/-- The short complex obtained by applying the internal hom `Hom_ℤ(-,N)` to a short complex
`S : 0 → X₁ → X₂ → X₃ → 0`.  It is `0 → Hom(X₃,N) → Hom(X₂,N) → Hom(X₁,N) → 0`. -/
noncomputable def homRepShortComplex (S : ShortComplex (Rep.{0} Coeff G))
    (N : Rep.{0} Coeff G) : ShortComplex (Rep.{0} Coeff G) :=
  ShortComplex.mk (homRepPre S.X₃ S.X₂ N S.g) (homRepPre S.X₂ S.X₁ N S.f) (by
    rw [homRepPre_comp S.X₃ S.X₂ S.X₁ N S.g S.f, S.zero]
    exact homRepPre_zero S.X₃ S.X₁ N)

@[simp] lemma homRepShortComplex_X₁ (S : ShortComplex (Rep.{0} Coeff G)) (N : Rep.{0} Coeff G) :
    (homRepShortComplex S N).X₁ = homRep S.X₃ N := rfl

@[simp] lemma homRepShortComplex_X₂ (S : ShortComplex (Rep.{0} Coeff G)) (N : Rep.{0} Coeff G) :
    (homRepShortComplex S N).X₂ = homRep S.X₂ N := rfl

@[simp] lemma homRepShortComplex_X₃ (S : ShortComplex (Rep.{0} Coeff G)) (N : Rep.{0} Coeff G) :
    (homRepShortComplex S N).X₃ = homRep S.X₁ N := rfl

lemma homRepShortComplex_f (S : ShortComplex (Rep.{0} Coeff G)) (N : Rep.{0} Coeff G) :
    (homRepShortComplex S N).f = homRepPre S.X₃ S.X₂ N S.g := rfl

lemma homRepShortComplex_g (S : ShortComplex (Rep.{0} Coeff G)) (N : Rep.{0} Coeff G) :
    (homRepShortComplex S N).g = homRepPre S.X₂ S.X₁ N S.f := rfl

end

end Work.SSGRoute
