import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.LocalInputs

/-
The openness hypothesis `hopen` is needed because `Gal(maxAbelianSubext κ K'/κ)` is the
*topological* abelianisation of `Gal(K'/κ)`, while `HasAbelianFrattiniRank` refers to the
*abstract* abelianisation: the two agree on index-`p` subgroups exactly when index-`p` normal
subgroups of `Gal(K'/κ)` are open.  For `κ` a `p`-adic field this holds, since `Gal(κ̄/κ)` is
topologically finitely generated and every finite-index subgroup of such a group is open
(Nikolov–Segal).  See
`NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen` and the warning in
`Submission/Work/LocalInputs/AbelianRank/Hints.lean`.

**Do not drop `hopen`**: without it the statement is false (algebraic vs. topological
abelianisation).
-/

/-- **The abelian rank from the reciprocity datum.**  If the canonical reciprocity isomorphisms
exist for `κ` (the Lubin–Tate input), every index-`p` normal subgroup of `Gal(K'/κ)` is open, and
the profinite completion of `κˣ` has `p`-Frattini rank `r`, then `Gal(K'/κ)^{ab}` has
`p`-Frattini rank `r`. -/
theorem hasAbelianFrattiniRank_of_lubinTate {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsGalois κ K'] (D : NK.LocalReciprocity.LocalReciprocityDatum κ K') {p r : ℕ}
    (hopen : ∀ H : Subgroup (Gal(K'/κ)), H.index = p → H.Normal →
      IsOpen (H : Set (Gal(K'/κ))))
    (h : NK.LocalAnabelian.HasFrattiniRank p r (NK.LocalReciprocity.completionUnits κ)) :
    NK.LocalAnabelian.HasAbelianFrattiniRank p r (Gal(K'/κ)) :=
  AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen hopen
    (NK.LocalReciprocity.hasFrattiniRank_maxAbelian_of_datum D h)

/-- **The abelian rank from the Lubin–Tate input.**  Same as `hasAbelianFrattiniRank_of_lubinTate`
with the existence of the reciprocity datum as a proposition, which is the exact form isolated in
`NK.LocalReciprocity.LubinTateInput`. -/
theorem hasAbelianFrattiniRank_of_lubinTateInput {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] (hLT : NK.LocalReciprocity.LubinTateInput κ K') {p r : ℕ}
    (hopen : ∀ H : Subgroup (Gal(K'/κ)), H.index = p → H.Normal →
      IsOpen (H : Set (Gal(K'/κ))))
    (h : NK.LocalAnabelian.HasFrattiniRank p r (NK.LocalReciprocity.completionUnits κ)) :
    NK.LocalAnabelian.HasAbelianFrattiniRank p r (Gal(K'/κ)) :=
  hasAbelianFrattiniRank_of_lubinTate (Classical.choice hLT) hopen h

end NK.LocalInputs
