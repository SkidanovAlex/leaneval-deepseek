/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abelian rank from local reciprocity (route (b))

The abelian-rank input of `NK.LocalInputs.Inputs`
(`LocalGaloisInputs.abelian_rank`: `NK.LocalAnabelian.HasAbelianFrattiniRank p (d+1+δ) (Gal(K'/κ))`)
is the classical local-class-field-theory computation

  `G_κ^{ab} ≅ κˣ^{∧} ≅ Ẑ × μ_κ × ℤ_p^{[κ:ℚ_p]}`,

i.e. the maximal elementary abelian `p`-quotient of `G_κ^{ab}` is `(ℤ/p)^{d+1+δ}` (there are
`(p^{d+1+δ}-1)/(p-1)` *cyclic* degree-`p` extensions of `κ`).

This file reduces the input to two clearly delimited pieces:

* the Lubin–Tate / existence input of local class field theory, isolated by the sibling area as
  `NK.LocalReciprocity.LocalReciprocityDatum` / `NK.LocalReciprocity.LubinTateInput`;
* the `p`-Frattini rank of the profinite completion of `κˣ`,
  `NK.LocalAnabelian.HasFrattiniRank p r (NK.LocalReciprocity.completionUnits κ)` — a purely
  *unit-group* statement (the arithmetic of `κˣ`), which for `κ = K_𝔭` is equivalent to the
  power-class count `|κˣ/(κˣ)^p| = p^r` (see `NK.LocalInputs.PowerQuotient`).

The transfer along the reciprocity isomorphism is
`NK.LocalReciprocity.hasFrattiniRank_maxAbelian_of_datum` (`Submission/Work/LocalReciprocity/Invariants.lean`),
and the passage from the maximal abelian subextension to the abelianisation of `Gal(K'/κ)` is
`NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian`.
-/
import Submission.NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen
import Submission.NK.LocalReciprocity.Invariants
import Submission.NK.LocalReciprocity.LubinTate

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
