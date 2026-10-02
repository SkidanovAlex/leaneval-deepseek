import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.lhMap_comap
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.LerayHirsch.lerayHirschGlueProof

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The Mayer–Vietoris rung of the Leray–Hirsch induction

This is the deliverable `Work.LerayHirsch.lerayHirschGlue`: the **Mayer–Vietoris rung** of the
Leray–Hirsch induction for the projectivisation of a complex gluing-data bundle
(`Work.LerayHirsch.LerayHirschGlue`, stated in `Submission/Work/LerayHirsch/LH.lean`).

The statement says: for a complex bundle `Z` over a base `B` and a finite open cover
`U : ιc → Set B` of `B`, if `H^*(P(E);ℤ)` is free over `H^*(B;ℤ)` on `1, ζ, …, ζ^{m-1}` after
restricting to `U_S = ⋂_{k ∈ S} U_k` for every nonempty finite `S` (i.e. `LerayHirschFull` holds for
`Z|_{U_S}`), then it holds for `Z` itself.

The mathematical content is the usual one: the two-piece case is the ladder comparison of the
Mayer–Vietoris long exact sequence of the cover `(π⁻¹U, π⁻¹V)` of `P(E)` with the
`ζ`-tensored Mayer–Vietoris sequence of the base, via the five lemma; the general finite cover is
then an induction over the members of the cover, in which the overlap of one piece with the union
of the others is again a union of pairwise intersections of the cover, so that the hypothesis
applies.

The proof is provided by `Work.LerayHirsch.lerayHirschGlueProof`
(`Submission/Work/LerayHirsch/lerayHirschGlueProof.lean`), whose proof runs on the ladder set up in
`Submission/Work/LerayHirsch/LhTwoCoverDefs.lean` (the two-piece Mayer–Vietoris ladders), with
`Work.LerayHirsch.Mv_exact` for the exactness of the base ladder, the three ladder squares of
`Submission/Work/LerayHirsch/MvSquares.lean` together with the comparison maps of
`Submission/Work/LerayHirsch/MvTM_translate.lean` and
`Submission/Work/LerayHirsch/MvPieceTranslate.lean`, the piece identification
`Submission/Work/LerayHirsch/MvPieceIso.lean`
(`P(Z|_U) ≅ π⁻¹U`, via `Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype`), the
naturality `Work.LerayHirsch.lhMap_comap`/`Work.LerayHirsch.zetaPow_comap` of `π^*` and of the
powers of `ζ`, the bridge `Work.LerayHirsch.lhAny_bijective_iff` between the even/odd Leray–Hirsch
maps and the uniform one used by the ladder, the three exactness spots of the honest relative
Mayer–Vietoris sequence (`Work.Cohomology.honest_exact₁/₂/₃`) for the total space side, and the
five lemma `Work.Thom.five_lemma_LES'`.  The two-set rung is
`Work.LerayHirsch.lerayHirschFull_of_two_cover`
(`Submission/Work/LerayHirsch/lerayHirschFull_of_two_cover.lean`), and the empty-piece/empty-base
cases are `Work.LerayHirsch.lerayHirschFull_of_isEmpty`.
-/

namespace Work.LerayHirsch

/-- **The Mayer–Vietoris rung of the Leray–Hirsch induction** — see the module docstring. -/
theorem lerayHirschGlue : Work.LerayHirsch.LerayHirschGlue := lerayHirschGlueProof

end Work.LerayHirsch
