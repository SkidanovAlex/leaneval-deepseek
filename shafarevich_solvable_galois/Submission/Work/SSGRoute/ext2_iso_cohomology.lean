import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.GroupCohomology.Basic
import Submission.Work.SSGRoute.ext2_iso_cohomology_proof
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node `E1a/1`: `Ext²_G(R, X) ≅ H²(G, Hom_ℤ(R, X))` for a `ℤ`-lattice `R`

This is the first of the four pieces that `Work.SSGRoute.ext_sha2_bridge` (design node `E1a`,
`DESIGN_EXT.md`) needs: the `Ext`-cohomology dictionary in the **first** variable.

## Hypotheses (verified — the finite-`M` form is FALSE)

`R.V` must be a `ℤ`-lattice: free and finitely generated over `ℤ` (e.g. the syzygy `R` of a
presentation `0 → R → ℤ[G]^r → M → 0` for a finite `M`).  With merely finite `M` the statement
fails, as both reviewers of this node verified independently:

* `G = ℤ/2`, `M = X =` trivial rep on `ℤ/2`: `Hom_ℤ(ℤ/2,ℤ/2) = ℤ/2`, `H²(ℤ/2,ℤ/2) = ℤ/2 ≠ 0`,
  while `ℤ[ℤ/2] ≅ ℤ × ℤ` has global dimension `1`, so `Ext²_{ℤ[G]}(ℤ/2,ℤ/2) = 0`.
* `G = ℤ/2`, `M = (ℤ/2)_triv`, `X = ℤ_triv`: the right side is `0`, while
  `0 → ℤ →·2 ℤ → ℤ/2 → 0` gives `Ext²_{ℤ[G]}(ℤ/2,ℤ) ≅ ℤ/2 ≠ 0`.

Root cause: `Hom_ℤ(·,X)` is only exact on `0 → Hom(M,X) → Hom(F,X) → Hom(R,X) → 0` when `X` is
divisible (or the presentation splits over `ℤ`, impossible for torsion `M`) — this is why the
arithmetic step of `E1a` dualises into the divisible `Ω̄ˣ` first.

## Proof plan

`ℤ[G]`-modules are `Rep Coeff G`.  With `C_•` the bar resolution of the trivial module (Mathlib:
`Rep.barResolution`, a `ProjectiveResolution` of `Rep.trivial k G k`) and `R` `ℤ`-free, the complex
`R ⊗_ℤ C_•` (diagonal `G`-action) is a complex of free `ℤ[G]`-modules resolving
`R ⊗_ℤ ℤ = R`.  Hence
`Ext²_G(R,X) ≅ H²(Hom_G(R ⊗ C_•, X)) ≅ H²(Hom_G(C_•, Hom_ℤ(R,X)))` (tensor–hom adjunction,
`Hom_ℤ(R,X)` being the object supplied by `Submission.Work.SSGRoute.homRep`, with the conjugation
action) `≅ H²(G, Hom_ℤ(R,X))` (the standard resolution computes group cohomology;
`Rep.groupCohomologyIso` gives the identification with the bar resolution).

Needed ingredients, in order: the diagonal tensor product of two `Rep Coeff G`'s (Mathlib has no
monoidal structure on `Rep`); `R ⊗ ℤ[G]^k` is free; tensor–hom adjunction at the level of
`G`-invariants; `ProjectiveResolution.isoExt`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **Node `E1a/1`.**  For a group `G`, a `ℤ`-lattice `R` (a `Rep Coeff G` whose underlying abelian
group is free and finitely generated over `ℤ`) and any `Rep Coeff G` `X`:
`Ext²_{ℤ[G]}(R,X) ≅ H²(G, Hom_ℤ(R,X))`, the right-hand side being the group cohomology of the
internal `Hom` with the conjugation action (`Submission.Work.SSGRoute.homRep`). -/
theorem ext2_iso_cohomology (G : Type) [Group G] (R X : Rep.{0} Coeff G)
    [Module.Free ℤ R.V] [Module.Finite ℤ R.V] :
    Nonempty (CategoryTheory.Abelian.Ext R X 2 ≃+
      Work.GroupCohomology.H2 G (R.V →ₗ[Coeff] X.V)) :=
  ext2_iso_cohomology_proof G R X

end Work.SSGRoute
