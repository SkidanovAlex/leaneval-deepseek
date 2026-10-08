import Mathlib
import Submission.Work.ThompsonFrobenius.BlueprintZJ
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `N_G(P) ≤ N_G(Z(J(P)))`

`Submission.Blueprint.ZJ P = J(P) ∩ C_G(J(P))` is the centre of the Thompson subgroup of `P`.
The Thompson subgroup is built from the abelian subgroups of `P` of maximal order, so it is
*characteristic* in `P`: any `g` normalizing `P` permutes those abelian subgroups (conjugation
is an isomorphism, hence preserves commutativity and cardinality), and therefore fixes their
supremum `J(P)`.  Passing to the centre preserves invariance under conjugation, so `Z(J(P))` is
characteristic in `P` as well and `N_G(P) ≤ N_G(Z(J(P)))`.

Both steps are already available for the `Work.PGroup` models in
`Work.PGroup.thompsonJ_characteristic` / `Work.PGroup.ZJ_characteristic`, and the bridge
`Work.GlaubermanZJ.ZJ_eq` identifies `Submission.Blueprint.ZJ P` with `Work.PGroup.ZJ P`.
-/

namespace Work.ThompsonFrobenius

/-- The normalizer of `P` is contained in the normalizer of `Z(J(P))`: `Z(J(P))` is
characteristic in `P`. -/
theorem normalizer_le_normalizer_ZJ {G : Type*} [Group G] [Finite G] (P : Subgroup G) : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Submission.Blueprint.ZJ P : Set G) := by
  intro g hg
  -- Rewrite membership in the normalizer as invariance of the subgroup under `MulAut.conj g`.
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  -- Replace the blueprint's `ZJ` by the `Work.PGroup` model, for which characteristicity is
  -- already proved.
  rw [Work.GlaubermanZJ.ZJ_eq P]
  have hchar := Work.PGroup.ZJ_characteristic P g hg
  rwa [Work.PGroup.conjBy, Subgroup.pointwise_smul_def] at hchar

end Work.ThompsonFrobenius
