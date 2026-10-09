import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_H3_defs
import Submission.Work.SSGRoute.PT.shapiro_H3_chainmap
import Submission.Work.SSGRoute.PT.shapiro_H3_homotopy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The primitive of a `3`-cocycle whose restriction is a coboundary

`h3Primitive_d2` is the degree-`3` analogue of `h2Primitive_d1` (`shapiro_H2_inj`): if `c` is a
`3`-cocycle of `G` with values in `Coind U G M` whose restriction to `U` is the coboundary `d² b`
of a `2`-cochain `b` of `U`, then `d² (h3Primitive U b c) = c`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

theorem h3Primitive_d2 {b : U × U → M} {c : G × G × G → Coind G U M}
    (hc : c ∈ Work.SSGRoute.Z3 (M := Coind G U M) G)
    (hb : ∀ u v w : U, Work.GroupCohomology.d2 U M b (u, v, w)
        = (c ((u : G), (v : G), (w : G)) : G → M) 1) :
    Work.GroupCohomology.d2 G (Coind G U M) (h3Primitive U b c) = c := by
  funext p
  obtain ⟨g, h, k⟩ := p
  apply Subtype.ext
  funext x
  have h1 := shapiroLift_d2_apply U b g h k x
  have h2 := s2c_d2_apply U hc g h k x
  rw [h3Primitive, map_add]
  simp only [Pi.add_apply, AddSubgroup.coe_add]
  rw [h1, h2]
  rw [hb (Shapiro.A 0 G U g (x : G ⧸ U)) (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)))
    (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)))]
  abel

end

end Work.SSGRoute.PT
