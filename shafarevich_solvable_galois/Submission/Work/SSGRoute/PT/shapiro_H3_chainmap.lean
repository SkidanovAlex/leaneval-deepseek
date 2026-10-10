import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Defs.Basic
import Submission.Work.SSGRoute.PT.shapiro_H3_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Shapiro lifts are chain maps (degrees `2 → 3` and `3 → 4`)

For a subgroup `U ≤ G` and a `U`-module `M`, the Shapiro lifts (into the coinduced module
`Coind U G M`) commute with the cochain differentials:

* `shapiroLift_d2_apply` — `d² (Ψ₂ b) = Ψ₃ (d² b)` for a `2`-cochain `b` on `U`;
* `shapiroLift3_d3` — `d³ (Ψ₃ a) = Ψ₄ (d³ a)` for a `3`-cochain `a` on `U` (evaluated);
* `shapiroLift3_apply_one` — the diagonal evaluation `Ψ₃ a (u,v,w) 1 = a (u,v,w)`.

These are the degree-`3` analogues of `coindCocycle_d1_apply` (`shapiro_H2_inj`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-- **The degree-`2` Shapiro lift is a chain map**: `d² (Ψ₂ b) = Ψ₃ (d² b)`, evaluated at
`(g,h,k)` and the point `x`. -/
theorem shapiroLift_d2_apply (b : U × U → M) (g h k x : G) :
    (Work.GroupCohomology.d2 G (Coind G U M) (shapiroLift U b) (g, h, k) : G → M) x
      = coord U x • Work.GroupCohomology.d2 U M b (Shapiro.A 0 G U g (x : G ⧸ U),
          Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)),
          Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U))) := by
  simp only [Work.GroupCohomology.d2_apply, Coind.smul_apply, shapiroLift_apply,
    AddSubgroup.coe_add, AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply,
    coset_smul, coord_smul, A_mul', mul_smul, smul_sub, smul_add, mul_inv_rev]

/-- **The degree-`3` Shapiro lift is a chain map**: `d³ (Ψ₃ a) = Ψ₄ (d³ a)`, evaluated at
`(g,h,k,l)` and the point `x`. -/
theorem shapiroLift3_d3 (a : U × U × U → M) (g h k l x : G) :
    (Work.SSGRoute.d3 (G := G) (A := Coind G U M) (shapiroLift3 U a) (g, h, k, l) : G → M) x
      = coord U x • Work.SSGRoute.d3 (G := U) (A := M) a (Shapiro.A 0 G U g (x : G ⧸ U),
          Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)),
          Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)),
          Shapiro.A 0 G U l ((g * h * k)⁻¹ • (x : G ⧸ U))) := by
  letI : TopologicalSpace G := ⊥
  simp only [Work.SSGRoute.d3_apply, Coind.smul_apply, shapiroLift3_apply,
    AddSubgroup.coe_add, AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply,
    coset_smul, coord_smul, A_mul', mul_smul, smul_sub, smul_add, mul_inv_rev]

/-- The diagonal evaluation of the degree-`3` Shapiro lift: at a `U`-triple evaluated at the
identity of `G` it returns the original value. -/
theorem shapiroLift3_apply_one (a : U × U × U → M) (u v w : U) :
    (shapiroLift3 U a ((u : G), (v : G), (w : G)) : G → M) 1 = a (u, v, w) := by
  have hfix : (u : G)⁻¹ • ((1 : G) : G ⧸ U) = ((1 : G) : G ⧸ U) := by
    change (u : G)⁻¹ • Shapiro.basePoint 0 G U = Shapiro.basePoint 0 G U
    exact Shapiro.basePoint_smul_eq 0 G U u⁻¹
  have hfix2 : ((u : G) * (v : G))⁻¹ • ((1 : G) : G ⧸ U) = ((1 : G) : G ⧸ U) := by
    change ((u : G) * (v : G))⁻¹ • Shapiro.basePoint 0 G U = Shapiro.basePoint 0 G U
    exact Shapiro.basePoint_smul_eq 0 G U (((u * v)⁻¹ : U))
  have h1 : Shapiro.A 0 G U (u : G) (((1 : G)) : G ⧸ U) = u := by
    change Shapiro.A 0 G U (u : G) (Shapiro.basePoint 0 G U) = u
    exact A_basePoint U u
  have h2 : Shapiro.A 0 G U (v : G) ((u : G)⁻¹ • ((1 : G) : G ⧸ U)) = v := by
    rw [hfix]
    change Shapiro.A 0 G U (v : G) (Shapiro.basePoint 0 G U) = v
    exact A_basePoint U v
  have h3 : Shapiro.A 0 G U (w : G) (((u : G) * (v : G))⁻¹ • ((1 : G) : G ⧸ U)) = w := by
    rw [hfix2]
    change Shapiro.A 0 G U (w : G) (Shapiro.basePoint 0 G U) = w
    exact A_basePoint U w
  rw [shapiroLift3_apply, coord_one, h1, h2, h3, one_smul]

end

end Work.SSGRoute.PT
