import Mathlib.Topology.Algebra.Group.Quotient
import Submission.Work.SSGRoute.PT.isOpen_setOf_inv_smul_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the Shapiro coordinates, valued in the open subgroup `U`

For a topological group `G` and an **open** subgroup `U ≤ G`, the coset space `G ⧸ U` is
discrete (`QuotientGroup.discreteTopology`).  Hence the chosen section `Shapiro.sec 0 G U` of the
coset projection is continuous, and the `U`-coordinates

  `A g C = (sec C)⁻¹ * g * sec (g⁻¹ • C)`

are continuous in `(g, C)`: this is `Work.SSGRoute.PT.continuous_shapiroCoordinates`, the
`G`-valued statement.  Here we record the statement for the *subtype* `U × U`: a map `G × G → U × U`
is continuous iff its two `G`-valued components are, as `U ↪ G` is an embedding.

This is the topological input making the Shapiro cochain `coindCocycle U φ` a continuous cocycle.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

/-- The `G`-valued Shapiro coordinate map `p ↦ (A p.1 C, A p.2 (p.1⁻¹ • C))` is continuous.
Since `U` is open the coset space `G ⧸ U` is discrete, so the section `sec` is continuous, and the
coordinate expressions are built from `sec`, the group operations and the continuous coset action. -/
theorem continuous_shapiroCoordinates_G {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (C : G ⧸ U) :
    Continuous fun p : G × G =>
      ((Work.SSGRoute.Shapiro.A 0 G U p.1 C : G),
       (Work.SSGRoute.Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G)) := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have hsec : Continuous (fun x : G ⧸ U => Work.SSGRoute.Shapiro.sec 0 G U x) :=
    continuous_of_discreteTopology
  have hfst : Continuous (fun p : G × G => (Work.SSGRoute.Shapiro.A 0 G U p.1 C : G)) := by
    rw [show (fun p : G × G => (Work.SSGRoute.Shapiro.A 0 G U p.1 C : G))
        = fun p =>
            (Work.SSGRoute.Shapiro.sec 0 G U C)⁻¹ * p.1
              * Work.SSGRoute.Shapiro.sec 0 G U (p.1⁻¹ • C) from by
      funext p; exact Work.SSGRoute.Shapiro.coe_A 0 G U p.1 C]
    exact ((continuous_const.mul continuous_fst).mul
      (hsec.comp (continuous_fst.inv.smul continuous_const)))
  have hsnd : Continuous (fun p : G × G => (Work.SSGRoute.Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G)) := by
    rw [show (fun p : G × G => (Work.SSGRoute.Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G))
        = fun p =>
            (Work.SSGRoute.Shapiro.sec 0 G U (p.1⁻¹ • C))⁻¹ * p.2
              * Work.SSGRoute.Shapiro.sec 0 G U (p.2⁻¹ • (p.1⁻¹ • C)) from by
      funext p; exact Work.SSGRoute.Shapiro.coe_A 0 G U p.2 (p.1⁻¹ • C)]
    exact ((hsec.comp (continuous_fst.inv.smul continuous_const)).inv.mul continuous_snd).mul
      (hsec.comp ((continuous_snd.inv).smul (continuous_fst.inv.smul continuous_const)))
  exact Continuous.prodMk hfst hsnd

theorem continuous_shapiroCoordinates_subtype {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (C : G ⧸ U) :
    Continuous fun p : G × G =>
      ((Work.SSGRoute.Shapiro.A 0 G U p.1 C, Work.SSGRoute.Shapiro.A 0 G U p.2 (p.1⁻¹ • C))
        : U × U) := by
  have H := continuous_shapiroCoordinates_G U hU C
  exact Continuous.prodMk
    (H.fst.subtype_mk (fun p => (Work.SSGRoute.Shapiro.A 0 G U p.1 C).2))
    (H.snd.subtype_mk (fun p => (Work.SSGRoute.Shapiro.A 0 G U p.2 (p.1⁻¹ • C)).2))

end Work.SSGRoute.PT
