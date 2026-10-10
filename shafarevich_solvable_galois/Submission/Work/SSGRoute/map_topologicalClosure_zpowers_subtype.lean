import Mathlib.Topology.Algebra.Group.Subgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The closure of a cyclic subgroup computed inside a closed subgroup is its closure in the
ambient group.**  Let `G` be a topological group, `D ≤ G` a closed subgroup and `σ ∈ D`.  Then the
image of the topological closure of `zpowers ⟨σ, hσ⟩` (computed in `↥D`) under the inclusion
`↥D → G` is the topological closure of `zpowers σ` (computed in `G`).

ROUTE.  `⊆`: `Subgroup.map` is monotone and `D.subtype` is continuous, so the image of the closure
is contained in the closure of the image.  `⊇`: the subgroup
`(closure (zpowers ⟨σ, hσ⟩)).map D.subtype` is closed in `G` — it is the image in `G` of a set
closed in `↥D` under the embedding `↥D → G` whose range `D` is closed — and it contains
`zpowers σ`; hence it contains `Subgroup.topologicalClosure (Subgroup.zpowers σ)`.  Useful
ingredients: `Subgroup.isClosed_topologicalClosure`, `Subgroup.le_topologicalClosure`,
`Subgroup.topologicalClosure_min`, `isClosed_induced_iff` and `IsClosed.preimage`
(`continuous_subtype_val`). -/
theorem map_topologicalClosure_zpowers_subtype {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (D : Subgroup G) (hD : IsClosed (D : Set G))
    (σ : G) (hσ : σ ∈ D) :
    (Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσ⟩ : ↥D))).map D.subtype =
      Subgroup.topologicalClosure (Subgroup.zpowers σ) := by
  refine le_antisymm ?_ ?_
  · -- The image of the closure is contained in the closure of the image.
    rw [Subgroup.map_le_iff_le_comap]
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · -- `zpowers ⟨σ, hσ⟩` maps into the closure of `zpowers σ`
      rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)
    · -- the preimage of a closed subgroup under the continuous inclusion is closed
      rw [Subgroup.coe_comap]
      exact (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val
  · -- The image of the closure is closed and contains `zpowers σ`
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · have h1 : Subgroup.zpowers σ = (Subgroup.zpowers (⟨σ, hσ⟩ : ↥D)).map D.subtype := by
        rw [MonoidHom.map_zpowers, Subgroup.subtype_apply]
      rw [h1]
      exact Subgroup.map_mono (Subgroup.le_topologicalClosure _)
    · have hcl : IsClosed
          ((Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσ⟩ : ↥D)) : Set ↥D)) :=
        Subgroup.isClosed_topologicalClosure _
      rw [Subgroup.coe_map]
      exact hD.isClosedMap_subtype_val _ hcl

end Work.SSGRoute
