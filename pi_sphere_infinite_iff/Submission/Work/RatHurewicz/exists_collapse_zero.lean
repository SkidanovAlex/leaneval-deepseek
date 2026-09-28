import Mathlib
import Submission.Work.RatHurewicz.AssemblyDefs
import Submission.Work.ThomBordism.TwoSet.CubeCollapse
import Submission.Work.RatHurewicz.Collapse.Defs
import Submission.Work.RatHurewicz.Collapse.exists_sphereToBdy
import Submission.Work.RatHurewicz.Collapse.exists_onePointHomeo
import Submission.Work.Stems.exists_collapsingMap

/-!
# The collapse of the cube `I^{m+2}` onto the boundary of `I^{m+3}` at its corner

The map is the composite

`I^{m+2} --cubeToOnePoint--> OnePoint ℝ^{m+2} --≃--> S^{m+2} --radial--> ∂I^{m+3}`

of the one-point collapse of the boundary of the cube (`∂I^{m+2} ↦ ∞`, injective off `∂I^{m+2}`),
the inverse stereographic homeomorphism of the one-point compactification with the round sphere
(sending `∞` to the corner direction), and the ℓ∞-radial projection of the sphere onto `∂I^{m+3}`
(sending the corner direction to the corner `(0,…,0)`), which is injective.

The properties of the target statement are then immediate from the corresponding properties of the
three factors: `∂I^{m+2}` is collapsed to the corner `0`, the only points mapping to `0` are the
points of `∂I^{m+2}`, and the composite is injective off `∂I^{m+2}`.
-/

namespace Work.RatHurewicz

open scoped unitInterval Topology
open Work.Stems.Cubical

/-- The corner `(0,…,0)` of `I^{m+3}` is a point of the boundary. -/
theorem mem_boundary_zero_IC (m : ℕ) : (0 : IC (m + 3)) ∈ Cube.boundary (Fin (m + 3)) :=
  ⟨(0 : Fin (m + 3)), Or.inl rfl⟩

theorem exists_collapse_zero (m : ℕ) :
    ∃ φ : C(Work.Stems.Cubical.IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))),
      (∀ u ∈ Cube.boundary (Fin (m + 2)), (φ u : Work.Stems.Cubical.IC (m + 3)) = 0) ∧
      (∀ u : Work.Stems.Cubical.IC (m + 2),
        (φ u : Work.Stems.Cubical.IC (m + 3)) = 0 → u ∈ Cube.boundary (Fin (m + 2))) ∧
      (∀ u v : Work.Stems.Cubical.IC (m + 2),
        u ∉ Cube.boundary (Fin (m + 2)) → φ u = φ v → u = v) := by
  obtain ⟨Φ, hΦinj, hΦc⟩ := Work.RatHurewicz.Collapse.exists_sphereToBdy (m + 2)
  obtain ⟨e, he⟩ := Work.RatHurewicz.Collapse.exists_onePointHomeo (m + 2)
  refine ⟨⟨fun u => Φ (e (Work.Stems.cubeToOnePoint (m + 2) u)),
    Φ.continuous.comp (e.continuous.comp
      (Work.Stems.cubeToOnePoint_continuous (m + 2)))⟩, ?_, ?_, ?_⟩
  · intro u hu
    have h1 : Work.Stems.cubeToOnePoint (m + 2) u = OnePoint.infty :=
      Work.Stems.cubeToOnePoint_eq_infty_of_mem_boundary hu
    change ((Φ (e (Work.Stems.cubeToOnePoint (m + 2) u)) :
      ↥(Cube.boundary (Fin (m + 3)))) : IC (m + 3)) = 0
    rw [h1, he, hΦc, Work.RatHurewicz.Collapse.cornerBdy_coe]
  · intro u hu
    have h2 : Φ (e (Work.Stems.cubeToOnePoint (m + 2) u)) =
        Work.RatHurewicz.Collapse.cornerBdy (m + 2) := by
      apply Subtype.ext
      have hu' : ((Φ (e (Work.Stems.cubeToOnePoint (m + 2) u)) :
        ↥(Cube.boundary (Fin (m + 3)))) : IC (m + 3)) = 0 := hu
      rw [hu', Work.RatHurewicz.Collapse.cornerBdy_coe]
    have h3 : e (Work.Stems.cubeToOnePoint (m + 2) u) =
        Work.RatHurewicz.Collapse.cornerPt (m + 2) := hΦinj (h2.trans hΦc.symm)
    have h4 : Work.Stems.cubeToOnePoint (m + 2) u = OnePoint.infty := by
      have h5 : e (Work.Stems.cubeToOnePoint (m + 2) u) = e OnePoint.infty := by
        rw [he]; exact h3
      exact e.injective h5
    by_contra hq
    rw [Work.Stems.cubeToOnePoint_eq_coe_of_not_mem_boundary hq] at h4
    exact OnePoint.coe_ne_infty _ h4
  · intro u v hu h
    have h1 : Φ (e (Work.Stems.cubeToOnePoint (m + 2) u)) =
        Φ (e (Work.Stems.cubeToOnePoint (m + 2) v)) := h
    have h2 : e (Work.Stems.cubeToOnePoint (m + 2) u) =
        e (Work.Stems.cubeToOnePoint (m + 2) v) := hΦinj h1
    have h3 : Work.Stems.cubeToOnePoint (m + 2) u =
        Work.Stems.cubeToOnePoint (m + 2) v := e.injective h2
    rcases Work.Stems.cubeToOnePoint_fibers (m + 2) h3 with h4 | ⟨h4, _⟩
    · exact h4
    · exact absurd h4 hu

end Work.RatHurewicz
