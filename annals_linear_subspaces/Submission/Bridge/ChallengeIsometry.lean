import ChallengeDeps
import Submission.Bridge.Challenge
import Submission.Bridge.Isometry

/-!
# Isometry invariance of the challenge distance `distSubspaces` (`finrank v ≤ finrank x`)

The challenge distance `LinearSubspaces.distSubspaces v x` is invariant under applying a
linear isometry `g` of `ℝᵈ` to both subspaces (`finrank v ≤ finrank x`, both nonzero):

    `distSubspaces (v.map g) (x.map g) = distSubspaces v x`

Proof: both sides reduce, through the distance bridge
(`Submission.Bridge.distSubspaces_eq_planeResidual_of_le`), to the operator-norm residual
`planeResidual`, whose simultaneous-transport invariance is
`Submission.Bridge.Isometry.planeResidual_map_map`; the finrank / nonzero hypotheses
transport because `g` is a linear equivalence (`LinearEquiv.finrank_map_eq`,
`map = ⊥ ↔ source = ⊥`).

This is the transport lemma of the general-`x` layer (item F): approximating the plane
`x = g⁻¹(x₀)` by rational `k`-planes is equivalent — by transporting along `g` — to
approximating the coordinate plane `x₀` by planes in the transported lattice `g(ℤᵈ)`;
the distance side is exactly this invariance.

Challenge-side module (imports ChallengeDeps); zero sorry/axioms.
-/

noncomputable section

open Module Real InnerProductGeometry
open LinearSubspaces
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Bridge.Isometry

variable {d : ℕ}
abbrev RD (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- A nonzero submodule maps to a nonzero submodule under a linear equivalence (and
conversely). -/
lemma map_ne_bot_iff {E F : Type*} [AddCommGroup E] [AddCommGroup F] [Module ℝ E] [Module ℝ F]
    (g : E ≃ₗ[ℝ] F) (V : Submodule ℝ E) :
    V.map (g : E →ₗ[ℝ] F) ≠ ⊥ ↔ V ≠ ⊥ := by
  constructor
  · intro h hV
    apply h
    simp [hV]
  · intro hV hmap
    apply hV
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hgx : g x ∈ V.map (g : E →ₗ[ℝ] F) := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have hbot : g x = 0 := by
      rw [hmap] at hgx
      exact (Submodule.mem_bot ℝ).mp hgx
    exact (g.map_eq_zero_iff.mp hbot)

/-- **`distSubspaces` is invariant under a simultaneous linear isometry** of both
subspaces, for `finrank v ≤ finrank x` and both subspaces nonzero:
`distSubspaces (v.map g) (x.map g) = distSubspaces v x`. -/
theorem distSubspaces_map (v x : Submodule ℝ (RD d)) (g : RD d ≃ₗᵢ[ℝ] RD d)
    (hkl : finrank ℝ v ≤ finrank ℝ x) (hvn : v ≠ ⊥) (hxn : x ≠ ⊥) :
    LinearSubspaces.distSubspaces (v.map (g : RD d →ₗ[ℝ] RD d))
        (x.map (g : RD d →ₗ[ℝ] RD d)) =
      LinearSubspaces.distSubspaces v x := by
  classical
  let hg : RD d ≃ₗ[ℝ] RD d := g.toLinearEquiv
  have hfrV : Module.finrank ℝ (v.map (g : RD d →ₗ[ℝ] RD d)) = Module.finrank ℝ v := by
    calc
      Module.finrank ℝ (v.map (g : RD d →ₗ[ℝ] RD d))
          = Module.finrank ℝ (v.map (hg : RD d →ₗ[ℝ] RD d)) := by
            congr 1
      _ = Module.finrank ℝ v := by
            simpa [hg] using (hg.finrank_map_eq v)
  have hfrX : Module.finrank ℝ (x.map (g : RD d →ₗ[ℝ] RD d)) = Module.finrank ℝ x := by
    calc
      Module.finrank ℝ (x.map (g : RD d →ₗ[ℝ] RD d))
          = Module.finrank ℝ (x.map (hg : RD d →ₗ[ℝ] RD d)) := by
            congr 1
      _ = Module.finrank ℝ x := by
            simpa [hg] using (hg.finrank_map_eq x)
  have hkl' : finrank ℝ (v.map (g : RD d →ₗ[ℝ] RD d)) ≤
      finrank ℝ (x.map (g : RD d →ₗ[ℝ] RD d)) := by
    rw [hfrV, hfrX]
    exact hkl
  have hvn' : v.map (g : RD d →ₗ[ℝ] RD d) ≠ ⊥ := by
    have h' : v.map (hg : RD d →ₗ[ℝ] RD d) ≠ ⊥ := (map_ne_bot_iff hg v).mpr hvn
    simpa [hg] using h'
  have hxn' : x.map (g : RD d →ₗ[ℝ] RD d) ≠ ⊥ := by
    have h' : x.map (hg : RD d →ₗ[ℝ] RD d) ≠ ⊥ := (map_ne_bot_iff hg x).mpr hxn
    simpa [hg] using h'
  calc
    LinearSubspaces.distSubspaces (v.map (g : RD d →ₗ[ℝ] RD d))
        (x.map (g : RD d →ₗ[ℝ] RD d))
        = Submission.ProjectionDistance.planeResidual (v.map (g : RD d →ₗ[ℝ] RD d))
            (x.map (g : RD d →ₗ[ℝ] RD d)) :=
          Submission.Bridge.distSubspaces_eq_planeResidual_of_le
            (v.map (g : RD d →ₗ[ℝ] RD d)) (x.map (g : RD d →ₗ[ℝ] RD d)) hkl' hvn' hxn'
    _ = Submission.ProjectionDistance.planeResidual v x :=
          Submission.Bridge.Isometry.planeResidual_map_map v x g
    _ = LinearSubspaces.distSubspaces v x :=
          (Submission.Bridge.distSubspaces_eq_planeResidual_of_le v x hkl hvn hxn).symm

/-- **Upper-bound form** (all the Dirichlet direction needs): applying an isometry to both
subspaces does not increase the challenge distance:
`distSubspaces (v.map g) (x.map g) ≤ distSubspaces v x` (in fact equality). -/
theorem distSubspaces_map_le (v x : Submodule ℝ (RD d)) (g : RD d ≃ₗᵢ[ℝ] RD d)
    (hkl : finrank ℝ v ≤ finrank ℝ x) (hvn : v ≠ ⊥) (hxn : x ≠ ⊥) :
    LinearSubspaces.distSubspaces (v.map (g : RD d →ₗ[ℝ] RD d))
        (x.map (g : RD d →ₗ[ℝ] RD d)) ≤
      LinearSubspaces.distSubspaces v x := by
  rw [distSubspaces_map v x g hkl hvn hxn]

end Submission.Bridge.Isometry

end
