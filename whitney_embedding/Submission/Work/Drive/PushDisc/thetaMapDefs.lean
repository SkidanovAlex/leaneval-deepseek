import Mathlib
import Submission.Work.Drive.Whitney.modelChart
import Submission.Work.Drive.PushDisc.sheetModel

/-!
# The `θ` of the framing assembly, and its row on the plane `{u = 0, v = 0}`

`Work.Drive.PushDisc.thetaMap` is the explicit map of the lead's assembly
(`NOTES_LEAD_L0.md`, `NOTES_H344_ASSEMBLY_DESIGN.md` §2):

    θ (x,y,u,v) = Δ (x,y) + Σᵢ uᵢ • Uᵢ (x,y) + Σⱼ (r vⱼ) • Wⱼ (x,y)
                   + [ S₂ (x, r • v) - Δ (x, c x) - (fderiv ℝ (fun v => S₂ (x,v)) 0) (r • v) ]

with `Δ` the disc approximation (L0), `S₂` the finger's chart image (`Φ₀ ∘ f ∘ σ₂`), `U` the
`u`-frame (F1), `W` the `v`-frame (F2) and `c` the arch.

The row proved here is the one that transmits the *first sheet* through the assembly:
`thetaMap_plane` says `θ (x,0,u,0) = (x,0,u,0)`.  It is stated with the identity
`Σᵢ uᵢ • ιuᵢ = (0,0,u,0)` for the chosen `u`-frame as a hypothesis (that is exactly (F1) plus the
definition of the standard frame; `sum_smul_iotaU` proves it for the standard basis `iotaU`).
-/

namespace Work.Drive.PushDisc

open scoped ContDiff

/-- The `θ` of the framing assembly.  See the module docstring. -/
noncomputable def thetaMap {k : ℕ} (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k) (c : ℝ → ℝ) (r : ℝ)
    (ξ : Work.Drive.Whitney.Mdl k) : Work.Drive.Whitney.Mdl k :=
  Δ (ξ.1, ξ.2.1)
    + (∑ i : Fin k, ξ.2.2.1 i • U (ξ.1, ξ.2.1) i)
    + (∑ j : Fin k, (r * ξ.2.2.2 j) • W (ξ.1, ξ.2.1) j)
    + (S₂ (ξ.1, r • ξ.2.2.2) - Δ (ξ.1, c ξ.1)
        - (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, v)) 0) (r • ξ.2.2.2))

/-- **The plane row of `θ`.**  Given (F1) in the form `Σᵢ uᵢ • ιuᵢ = (0,0,u,0)` (the standard frame,
`sum_smul_iotaU` below), the `x`-axis row `Δ (x,0) = (x,0,0,0)` and the top-edge agreement
`S₂ (x,0) = Δ (x, c x)`, the map `θ` fixes the plane `{y = 0, v = 0}`:
`θ (x,0,u,0) = (x,0,u,0)`. -/
theorem thetaMap_plane {k : ℕ} (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k) (c : ℝ → ℝ) (r : ℝ)
    (ιu : Fin k → Work.Drive.Whitney.Mdl k)
    (hιu : ∀ u : EuclideanSpace ℝ (Fin k),
      (∑ i : Fin k, u i • ιu i) = (0, 0, u, 0))
    (hΔ : ∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0))
    (hU : ∀ x : ℝ, U (x, 0) = ιu)
    (hS₂ : ∀ x : ℝ, S₂ (x, 0) = Δ (x, c x))
    (x : ℝ) (u : EuclideanSpace ℝ (Fin k)) :
    thetaMap Δ U W S₂ c r (x, 0, u, 0) = (x, 0, u, 0) := by
  have hzero : ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k).2.2.2 =
      (0 : EuclideanSpace ℝ (Fin k)) := rfl
  have hsumW : (∑ j : Fin k, (r * ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k).2.2.2 j)
      • W (x, 0) j) = 0 := by
    rw [hzero]
    simp
  have hbracket : S₂ (x, r • (0 : EuclideanSpace ℝ (Fin k))) - Δ (x, c x)
      - (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin k) => S₂ (x, v)) 0)
          (r • (0 : EuclideanSpace ℝ (Fin k))) = 0 := by
    rw [smul_zero, map_zero, sub_zero, hS₂ x, sub_self]
  rw [thetaMap, hbracket, add_zero, hsumW, add_zero, hU x, hιu u, hΔ x]
  ext <;> simp

end Work.Drive.PushDisc
