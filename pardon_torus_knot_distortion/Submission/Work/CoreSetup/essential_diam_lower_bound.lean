import Mathlib
import Submission.Work.Core.Torus
import Submission.Work.TorusCover.Main
import Submission.Work.Geometry.diameter_systole
import Submission.Work.Extract.psi_structure

/-!
# The extrinsic diameter systole of the image torus `Φ.Hinv 1 ∘ torusMap`

Fix an ambient isotopy `Φ` of `ℝ³` and let

  `ψ x y = Φ.Hinv 1 (torusMap x y)`

be the image of the standard torus of revolution under the inverse of the time-one map of `Φ`.
This is an embedded torus in `ℝ³`; it is `2π`-periodic in each variable, injective modulo `2π`,
and continuous (`Work.Extract.psi_structure`).

The main result of this file, `Work.CoreSetup.essential_diam_lower_bound`, is the *extrinsic
diameter systole bound* of this embedded torus: there is a positive constant `ρ` such that the
image of *every* essential closed curve on `ψ` — a curve whose lift to the parameter plane winds
by a nonzero vector `v ∈ ℤ²`, i.e. a curve that is not null-homotopic in the torus — has
Euclidean diameter at least `ρ`.

It is a direct instantiation of the general systole bound `Work.Geometry.diameter_systole` for a
continuous, `2π`-periodic, modulo-`2π` injective parametrisation: `Work.TorusCover.HasWinding`
supplies the periodic lift `Λ` required there, and `Work.Extract.psi_structure` supplies the
structural hypotheses on `ψ`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreSetup

/-- **Extrinsic diameter systole of the image torus of an ambient isotopy.**  For `ψ = Φ.Hinv 1 ∘
torusMap` there is `ρ > 0` such that every curve of `ℝ³` whose winding vector on `ψ` is nonzero
(equivalently, which is not null-homotopic on the torus) has diameter at least `ρ`.

The curve `γ` need not be assumed closed or continuous: a nonzero winding vector is witnessed by
a continuous periodic lift `Λ` of `γ` through the continuous parametrisation `ψ`, so `γ = ψ ∘ Λ`
is automatically continuous and `2π`-periodic. -/
theorem essential_diam_lower_bound (Φ : LeanEval.KnotTheory.PardonDistortion.AmbientIsotopy) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (v : ℤ × ℤ), v ≠ 0 →
      Work.TorusCover.HasWinding (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) γ v →
      ρ ≤ Metric.diam (Set.range γ) := by
  -- the structural facts about `ψ = Φ.Hinv 1 ∘ torusMap`: periodicity in each variable,
  -- injectivity modulo `2π`, and continuity
  obtain ⟨c, hcpos, hper1, hper2, hinj, hcont, hderiv⟩ := Work.Extract.psi_structure Φ
  -- the general diameter systole bound for a parametrised torus
  obtain ⟨ρ, hρpos, hρ⟩ :=
    Work.Geometry.diameter_systole (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y))
      hper1 hper2 hinj hcont
  refine ⟨ρ, hρpos, ?_⟩
  intro γ v hv hw
  -- a nonzero winding vector is witnessed by a continuous, `2π`-periodic lift `Λ`
  obtain ⟨Λ, hΛ⟩ := hw
  have hΛcont : Continuous Λ := hΛ.continuous
  have hΛmap : ∀ t, (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) (Λ t).1 (Λ t).2 = γ t :=
    hΛ.map_eq
  have hΛshift : ∀ t, Λ (t + 2 * Real.pi) = Λ t + Work.TorusCover.periodShift v := hΛ.shift
  -- `γ` is continuous, being the composition of the continuous parametrisation with `Λ`
  have hγcont : Continuous γ := by
    have hcomp : Continuous
        (fun t : ℝ => (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) (Λ t).1 (Λ t).2) :=
      hcont.comp hΛcont
    exact hcomp.congr hΛmap
  refine hρ γ Λ v.1 v.2 hγcont hΛcont hΛmap ?_ (by simpa using hv)
  intro t
  rw [hΛshift t, Work.TorusCover.periodShift]
  ext <;> ring_nf

end Work.CoreSetup
