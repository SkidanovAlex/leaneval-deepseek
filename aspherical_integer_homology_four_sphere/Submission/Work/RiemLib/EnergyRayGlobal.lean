import Submission.Work.RiemLib.EnergyRayCover
import Submission.Work.RiemLib.EnergyCover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.EnergyRayCover
open Submission.EnergyCover
open Submission.GlobalExp
open Submission.Length
open Submission.GeodesicSpeed
open Submission.Minimal
open Submission.RauchGlobal
open Submission.JacobiCoords
open Submission.IntrinsicVariation
open Submission.SecondVarGlobal
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2

/-!
# The second variation of the energy of the geodesic variation of a `GExp`-ray, globally

`Submission.EnergyRayCover.exists_pos_piece_second_deriv` produces the per-piece data of the second
variation of the energy of the family `Φ(σ,t) = GExp (γ t) (σ • (d • V t))` along a `GExp`-ray `γ`,
and `Submission.EnergyCover.energy_second_deriv_cover_eventually` assembles the per-piece data into
the global statement.  This module performs the (mechanical) composition, producing
**`energy_second_deriv_ray`**: the two facts

`HasDerivAt (deriv E) (2 ∫_a^b idxAlong γ (d•V) (covAlong cov (d•V))) 0` and `DifferentiableAt E 0`

for `E(σ) = ∫_a^b (curveSpeed (fun t => GExp (γ t) (σ • (d • V t))))²`, valid for all sufficiently
small `d > 0`.  This is the input of the shortening argument of the global `σ ≤ κ`
(`ConjCut.CutConjInequality`, Roadmap §101.6 item 3).
-/

namespace Submission.EnergyRayGlobal

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The second variation of the energy of a geodesic variation of a `GExp`-ray.**  For a unit... no:
for a nonzero `ξ` and a field `V` that is smooth along the ray `s ↦ GExp p (s • ξ)`, there is
`c₀ > 0` such that for every `d ∈ (0,c₀]` the energy

`E(σ) = ∫_a^b (curveSpeed (fun t => GExp (γ t) (σ • (d • V t))))²`

of the geodesic variation `Φ(σ,t) = GExp (γ t) (σ • (d • V t))` satisfies
`E''(0) = 2 ∫_a^b idxAlong γ (d • V) (∇(d • V))` (and `E` is differentiable at `0`). -/
theorem energy_second_deriv_ray (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hab : a < b) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ Set.Ioc (0 : ℝ) c₀,
      (HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
            (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in a..b, idxAlong (cov := cov)
          (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0) ∧
      (DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
            (σ • (d • V s))) t) ^ 2) 0) := by
  obtain ⟨N, c, c₀, hc₀pos, hc0, hcN, hmono, hspec⟩ :=
    Submission.EnergyRayCover.exists_pos_piece_second_deriv (cov := cov) hmet htor hξ hVs hab
  refine ⟨c₀, hc₀pos, fun d hd => ?_⟩
  obtain ⟨hint, hintZ, hk⟩ := hspec d hd
  exact Submission.EnergyCover.energy_second_deriv_cover_eventually (cov := cov)
    (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))
    (V := fun s => d • V s) (Z := covAlong cov (fun s => d • V s))
    (F := fun σ t => (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
        (σ • (d • V s))) t) ^ 2)
    hc0 hcN hint hintZ hk


/-- **The second variation of the energy of a geodesic variation of a `GExp`-ray**, with the
*eventual differentiability* of the energy kept (needed by the shortening argument). -/
theorem energy_second_deriv_ray' (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hab : a < b) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ Set.Ioc (0 : ℝ) c₀,
      (HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
            (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in a..b, idxAlong (cov := cov)
          (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0) ∧
      (DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
            (σ • (d • V s))) t) ^ 2) 0) ∧
      (∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
            (σ • (d • V s))) t) ^ 2) σ) := by
  obtain ⟨N, c, c₀, hc₀pos, hc0, hcN, hmono, hspec⟩ :=
    Submission.EnergyRayCover.exists_pos_piece_second_deriv (cov := cov) hmet htor hξ hVs hab
  refine ⟨c₀, hc₀pos, fun d hd => ?_⟩
  obtain ⟨hint, hintZ, hk⟩ := hspec d hd
  exact Submission.EnergyCover.energy_second_deriv_cover_eventually' (cov := cov)
    (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))
    (V := fun s => d • V s) (Z := covAlong cov (fun s => d • V s))
    (F := fun σ t => (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
        (σ • (d • V s))) t) ^ 2)
    hc0 hcN hint hintZ hk
end

end Submission.EnergyRayGlobal
