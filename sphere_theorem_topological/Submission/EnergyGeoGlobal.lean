import Submission.EnergyGeoCover
import Submission.EnergyCover

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
# The second variation of the energy of the geodesic variation of an arbitrary geodesic

`Submission.EnergyRayGlobal` composes the per-piece data of the second variation of the energy along a
`GExp`-ray with the cover assembly.  This module does the same for an arbitrary `C^∞` geodesic with
non-vanishing velocity, using `Submission.EnergyRayCover.exists_pos_piece_second_deriv_geodesic`.
-/

namespace Submission.EnergyGeoGlobal

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

theorem energy_second_deriv_geodesic (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s)
    (hab : a < b) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ Set.Ioc (0 : ℝ) c₀,
      (HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in a..b, idxAlong (cov := cov)
          γ (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0) ∧
      (DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2) 0) := by
  obtain ⟨N, c, c₀, hc₀pos, hc0, hcN, hmono, hspec⟩ :=
    Submission.EnergyRayCover.exists_pos_piece_second_deriv_geodesic (cov := cov) hmet htor hγsm
      hgeo hne hVs hab
  refine ⟨c₀, hc₀pos, fun d hd => ?_⟩
  obtain ⟨hint, hintZ, hk⟩ := hspec d hd
  exact Submission.EnergyCover.energy_second_deriv_cover_eventually (cov := cov)
    (γ := γ)
    (V := fun s => d • V s) (Z := covAlong cov (fun s => d • V s))
    (F := fun σ t => (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2)
    hc0 hcN hint hintZ hk




theorem energy_second_deriv_geodesic' (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s)
    (hab : a < b) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ Set.Ioc (0 : ℝ) c₀,
      (HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in a..b, idxAlong (cov := cov)
          γ (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0) ∧
      (DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2) 0) ∧
      (∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2) σ) := by
  obtain ⟨N, c, c₀, hc₀pos, hc0, hcN, hmono, hspec⟩ :=
    Submission.EnergyRayCover.exists_pos_piece_second_deriv_geodesic (cov := cov) hmet htor hγsm
      hgeo hne hVs hab
  refine ⟨c₀, hc₀pos, fun d hd => ?_⟩
  obtain ⟨hint, hintZ, hk⟩ := hspec d hd
  exact Submission.EnergyCover.energy_second_deriv_cover_eventually' (cov := cov)
    (γ := γ)
    (V := fun s => d • V s) (Z := covAlong cov (fun s => d • V s))
    (F := fun σ t => (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2)
    hc0 hcN hint hintZ hk

end

end Submission.EnergyGeoGlobal
