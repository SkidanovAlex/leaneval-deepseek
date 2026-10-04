import Submission.EnergyGeoShorten

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.GlobalExp
open Submission.CurvatureVec
open Submission.Length
open Submission.GeodesicSpeed

/-!
# Synge's shortening lemma

**`exists_shorter_closed_curve`**: on a manifold with a *positive* lower bound `δ > 0` for the
sectional curvature, a closed unit-speed geodesic `γ` of length `L` which carries a field `X` that is

* smooth along `γ`, *parallel* (`∇X = 0`), *periodic* (`X L = X 0`),
* of constant norm `1` and normal to the velocity,

can be **shortened by closed curves**: there is `d > 0` such that for all sufficiently small `σ` on
one side of `0` the curve `t ↦ GExp (γ t) (σ • (d • X t))` is closed (`t = 0` and `t = L` agree) and
has length `< L`.

This is the second-variation step of Berger's even-dimensional proof of Klingenberg's estimate
(Roadmap §§110, 112, 113): with `X` supplied by Synge's linear algebra (the holonomy of the normal
bundle is an element of `SO(n-1)` with `n-1` odd, hence fixes a vector; see
`Submission.HolDet.exists_periodic_parallelField`), the shortened closed curves contradict the
minimality of the shortest closed geodesic.
-/

namespace Submission.SyngeShorten

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

/-- **Synge's shortening lemma.**  A closed unit-speed geodesic carrying a smooth, parallel,
periodic, unit, normal field shortens, by closed curves, as soon as the sectional curvature is
positive. -/
theorem exists_shorter_closed_curve (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {L : ℝ} (hL : 0 < L) (hloop : γ L = γ 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    {X : (t : ℝ) → TangentSpace I (γ t)}
    (hXs : ∀ s ∈ Icc (0 - 1) (L + 1), SmoothAlongAt (I := I) γ X s)
    (hXpar : ∀ s ∈ Icc (0 - 1) (L + 1), covAlong cov X s = 0)
    (hXper : X L = X 0)
    (hX1 : ∀ t ∈ Icc (0 : ℝ) L, ‖X t‖ = 1)
    (hXnorm : ∀ t ∈ Icc (0 : ℝ) L, inner ℝ (X t) (curveVelocity (I := I) γ t) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (curvVec cov (γ t) u v v) u) :
    ∃ d : ℝ, 0 < d ∧
      (((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • X t))) 0 L < L ∧
          GExp (cov := cov) hmet (γ L) (σ • (d • X L))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • X 0))) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • X t))) 0 L < L ∧
          GExp (cov := cov) hmet (γ L) (σ • (d • X L))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • X 0))))) := by
  classical
  -- the pointwise positivity of the curvature pairing
  have hvel1 : ∀ t ∈ Icc (0 : ℝ) L, ‖curveVelocity (I := I) γ t‖ = 1 := by
    intro t ht
    rw [← curveSpeed_eq_norm (I := I) γ t]
    exact hspeed t ht
  have hpos : ∀ t ∈ Icc (0 : ℝ) L, 0 < inner ℝ
      (curvVec cov (γ t) (X t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (X t) := by
    intro t ht
    exact lt_of_lt_of_le hδ
      (hcurv t ht (X t) (curveVelocity (I := I) γ t) (hX1 t ht) (hvel1 t ht) (hXnorm t ht))
  have hmain := Submission.EnergyShorten.exists_curveLength_lt_of_positive_curvature_geodesic
    (cov := cov) hmet htor (contMDiffOn_univ.mpr hγsm) hgeo hne hXs hXpar hL hspeed hpos
  obtain ⟨d, hdpos, hd⟩ := hmain
  refine ⟨d, hdpos, ?_⟩
  -- the shortened curves are closed
  have hclosed : ∀ σ : ℝ, GExp (cov := cov) hmet (γ L) (σ • (d • X L))
      = GExp (cov := cov) hmet (γ 0) (σ • (d • X 0)) := by
    intro σ
    have h1 : (σ • (d • X L) : TangentSpace I (γ L)) = σ • (d • X 0) := by
      rw [hXper]
    rw [h1, hloop]
  rcases hd with h | h
  · exact Or.inl (h.mono fun σ hσ => ⟨hσ, hclosed σ⟩)
  · exact Or.inr (h.mono fun σ hσ => ⟨hσ, hclosed σ⟩)

end

end Submission.SyngeShorten
