import Submission.Work.EvenBound.OnlyTwo

/-!
# The "flush" data produced by the closest-cut-point configuration

At a point `p` whose maximal injectivity radius is `m = injSup hmet < π/√K`, the cut-point step
produces two distinct unit directions `ξ ≠ η` whose minimising rays of length `m` meet at a common
point `q`; Xu's theorem applied at `p` and at `q` (`Submission.KlingenbergEven.ray_periodic_of_two_minimising`)
shows that the ray of `ξ` is **periodic of period `2m`** (so `η = -ξ`).  This module packages the
result in the `1`-periodic, constant-speed `2m` parametrisation

`γ t = GExp p (t • (2m • ξ))`

used by the Synge/third-geodesic argument: `γ` is `1`-periodic, has constant speed `2m` on `[0,1]`,
and the only unit directions `w` at `p` with `GExp p (m • w) = q` are the two directions of `γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.JacobiGlobal
open Submission.Length
open Submission.InjRadius
open Submission.CurvatureVec
open Submission.GeodesicSpeed

namespace Work.EvenBound.FlushData

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The `1`-periodic `2m`-speed parametrisation of the Klingenberg loop is `1`-periodic.** -/
theorem periodic_smul (hmet : IsMetricCompatible cov)
    {p : M} {m : ℝ} {ξ : TangentSpace I p}
    (hper : ∀ u : ℝ, GExp (cov := cov) hmet p ((u + 2 * m) • ξ)
      = GExp (cov := cov) hmet p (u • ξ)) :
    ∀ t : ℝ, GExp (cov := cov) hmet p ((t + 1) • ((2 * m) • ξ))
      = GExp (cov := cov) hmet p (t • ((2 * m) • ξ)) := by
  intro t
  have harg : (t + 1) • ((2 * m) • ξ) = ((2 * m * t) + 2 * m) • ξ := by
    rw [smul_smul]
    congr 1
    ring
  have harg2 : t • ((2 * m) • ξ) = (2 * m * t) • ξ := by
    rw [smul_smul]
    congr 1
    ring
  rw [harg, harg2]
  exact hper (2 * m * t)

/-- **The `2m`-speed of the parametrisation.** -/
theorem curveSpeed_smul (hmet : IsMetricCompatible cov)
    {p : M} {m : ℝ} (hm : 0 < m) {ξ : TangentSpace I p} (hξ : ξ ≠ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      curveSpeed (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ((2 * m) • ξ))) t
        = ‖(2 * m) • ξ‖ := by
  intro t _
  have hne : (2 * m) • ξ ≠ 0 := by
    rw [smul_ne_zero_iff]
    exact ⟨by positivity, hξ⟩
  exact Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hne t


/-- **The only unit directions at `p` whose ray of length `m` ends at `q` are the two directions of
the Klingenberg loop.**  Here `q = GExp p (m • ξ)` and the ray of `ξ` is periodic of period `2m`
(so the ray of `-ξ` also reaches `q` at time `m`); the statement is `Work.EvenBound.OnlyTwo` applied
to the pair `(ξ, -ξ)`.

The two directions are written as `±(2m)⁻¹ • γ'(0)` for the `1`-periodic `2m`-speed parametrisation
`γ t = GExp p (t • (2m • ξ))`, so that the result plugs directly into
`Work.EvenBound.ThirdGeodesic.no_shorter_closed_of_only_two_minimising`. -/
theorem only_two_directions (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p q : M} {m : ℝ} (hm : 0 < m)
    (hinj : InjAtLeast hmet p m) (hmax : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1)
    (hq : GExp (cov := cov) hmet p (m • ξ) = q)
    (hminξ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m)
    (hper : ∀ u : ℝ, GExp (cov := cov) hmet p ((u + 2 * m) • ξ)
      = GExp (cov := cov) hmet p (u • ξ))
    (hnc : ¬ Submission.ConjRadius.IsConjugateTime cov
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m) :
    ∀ w : TangentSpace I p, ‖w‖ = 1 → GExp (cov := cov) hmet p (m • w) = q →
      w = (2 * m)⁻¹ • curveVelocity (I := I)
            (fun t : ℝ => GExp (cov := cov) hmet p (t • ((2 * m) • ξ))) 0 ∨
        w = -((2 * m)⁻¹ • curveVelocity (I := I)
            (fun t : ℝ => GExp (cov := cov) hmet p (t • ((2 * m) • ξ))) 0) := by
  intro w hw hwq
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  -- the ray of `-ξ` also reaches `q` at time `m`
  have hneg : GExp (cov := cov) hmet p (m • (-ξ))
      = GExp (cov := cov) hmet p (m • ξ) := by
    have h1 : m • (-ξ) = ((-m : ℝ)) • ξ := by
      rw [smul_neg, neg_smul]
    rw [h1]
    have h2 := hper (-m)
    rw [show ((-m : ℝ)) + 2 * m = m from by ring] at h2
    exact h2.symm
  have hmeet' : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • (-ξ)) :=
    hneg.symm
  have hminneg : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • (-ξ)))
      = ENNReal.ofReal m := by rw [hneg]; exact hminξ
  have hne' : ξ ≠ -ξ := by
    intro h0
    have h2 : (2 : ℝ) • ξ = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h0]
      exact add_neg_cancel ξ
    exact hξne ((smul_eq_zero.mp h2).resolve_left (by norm_num))
  have hmain := Work.EvenBound.OnlyTwo.eq_or_eq_of_two_minimising_of_xu (I := I) (cov := cov)
    hmet htor hm hinj hmax hξ (by rw [norm_neg]; exact hξ) hw hne' hmeet' hminξ hnc
    (hwq.trans hq.symm)
  -- identify `ξ` and `-ξ` with the two displayed directions
  have hvel : curveVelocity (I := I)
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ((2 * m) • ξ))) 0 = (2 * m) • ξ := by
    have hne2 : (2 * m) • ξ ≠ 0 := by
      rw [smul_ne_zero_iff]
      exact ⟨by positivity, hξne⟩
    exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hne2
  have htwo : (2 * m) ≠ 0 := by positivity
  have hid : (2 * m)⁻¹ • ((2 * m) • ξ) = ξ := by
    rw [smul_smul, inv_mul_cancel₀ htwo, one_smul]
  rw [hvel, hid]
  rcases hmain with h | h
  · exact Or.inl h
  · exact Or.inr h

end

end Work.EvenBound.FlushData
