import Submission.Work.EvenBound.FlushData
import Submission.Work.EvenBound.SyngeField.exists_synge_field_periodic
import Submission.Work.EvenBound.SyngeAssembly.exists_shorter_family

set_option backward.isDefEq.respectTransparency.types false

/-!
# The even-dimensional Klingenberg estimate: the reduction to its two remaining inputs

This module assembles the classical even-dimensional proof of Klingenberg's injectivity-radius
estimate from the pieces proved in the surrounding files:

* `Submission.RayConj.exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt` — the cut-point
  step at the attained point `p`;
* `Submission.KlingenbergEven.ray_periodic_of_two_minimising` — Xu's Theorem B at `p` and at the cut
  point glue the two minimising rays into a **closed geodesic of length `2m`**;
* `Work.EvenBound.FlushData.only_two_directions` — the "only two minimising directions" structure at
  `p`, in the `1`-periodic constant-speed parametrisation of that closed geodesic;
* `Work.EvenBound.SyngeField.exists_synge_field_periodic` — the parallel periodic unit normal field of
  Synge (even dimension + simple connectivity);
* `Work.EvenBound.SyngeAssembly.exists_shorter_family` and
  `Work.EvenBound.SyngeConst.synge_shortening_const_speed` — the shortening to closed curves of
  length `< 2m`;
* `Work.EvenBound.ThirdGeodesic.no_shorter_closed_of_only_two_minimising` — the third minimising
  geodesic produced by the shortening, contradicting the structure at `p`.

The two statements proved elsewhere are taken here as hypotheses (`hattain` and `hnoshort`), so that
this file is a self-contained reduction.
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
open Submission.InjSup
open Submission.CurvatureVec
open Submission.GeodesicSpeed

namespace Work.EvenBound

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

/-- **The "flush + shortening is impossible" input** (the third-minimal-geodesic step): a closed
geodesic of length `2m` at whose base point the only two minimising directions of length `m` are its
own two directions cannot be shortened by a field variation
`t ↦ GExp (γ t) (σ • (d • Z t))`.

This is the statement of `Work.EvenBound.ThirdGeodesic.no_shorter_closed_of_only_two_minimising`,
packaged as a `Prop`. -/
def FlushNoShortening (hmet : IsMetricCompatible cov) : Prop :=
  ∀ {p q : M} {m : ℝ}, 0 < m →
    InjAllAtLeast hmet m →
    Manifold.riemannianEDist I p q = ENNReal.ofReal m →
    ∀ {γ : ℝ → M}, γ 0 = p → γ (1 / 2) = q → (∀ t : ℝ, γ (t + 1) = γ t) →
    ContMDiff 𝓘(ℝ) I ∞ γ →
    (∀ t : ℝ, IsGeodesicAt cov γ t) →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, curveSpeed (I := I) γ t = 2 * m) →
    (∀ w : TangentSpace I p, ‖w‖ = 1 → GExp (cov := cov) hmet p (m • w) = q →
      w = (2 * m)⁻¹ • curveVelocity (I := I) γ 0 ∨
        w = -((2 * m)⁻¹ • curveVelocity (I := I) γ 0)) →
    ∀ {Z : (t : ℝ) → TangentSpace I (γ t)}, Z 1 = Z 0 →
    (∀ s ∈ Set.Icc (0 - 1) ((1 : ℝ) + 1), SmoothAlongAt (I := I) γ Z s) →
    ∀ {d : ℝ}, 0 < d →
    (∀ᶠ σ in 𝓝[>] (0 : ℝ),
      curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • Z t))) 0 1
        < 2 * m) →
    False

/-- **The even-dimensional Klingenberg estimate, from its two remaining inputs.**  On a compact,
simply connected, even-dimensional manifold with `δ ≤ sec ≤ K` (`0 < δ`, `0 < K`), if the global
injectivity radius `injSup hmet = inf_p inj(p)` is attained at some point (`hattain`) and the
flush/shortening configuration is impossible (`hnoshort`), then the exponential map is injective on
the ball of radius `π/√K` at every point. -/
theorem injAllAtLeast_pi_div_sqrt_even_of_inputs
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hEven : Even (Module.finrank ℝ E))
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      δ ≤ inner ℝ (curvVec cov p u v v) u)
    (hattain : injSup hmet < Real.pi / Real.sqrt K → ∃ p : M, InjAtLeast hmet p (injSup hmet) ∧
      ∀ r : ℝ, injSup hmet < r → ¬ InjAtLeast hmet p r)
    (hnoshort : FlushNoShortening (I := I) (cov := cov) hmet) :
    InjAllAtLeast hmet (Real.pi / Real.sqrt K) := by
  classical
  suffices hle : Real.pi / Real.sqrt K ≤ injSup hmet by
    intro x
    exact Submission.InjRadius.injAtLeast_mono (I := I) hmet
      (Submission.InjSup.injAllAtLeast_injSup (I := I) hmet x) hle
  by_contra hcon
  push_neg at hcon
  -- the attained point and the uniform bound
  obtain ⟨p, hattain1, hmax⟩ := hattain hcon
  obtain ⟨ρ, hρpos, hρall⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  obtain ⟨R, -, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor p
  have hbdd : BddAbove {r : ℝ | InjAllAtLeast hmet r} :=
    Submission.InjSup.bddAbove_injAllAtLeast_of_diam_le (I := I) (cov := cov) hmet htor hR
  have hm0 : 0 < injSup hmet := by
    have : ρ ≤ sSup {r : ℝ | InjAllAtLeast hmet r} := le_csSup hbdd hρall
    exact lt_of_lt_of_le hρpos this
  have hinjall : InjAllAtLeast hmet (injSup hmet) :=
    Submission.InjSup.injAllAtLeast_injSup (I := I) hmet
  -- the cut-point step
  obtain ⟨ξ, η, hξ, hη, hξη, hmeet, -, -, -, -, -, hmin1, hmin2⟩ :=
    Submission.RayConj.exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt
      (I := I) (cov := cov) hmet htor hcurv hK hm0 hcon hattain1 hmax
  have hminξ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (injSup hmet • ξ))
      = ENNReal.ofReal (injSup hmet) := hmin1 (injSup hmet) ⟨hm0.le, le_rfl⟩
  have hminη : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (injSup hmet • η))
      = ENNReal.ofReal (injSup hmet) := by
    have h := hmin2 0 ⟨le_rfl, hm0.le⟩
    rw [sub_zero] at h
    exact h
  -- Xu's theorem at `p` and at the cut point: periodicity of the ray
  have hper : ∀ u : ℝ,
      GExp (cov := cov) hmet p ((u + 2 * injSup hmet) • ξ)
        = GExp (cov := cov) hmet p (u • ξ) :=
    Submission.KlingenbergEven.ray_periodic_of_two_minimising (I := I) (cov := cov) hmet htor
      hcurv hK hm0 hcon hattain1 hmax hinjall hξ hη hξη hmeet hminξ hminη
  -- the non-conjugacy along the ray of `ξ`
  have hnc : ¬ Submission.ConjRadius.IsConjugateTime cov
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) (injSup hmet) :=
    Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt (I := I) (cov := cov) hmet htor
      hcurv hK hcon
  -- the "only two directions" structure
  have honly : ∀ w : TangentSpace I p, ‖w‖ = 1 →
      GExp (cov := cov) hmet p (injSup hmet • w) = GExp (cov := cov) hmet p (injSup hmet • ξ) →
        w = (2 * injSup hmet)⁻¹ • curveVelocity (I := I)
              (fun t : ℝ => GExp (cov := cov) hmet p (t • ((2 * injSup hmet) • ξ))) 0 ∨
            w = -((2 * injSup hmet)⁻¹ • curveVelocity (I := I)
              (fun t : ℝ => GExp (cov := cov) hmet p (t • ((2 * injSup hmet) • ξ))) 0) :=
    Work.EvenBound.FlushData.only_two_directions (I := I) (cov := cov) hmet htor hm0 hattain1
      hmax hξ rfl hminξ hper hnc
  -- the `1`-periodic constant-speed `2m` parametrisation
  set γ : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet p (t • ((2 * injSup hmet) • ξ)) with hγ
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  have hvne : (2 * injSup hmet) • ξ ≠ 0 := by
    rw [smul_ne_zero_iff]
    exact ⟨by positivity, hξne⟩
  have hγsm : ContMDiff 𝓘(ℝ) I ∞ γ := by
    rw [hγ]
    exact Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hvne
  have hγgeo : ∀ t : ℝ, IsGeodesicAt cov γ t := by
    intro t
    rw [hγ]
    exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hvne t
  have hγne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0 := by
    intro t
    rw [hγ]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hvne t
  have hγ0 : γ 0 = p := by
    rw [hγ]
    simp [GExp_zero]
  have hγhalf : γ (1 / 2) = GExp (cov := cov) hmet p (injSup hmet • ξ) := by
    rw [hγ]
    have harg : (1 / 2 : ℝ) • ((2 * injSup hmet) • ξ) = injSup hmet • ξ := by
      rw [smul_smul]
      congr 1
      ring
    exact congrArg (fun v => GExp (cov := cov) hmet p v) harg
  have hγper : ∀ t : ℝ, γ (t + 1) = γ t := by
    rw [hγ]
    exact Work.EvenBound.FlushData.periodic_smul (I := I) (cov := cov) hmet hper
  have hγsp : ∀ t ∈ Set.Icc (0 : ℝ) 1, curveSpeed (I := I) γ t = 2 * injSup hmet := by
    intro t ht
    rw [hγ]
    rw [Work.EvenBound.FlushData.curveSpeed_smul (I := I) (cov := cov) hmet hm0 hξne t ht]
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * injSup hmet), hξ, mul_one]
  have hpq : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (injSup hmet • ξ))
      = ENNReal.ofReal (injSup hmet) := hminξ
  -- the curvature bound along `γ`
  have hcurvγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (curvVec cov (γ t) u v v) u :=
    fun t _ u v hu hv huv => hpinch (γ t) u v hu hv huv
  -- Synge's parallel normal field
  obtain ⟨Z, hZ1, hZ1n, hZn, hZsm, hZpar⟩ :=
    Work.EvenBound.SyngeField.exists_synge_field_periodic (I := I) (cov := cov) hmet htor
      hγper hγsm hγgeo hγne hEven
  -- the shortening family
  obtain ⟨Z', d, hd, hZ'1, hZ'sm, hshort⟩ :=
    Work.EvenBound.SyngeAssembly.exists_shorter_family (I := I) (cov := cov) hmet htor
      hm0 hγper hγsm hγgeo hγne hγsp hZ1 hZsm hZpar hZ1n hZn hδ hcurvγ
  -- the third-minimal-geodesic contradiction
  exact hnoshort hm0 hinjall hpq hγ0 hγhalf hγper hγsm hγgeo hγsp
    (fun w hw hwq => by
      rcases honly w hw hwq with h | h
      · exact Or.inl (by rw [hγ]; exact h)
      · exact Or.inr (by rw [hγ]; exact h))
    hZ'1 hZ'sm hd hshort

end

end Work.EvenBound
