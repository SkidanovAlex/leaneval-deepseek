import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.Minimax
import Submission.Work.OddBound.IndexDirichlet
import Submission.Work.OddBound.IndexPair
import Submission.Work.OddBound.strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair

set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.klingenbergOdd

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-! ## The index bound: non-strict curvature, strict length

`Work.OddBound.not_dirichletIndexAtMostOne_of_parallelNormalPair` needs the curvature to exceed
`δ` by a *uniform* margin `ε > 0`; that margin is what makes the index integral at the critical
length `L = π/√δ` strictly negative.  When the pinching is only non-strict (`sec ≥ δ`) the index
integral can vanish at `L = π/√δ`, but it is strictly negative as soon as `L > π/√δ` — the extra
slack in the *length* plays the role of the margin `ε`.  This lemma records that form, by applying
the existing one to a curvature threshold `δ' < δ` chosen so that `π/√δ' ≤ L`. -/

theorem not_dirichletIndexLeOne_of_parallelNormalPair_strict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {L δ : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hδ : 0 < δ) (hπ : Real.pi / Real.sqrt δ < L)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (curvVec cov (γ t) u v v) u)
    (hp : ParallelNormalPair (I := I) cov γ L) :
    ¬ DirichletIndexLeOne (I := I) (cov := cov) γ L := by
  refine not_dirichletIndexLeOne_of_dirichletIndexNotLeOne (I := I) (cov := cov) ?_
  refine strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair (I := I) (cov := cov)
    (L := L) (δ := δ / 2) (ε := δ / 2) hmet htor hγsm hne hL hspeed ?_ ?_ ?_ ?_ hp
  · positivity
  · positivity
  · rw [show δ / 2 + δ / 2 = δ by ring]
    exact hπ
  · intro t ht u v hu hv huv
    rw [show δ / 2 + δ / 2 = δ by ring]
    exact hcurv t ht u v hu hv huv

/-! ## The injectivity-radius estimate -/

/-- **The odd-dimensional Klingenberg injectivity estimate from the minimax input, with the
boundary hypothesis.**  Same as `Work.OddBound.injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput` but
with the *strict* pinching `K/4 + ε ≤ sec` replaced by the non-strict `K/4 ≤ sec` together with the
boundary hypothesis `hboundary`: a closed unit-speed geodesic of length exactly `2π/√K` is never a
Dirichlet-index-`≤ 1` critical point.  The two cases are then immediate: a minimax geodesic of length
`> 2π/√K` contradicts the index bound with `δ = K/4` and strict length
(`not_dirichletIndexAtMostOne_of_parallelNormalPair_strict`), while one of length exactly `2π/√K`
contradicts `hboundary`. -/
theorem injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput_and_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    [SimplyConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u)
    (hminimax : Work.OddBound.MinimaxInput (I := I) (cov := cov) hmet htor K)
    (hboundary : ∀ (c : ℝ → M) (T : ℝ), c T = c 0 →
      ContMDiff 𝓘(ℝ) I ∞ c →
      (∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov c t) →
      (∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) c t ≠ 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, Submission.Length.curveSpeed (I := I) c t = 1) →
      T = 2 * Real.pi / Real.sqrt K →
      ¬ Work.OddBound.DirichletIndexLeOne (I := I) (cov := cov) c T) :
    InjAllAtLeast hmet (Real.pi / Real.sqrt K) := by
  classical
  suffices hle : Real.pi / Real.sqrt K ≤ Submission.InjSup.injSup hmet by
    intro x
    exact Submission.InjRadius.injAtLeast_mono (I := I) hmet
      (Submission.InjSup.injAllAtLeast_injSup (I := I) hmet x) hle
  by_contra hcon
  push_neg at hcon
  -- ## the flush configuration at an attained closest cut point
  obtain ⟨p, hattain1, hmax⟩ :=
    Work.EvenBound.Attain.injSup_attained_of_lt_pi_div_sqrt (I := I) (cov := cov) hmet htor
      hcurv hK hcon
  obtain ⟨ρ, hρpos, hρall⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  obtain ⟨R, -, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor p
  have hbdd : BddAbove {r : ℝ | InjAllAtLeast hmet r} :=
    Submission.InjSup.bddAbove_injAllAtLeast_of_diam_le (I := I) (cov := cov) hmet htor hR
  have hm0 : 0 < Submission.InjSup.injSup hmet := by
    have : ρ ≤ sSup {r : ℝ | InjAllAtLeast hmet r} := le_csSup hbdd hρall
    exact lt_of_lt_of_le hρpos this
  have hinjall : InjAllAtLeast hmet (Submission.InjSup.injSup hmet) :=
    Submission.InjSup.injAllAtLeast_injSup (I := I) hmet
  obtain ⟨ξ, η, hξ, hη, hξη, hmeet, -, -, -, -, -, hmin1, hmin2⟩ :=
    Submission.RayConj.exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt
      (I := I) (cov := cov) hmet htor hcurv hK hm0 hcon hattain1 hmax
  have hminξ : Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • ξ))
      = ENNReal.ofReal (Submission.InjSup.injSup hmet) :=
    hmin1 (Submission.InjSup.injSup hmet) ⟨hm0.le, le_rfl⟩
  have hminη : Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • η))
      = ENNReal.ofReal (Submission.InjSup.injSup hmet) := by
    have h := hmin2 0 ⟨le_rfl, hm0.le⟩
    rw [sub_zero] at h
    exact h
  have hper : ∀ u : ℝ,
      GExp (cov := cov) hmet p ((u + 2 * Submission.InjSup.injSup hmet) • ξ)
        = GExp (cov := cov) hmet p (u • ξ) :=
    Submission.KlingenbergEven.ray_periodic_of_two_minimising (I := I) (cov := cov) hmet htor
      hcurv hK hm0 hcon hattain1 hmax hinjall hξ hη hξη hmeet hminξ hminη
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  -- ## the unit-speed ray of `ξ` is a nontrivial geodesic digon of length `2m`
  have hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t :=
    fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t
  have hneΓ : ∀ t : ℝ,
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t ≠ 0 :=
    fun t => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξne t
  have hspeedΓ : ∀ t ∈ Icc (0 : ℝ) (2 * Submission.InjSup.injSup hmet),
      curveSpeed (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t = 1 :=
    fun t _ => curveSpeed_GExp_ray_eq_one (cov := cov) hmet hξ t
  have hclosedΓ : (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
        (2 * Submission.InjSup.injSup hmet)
      = (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0 := by
    show GExp (cov := cov) hmet p ((2 * Submission.InjSup.injSup hmet) • ξ)
      = GExp (cov := cov) hmet p ((0 : ℝ) • ξ)
    rw [zero_smul, GExp_zero]
    exact GExp_two_mul_eq_of_cutPointData (cov := cov) hmet htor hcurv hK hm0 hcon
      hattain1 hmax hξ hη hξη hmeet hminξ hminη
  have hhalfΓ : Manifold.riemannianEDist I
        ((fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) 0)
        ((fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
          ((2 * Submission.InjSup.injSup hmet) / 2))
      = ENNReal.ofReal ((2 * Submission.InjSup.injSup hmet) / 2) := by
    have harg : (2 * Submission.InjSup.injSup hmet) / 2 = Submission.InjSup.injSup hmet := by ring
    rw [harg]
    show Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((0 : ℝ) • ξ))
      (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • ξ)) = _
    rw [zero_smul, GExp_zero]
    exact hminξ
  -- ## the minimax
  have hlt : 2 * Submission.InjSup.injSup hmet < 2 * Real.pi / Real.sqrt K := by
    rw [mul_div_assoc]
    linarith
  have hγsm : ContMDiff 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξne
  obtain ⟨T, c, hT, hc0, hcsm, hcgeo, hcne, hcsp, hidx⟩ :=
    hminimax ‹SimplyConnectedSpace M› hcurv hK (by positivity) hlt hγsm hgeo hneΓ hspeedΓ
      hclosedΓ (by simpa using hper) hhalfΓ
  -- ## the index bound at the minimax geodesic
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hπeq : Real.pi / Real.sqrt (K / 4) = 2 * Real.pi / Real.sqrt K := by
    have h4 : Real.sqrt (K / 4) = Real.sqrt K / 2 := by
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ K) 4]
      norm_num
    rw [h4]
    field_simp
  rcases lt_or_eq_of_le hT with hTstrict | hTeq
  · -- the length is strictly larger than the critical one: the index bound is strict
    obtain ⟨hp⟩ :=
      exists_parallelNormalPair (I := I) (cov := cov) (L := T) hmet htor
        (contMDiffOn_univ.mpr hcsm) hcgeo hcne (by linarith) hDim
    exact not_dirichletIndexLeOne_of_parallelNormalPair_strict (I := I) (cov := cov) hmet
      (γ := c) (L := T) (δ := K / 4) htor (contMDiffOn_univ.mpr hcsm) hcne hTpos hcsp
      (by linarith) (by rw [hπeq]; exact hTstrict)
      (fun t _ u v hu hv huv => hpinch (c t) u v hu hv huv) hp hidx
  · -- the length equals the critical one: this is ruled out by the boundary hypothesis
    exact (hboundary c T hc0 hcsm hcgeo hcne hcsp hTeq.symm) hidx

/-- **Klingenberg's length bound in odd dimensions, from the minimax input and the boundary
hypothesis.**  Every closed geodesic loop has length `≥ 2π/√K`: the injectivity-radius estimate
`injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput_and_boundary` is converted by
`Work.OddBound.two_pi_div_sqrt_le_of_inj`. -/
theorem klingenberg_length_bound_odd_of_minimaxInput_and_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    [SimplyConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u)
    (hminimax : Work.OddBound.MinimaxInput (I := I) (cov := cov) hmet htor K)
    (hboundary : ∀ (c : ℝ → M) (T : ℝ), c T = c 0 →
      ContMDiff 𝓘(ℝ) I ∞ c →
      (∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov c t) →
      (∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) c t ≠ 0) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, Submission.Length.curveSpeed (I := I) c t = 1) →
      T = 2 * Real.pi / Real.sqrt K →
      ¬ Work.OddBound.DirichletIndexLeOne (I := I) (cov := cov) c T) :
    ∀ {p : M} {T : ℝ} {γ : ℝ → M},
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt (I := I) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T := by
  intro p T γ hloop
  have hInj : InjAtLeast hmet p (Real.pi / Real.sqrt K) :=
    Submission.InjRadius.injAtLeast_of_injAllAtLeast (I := I) hmet
      (injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput_and_boundary (I := I) (cov := cov) hmet htor
        hDim hK hcurv hpinch hminimax hboundary) p
  exact two_pi_div_sqrt_le_of_inj (cov := cov) hmet htor hK hloop hInj le_rfl

end Work.OddBound.klingenbergOdd
