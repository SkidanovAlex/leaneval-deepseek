import Mathlib
import Submission.Work.OddBound.Defs

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

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

/-- **A negative index integral shortens a closed geodesic by closed curves.**  `γ` is a unit-speed
closed geodesic of length `L`; `V` is smooth on `[-(1:ℝ), L+1]` and *periodic* (`V L = V 0`); and
`∫₀^L idxAlong γ V (∇V) < 0`.  Then for all small `σ` on one side of `0` the curves
`s ↦ GExp (γ s) (σ • (d • V s))` are **closed** (because `γ L = γ 0` and `V L = V 0`) and have
`curveLength < L`.
Route: `Submission.EnergyShorten.exists_energy_lt_of_integral_neg_geodesic` for the energy, then the
Cauchy–Schwarz transfer `curveLength ≤ √(L · E σ) < L` exactly as in
`Submission.EnergyShorten.exists_curveLength_lt_of_positive_curvature_geodesic` (which does the same
for a *parallel* field; here the field is arbitrary but periodic). -/
theorem exists_shorter_closed_curve_of_negative_index
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {L : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    (hVs : ∀ s ∈ Icc (0 - 1) (L + 1), SmoothAlongAt (I := I) γ V s)
    (hper : V L = V 0) (hloop : γ L = γ 0)
    (hint : ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t < 0) :
    ∃ d : ℝ, 0 < d ∧
      ((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • V t))) 0 L < L ∧
          GExp (cov := cov) hmet (γ L) (σ • (d • V L))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • V 0))) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • V t))) 0 L < L ∧
          GExp (cov := cov) hmet (γ L) (σ • (d • V L))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • V 0)))) := by
  classical
  -- the second-variation data along the geodesic `γ`
  obtain ⟨c₀, hc₀pos, hspec⟩ :=
    Submission.EnergyGeoGlobal.energy_second_deriv_geodesic' (cov := cov) hmet htor hγsm hgeo hne
      (fun s hs => hVs s ⟨by linarith [hs.1], hs.2⟩) hL
  -- smoothness in `t` of the varied family
  obtain ⟨c₁, hc₁pos, hsmooth⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_geodesic_family (cov := cov) hmet htor hγsm
      (fun s hs => hVs s ⟨by linarith [hs.1], hs.2⟩) hL
  set d : ℝ := min 1 (min c₀ c₁) with hddef
  have hdpos : 0 < d := by rw [hddef]; positivity
  have hdc₀ : d ≤ c₀ := by rw [hddef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hdc₁ : d ≤ c₁ := by rw [hddef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hdIoc : d ∈ Set.Ioc (0 : ℝ) c₀ := ⟨hdpos, hdc₀⟩
  obtain ⟨hsec, hdiff0, hdifev⟩ := hspec d hdIoc
  set E : ℝ → ℝ := fun σ : ℝ => ∫ t in (0 : ℝ)..L, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2 with hEdef
  -- the scaled index integral is negative
  have hcov : covAlong cov (fun s : ℝ => d • V s) = fun s : ℝ => d • covAlong cov V s := by
    funext v
    exact Submission.IndexScale.covAlong_smul (cov := cov) htor γ V d v
  have hpoint : ∀ t : ℝ, idxAlong (cov := cov) γ (fun s => d • V s)
      (covAlong cov (fun s => d • V s)) t
      = d ^ 2 * idxAlong (cov := cov) γ V (covAlong cov V) t := by
    intro t
    rw [hcov]
    exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor γ V (covAlong cov V) d t
  have hInt : (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ (fun s => d • V s)
      (covAlong cov (fun s => d • V s)) t)
      = d ^ 2 * ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t := by
    rw [intervalIntegral.integral_congr (fun t _ => hpoint t),
      intervalIntegral.integral_const_mul]
  have hval : 2 * (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ (fun s => d • V s)
      (covAlong cov (fun s => d • V s)) t) < 0 := by
    rw [hInt]
    have hd2 : (0 : ℝ) < d ^ 2 := by positivity
    have hmul : d ^ 2 * (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t) < 0 :=
      mul_neg_of_pos_of_neg hd2 hint
    linarith
  have hderiv : HasDerivAt (deriv E) (2 * (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
      (fun s => d • V s) (covAlong cov (fun s => d • V s)) t)) 0 := by
    rw [hEdef]
    exact hsec
  have h00 : HasDerivAt E (deriv E 0) 0 := hdiff0.hasDerivAt
  have hev0 : (∀ᶠ σ in 𝓝[>] (0 : ℝ), E σ < E 0) ∨ (∀ᶠ σ in 𝓝[<] (0 : ℝ), E σ < E 0) :=
    Submission.DerivShorten.eventually_lt_or_eventually_lt_of_deriv_deriv_neg h00 hderiv hval hdifev
  -- the energy of the base geodesic: `E 0 = L` by unit speed
  have hE0 : E 0 = L := by
    show (∫ t in (0 : ℝ)..L, (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet
      (γ s) ((0 : ℝ) • (d • V s))) t) ^ 2) = L
    have hfun : (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        ((0 : ℝ) • (d • V s))) = γ := by
      funext s
      rw [zero_smul, GExp_zero]
    rw [hfun]
    have hae : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) L → (curveSpeed (I := I) γ t) ^ 2 = (1 : ℝ) := by
      filter_upwards with t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) L := by
        rw [Set.uIoc_of_le hL.le] at ht
        exact ⟨ht.1.le, ht.2⟩
      rw [hspeed t ht', one_pow]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const,
      smul_eq_mul, mul_one, sub_zero]
  -- Cauchy--Schwarz: length is bounded by the square root of the energy
  have hlen : ∀ σ : ℝ, ContinuousOn (fun t : ℝ => curveSpeed (I := I)
      (fun t' : ℝ => GExp (cov := cov) hmet (γ t')
        (σ • (d • V t'))) t) (Icc 0 L) →
      curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (γ t) (σ • (d • V t))) 0 L ≤ Real.sqrt (L * E σ) := by
    intro σ hcont
    have hcs := Commons.MeasureTheory.IntervalIntegral.sq_integral_le_mul_integral_sq
      (f := fun t : ℝ => curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (γ t') (σ • (d • V t'))) t) hL.le
      (hcont.intervalIntegrable_of_Icc hL.le)
      ((hcont.pow 2).intervalIntegrable_of_Icc hL.le)
    rw [sub_zero] at hcs
    rw [curveLength_def]
    show (∫ t in (0 : ℝ)..L, curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (γ t') (σ • (d • V t'))) t)
      ≤ Real.sqrt (L * ∫ t in (0 : ℝ)..L, (curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (γ t') (σ • (d • V t'))) t) ^ 2)
    exact Real.le_sqrt_of_sq_le hcs
  -- the varied curves are closed, since `γ` and `V` are periodic
  have hclosed : ∀ σ : ℝ, GExp (cov := cov) hmet (γ L) (σ • (d • V L))
      = GExp (cov := cov) hmet (γ 0) (σ • (d • V 0)) := by
    intro σ
    have h1 : (σ • (d • V L) : TangentSpace I (γ L)) = σ • (d • V 0) := by
      rw [hper]
    rw [h1, hloop]
  rcases hev0 with h | h
  · refine ⟨d, hdpos, Or.inl ?_⟩
    filter_upwards [h, (hsmooth d ⟨hdpos, hdc₁⟩).filter_mono nhdsWithin_le_nhds]
      with σ hσE hσsm
    have h1 : curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (γ t) (σ • (d • V t))) 0 L ≤ Real.sqrt (L * E σ) := hlen σ hσsm.2
    have h2 : Real.sqrt (L * E σ) < L := by
      rw [Real.sqrt_lt' hL]
      have h3 := mul_lt_mul_of_pos_left hσE hL
      rw [hE0] at h3
      simpa only [pow_two] using h3
    exact ⟨lt_of_le_of_lt h1 h2, hclosed σ⟩
  · refine ⟨d, hdpos, Or.inr ?_⟩
    filter_upwards [h, (hsmooth d ⟨hdpos, hdc₁⟩).filter_mono nhdsWithin_le_nhds]
      with σ hσE hσsm
    have h1 : curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (γ t) (σ • (d • V t))) 0 L ≤ Real.sqrt (L * E σ) := hlen σ hσsm.2
    have h2 : Real.sqrt (L * E σ) < L := by
      rw [Real.sqrt_lt' hL]
      have h3 := mul_lt_mul_of_pos_left hσE hL
      rw [hE0] at h3
      simpa only [pow_two] using h3
    exact ⟨lt_of_le_of_lt h1 h2, hclosed σ⟩

end Work.OddBound
