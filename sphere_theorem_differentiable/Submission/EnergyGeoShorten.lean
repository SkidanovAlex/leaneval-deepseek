import Submission.EnergyGeoGlobal
import Submission.EnergyGeoSmooth
import Submission.EnergyShorten

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
open scoped Interval
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.GlobalExp
open Submission.Length
open Submission.IndexIntrinsic
open Submission.CurvatureVec
open Submission.IndexScale
open Submission.DerivShorten

/-!
# The shortening of a geodesic variation of an arbitrary geodesic with negative index integral

`Submission.EnergyShorten` contains the shortening chain for a `GExp`-ray.  This module contains the
same chain for an arbitrary `C^∞` geodesic with non-vanishing velocity:

* `exists_energy_lt_of_integral_neg_geodesic` — a negative index integral shortens the energy;
* `exists_energy_lt_of_positive_curvature_geodesic` — the same for a parallel field with positive
  curvature pairing;
* **`exists_curveLength_lt_of_positive_curvature_geodesic`** — the geometric form: for a unit-speed
  geodesic of length `L` with a parallel field of positive curvature pairing, there is a scaling `d`
  such that the curves `t ↦ GExp (γ t) (σ • (d • V t))` have length `< L` for all small `σ` on one
  side of `0`.

These are the inputs of the Synge shortening argument (a closed geodesic of positive curvature with a
parallel periodic *normal* field can be shortened) and of the odd-dimensional Klingenberg argument.
-/

namespace Submission.EnergyShorten

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

theorem exists_energy_lt_of_integral_neg_geodesic
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s)
    (hab : a < b)
    (hint : ∫ t in a..b, idxAlong (cov := cov) γ V (covAlong cov V) t < 0) :
    ∃ d : ℝ, 0 < d ∧
      (((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (γ s)
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            γ t) ^ 2) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (γ s)
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            γ t) ^ 2))) := by
  classical
  obtain ⟨c₀, hc₀pos, hspec⟩ :=
    Submission.EnergyGeoGlobal.energy_second_deriv_geodesic' (cov := cov) hmet htor hγsm hgeo hne
      hVs hab
  refine ⟨min 1 c₀, by positivity, ?_⟩
  have hdmem : min 1 c₀ ∈ Set.Ioc (0 : ℝ) c₀ := ⟨by positivity, min_le_right _ _⟩
  obtain ⟨hsec, hdiff0, hdifev⟩ := hspec _ hdmem
  -- the energy of the scaled variation
  set E : ℝ → ℝ := fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        (σ • (min 1 c₀ • V s))) t) ^ 2 with hEdef
  -- the scaling identity for the index integral
  have hcov : covAlong cov (fun s : ℝ => min 1 c₀ • V s)
      = fun s : ℝ => min 1 c₀ • covAlong cov V s := by
    funext v
    exact Submission.IndexScale.covAlong_smul (cov := cov) htor
      γ V (min 1 c₀) v
  have hpoint : ∀ t : ℝ, idxAlong (cov := cov)
      γ (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t
      = (min 1 c₀) ^ 2 * idxAlong (cov := cov)
        γ V (covAlong cov V) t := by
    intro t
    rw [hcov]
    exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor
      γ V (covAlong cov V) (min 1 c₀) t
  have hInt : (∫ t in a..b, idxAlong (cov := cov)
      γ (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t)
      = (min 1 c₀) ^ 2 * ∫ t in a..b, idxAlong (cov := cov)
        γ V (covAlong cov V) t := by
    rw [intervalIntegral.integral_congr (fun t _ => hpoint t),
      intervalIntegral.integral_const_mul]
  have hval : 2 * (∫ t in a..b, idxAlong (cov := cov)
      γ (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t) < 0 := by
    rw [hInt]
    have hd2 : (0 : ℝ) < (min 1 c₀) ^ 2 := by positivity
    have hmul : (min 1 c₀) ^ 2 * (∫ t in a..b, idxAlong (cov := cov)
        γ V (covAlong cov V) t) < 0 :=
      mul_neg_of_pos_of_neg hd2 hint
    linarith
  -- the calculus lemma
  have hderiv : HasDerivAt (deriv E) (2 * (∫ t in a..b, idxAlong (cov := cov)
      γ (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t)) 0 := by
    rw [hEdef]
    exact hsec
  have h00 : HasDerivAt E (deriv E 0) 0 := hdiff0.hasDerivAt
  have hev : (∀ᶠ σ in 𝓝[>] (0 : ℝ), E σ < E 0) ∨ (∀ᶠ σ in 𝓝[<] (0 : ℝ), E σ < E 0) :=
    eventually_lt_or_eventually_lt_of_deriv_deriv_neg h00 hderiv hval hdifev
  have hE0 : (∫ t in a..b, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        ((0 : ℝ) • (min 1 c₀ • V s))) t) ^ 2)
      = ∫ t in a..b, (curveSpeed (I := I)
        γ t) ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hfun : (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        ((0 : ℝ) • (min 1 c₀ • V s)))
        = γ := by
      funext s
      rw [zero_smul, GExp_zero]
    rw [hfun]
  rcases hev with h | h
  · refine Or.inl (h.mono fun σ hσ => ?_)
    simp only [hEdef] at hσ
    rwa [hE0] at hσ
  · refine Or.inr (h.mono fun σ hσ => ?_)
    simp only [hEdef] at hσ
    rwa [hE0] at hσ



theorem exists_energy_lt_of_positive_curvature_geodesic
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s)
    (hpar : ∀ s ∈ Icc (a - 1) (b + 1), covAlong cov V s = 0)
    (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < inner ℝ (curvVec cov (γ t) (V t)
      (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (V t)) :
    ∃ d : ℝ, 0 < d ∧
      (((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (γ s)
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            γ t) ^ 2) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (γ s)
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            γ t) ^ 2))) := by
  refine exists_energy_lt_of_integral_neg_geodesic (cov := cov) hmet htor hγsm hgeo hne hVs hab ?_
  exact integral_idxAlong_neg_of_parallel (cov := cov) hmet htor hab (contMDiffOn_univ.mp hγsm)
    hne hVs hpar hpos



theorem exists_curveLength_lt_of_positive_curvature_geodesic
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    {L : ℝ}
    (hVs : ∀ s ∈ Icc (0 - 1) (L + 1), SmoothAlongAt (I := I) γ V s)
    (hpar : ∀ s ∈ Icc (0 - 1) (L + 1), covAlong cov V s = 0)
    (hL : 0 < L)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hpos : ∀ t ∈ Icc (0 : ℝ) L, 0 < inner ℝ (curvVec cov (γ t) (V t)
      (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (V t)) :
    ∃ d : ℝ, 0 < d ∧
      ((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
            (γ t) (σ • (d • V t))) 0 L < L) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
            (γ t) (σ • (d • V t))) 0 L < L)) := by
  classical
  obtain ⟨c₀, hc₀pos, hspec⟩ :=
    Submission.EnergyGeoGlobal.energy_second_deriv_geodesic' (cov := cov) hmet htor hγsm hgeo hne
      (fun s hs => hVs s ⟨by linarith [hs.1], hs.2⟩) hL
  obtain ⟨c₁, hc₁pos, hsmooth⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_geodesic_family (cov := cov) hmet htor hγsm
      (fun s hs => hVs s ⟨by linarith [hs.1], hs.2⟩) hL
  set d : ℝ := min 1 (min c₀ c₁) with hddef
  have hdpos : 0 < d := by rw [hddef]; positivity
  have hdc₀ : d ≤ c₀ := by
    rw [hddef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hdc₁ : d ≤ c₁ := by
    rw [hddef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hdIoc : d ∈ Set.Ioc (0 : ℝ) c₀ := ⟨hdpos, hdc₀⟩
  obtain ⟨hsec, hdiff0, hdifev⟩ := hspec d hdIoc
  set E : ℝ → ℝ := fun σ : ℝ => ∫ t in (0 : ℝ)..L, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        (σ • (d • V s))) t) ^ 2 with hEdef
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
  have hneg : ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t < 0 :=
    integral_idxAlong_neg_of_parallel (cov := cov) hmet htor hL (contMDiffOn_univ.mp hγsm)
    hne hVs hpar hpos
  have hval : 2 * (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ (fun s => d • V s)
      (covAlong cov (fun s => d • V s)) t) < 0 := by
    rw [hInt]
    have hd2 : (0 : ℝ) < d ^ 2 := by positivity
    have hmul : d ^ 2 * (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t) < 0 :=
      mul_neg_of_pos_of_neg hd2 hneg
    linarith
  have hderiv : HasDerivAt (deriv E) (2 * (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
      (fun s => d • V s) (covAlong cov (fun s => d • V s)) t)) 0 := by
    rw [hEdef]
    exact hsec
  have h00 : HasDerivAt E (deriv E 0) 0 := hdiff0.hasDerivAt
  have hev0 : (∀ᶠ σ in 𝓝[>] (0 : ℝ), E σ < E 0) ∨ (∀ᶠ σ in 𝓝[<] (0 : ℝ), E σ < E 0) :=
    eventually_lt_or_eventually_lt_of_deriv_deriv_neg h00 hderiv hval hdifev
  have hEnonneg : ∀ σ : ℝ, 0 ≤ E σ := by
    intro σ
    show 0 ≤ ∫ t in (0 : ℝ)..L, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (γ s)
        (σ • (d • V s))) t) ^ 2
    exact intervalIntegral.integral_nonneg hL.le (fun t _ => sq_nonneg _)
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
  -- the length bound
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
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..L, curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (γ t') (σ • (d • V t'))) t := by
      refine intervalIntegral.integral_nonneg hL.le (fun t _ => ?_)
      exact curveSpeed_nonneg (I := I) _ t
    rw [curveLength_def]
    show (∫ t in (0 : ℝ)..L, curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (γ t') (σ • (d • V t'))) t)
      ≤ Real.sqrt (L * ∫ t in (0 : ℝ)..L, (curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (γ t') (σ • (d • V t'))) t) ^ 2)
    exact Real.le_sqrt_of_sq_le hcs
  rcases hev0 with h | h
  · refine ⟨d, hdpos, Or.inl ?_⟩
    filter_upwards [h, (hsmooth d ⟨hdpos, hdc₁⟩).filter_mono nhdsWithin_le_nhds]
      with σ hσE hσsm
    have h1 : curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (γ t) (σ • (d • V t))) 0 L
        ≤ Real.sqrt (L * E σ) := hlen σ hσsm.2
    have h2 : Real.sqrt (L * E σ) < L := by
      rw [Real.sqrt_lt' hL]
      have h3 := mul_lt_mul_of_pos_left hσE hL
      rw [hE0] at h3
      simpa only [pow_two] using h3
    linarith
  · refine ⟨d, hdpos, Or.inr ?_⟩
    filter_upwards [h, (hsmooth d ⟨hdpos, hdc₁⟩).filter_mono nhdsWithin_le_nhds]
      with σ hσE hσsm
    have h1 : curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (γ t) (σ • (d • V t))) 0 L
        ≤ Real.sqrt (L * E σ) := hlen σ hσsm.2
    have h2 : Real.sqrt (L * E σ) < L := by
      rw [Real.sqrt_lt' hL]
      have h3 := mul_lt_mul_of_pos_left hσE hL
      rw [hE0] at h3
      simpa only [pow_two] using h3
    linarith


end

end Submission.EnergyShorten
