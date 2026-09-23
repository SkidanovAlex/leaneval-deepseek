import Submission.EnergyRayGlobal
import Submission.ConjEnergy
import Submission.Commons.MeasureTheory.IntervalIntegral.integral_pos_of_continuousOn_of_pos
import Submission.DerivShorten
import Submission.EnergyRaySmooth
import Submission.Commons.MeasureTheory.IntervalIntegral.sq_integral_le_mul_integral_sq
import Submission.IndexScale

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The shortening of a geodesic variation with negative second variation

**`exists_energy_lt_of_integral_neg`**: along a `GExp`-ray `γ(t) = GExp p (t • ξ)` (`ξ ≠ 0`), for a
field `V` that is smooth along the ray, if the **index integral**

`∫_a^b idxAlong γ V (∇ V) < 0`

is *negative* (this is the case for a **closed parallel unit normal field** on a closed geodesic of
positive curvature: `idxAlong = -⟨R(V,γ')γ',V⟩ = -sec` there), then the energy of the geodesic
variation `Φ(σ,t) = GExp (γ t) (σ • d • V t)` is **strictly smaller** than the energy of the base
curve `γ` itself, on one side of `σ = 0`:

`E(σ) < E(0) = ∫_a^b ‖γ'‖²` for all small `σ` on one side (an interval `(0,δ)` or `(-δ,0)`).

This is the **shortening step** of Klingenberg's injectivity-radius estimate (Roadmap §112.2 step 4):
combined with the Cauchy–Schwarz bound `L(c_σ) ≤ √((b-a) E(σ))` it produces closed curves strictly
shorter than the closed geodesic, which is the input of Klingenberg's lifting argument.

The proof combines
* `Submission.EnergyRayGlobal.energy_second_deriv_ray'` (the second variation of the energy of the
  variation by geodesics, which is `2 ∫ idxAlong`), with the fact that the integrand is *quadratic*
  in the scaling `d` (`IndexScale.idxAlong_smul`) — so the scaled integral is `d² ∫ idxAlong < 0`;
* `Submission.DerivShorten.eventually_lt_or_eventually_lt_of_deriv_deriv_neg` (a strictly negative
  second derivative with a vanishing or nonzero first derivative gives the one-sided inequality).
-/

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

/-- **The shortening of a geodesic variation with negative index integral.** -/
theorem exists_energy_lt_of_integral_neg
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hab : a < b)
    (hint : ∫ t in a..b, idxAlong (cov := cov)
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V (covAlong cov V) t < 0) :
    ∃ d : ℝ, 0 < d ∧
      (((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) ^ 2) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) ^ 2))) := by
  classical
  obtain ⟨c₀, hc₀pos, hspec⟩ :=
    Submission.EnergyRayGlobal.energy_second_deriv_ray' (cov := cov) hmet htor hξ hVs hab
  refine ⟨min 1 c₀, by positivity, ?_⟩
  have hdmem : min 1 c₀ ∈ Set.Ioc (0 : ℝ) c₀ := ⟨by positivity, min_le_right _ _⟩
  obtain ⟨hsec, hdiff0, hdifev⟩ := hspec _ hdmem
  -- the energy of the scaled variation
  set E : ℝ → ℝ := fun σ : ℝ => ∫ t in a..b, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
        (σ • (min 1 c₀ • V s))) t) ^ 2 with hEdef
  -- the scaling identity for the index integral
  have hcov : covAlong cov (fun s : ℝ => min 1 c₀ • V s)
      = fun s : ℝ => min 1 c₀ • covAlong cov V s := by
    funext v
    exact Submission.IndexScale.covAlong_smul (cov := cov) htor
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V (min 1 c₀) v
  have hpoint : ∀ t : ℝ, idxAlong (cov := cov)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t
      = (min 1 c₀) ^ 2 * idxAlong (cov := cov)
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V (covAlong cov V) t := by
    intro t
    rw [hcov]
    exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V (covAlong cov V) (min 1 c₀) t
  have hInt : (∫ t in a..b, idxAlong (cov := cov)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t)
      = (min 1 c₀) ^ 2 * ∫ t in a..b, idxAlong (cov := cov)
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V (covAlong cov V) t := by
    rw [intervalIntegral.integral_congr (fun t _ => hpoint t),
      intervalIntegral.integral_const_mul]
  have hval : 2 * (∫ t in a..b, idxAlong (cov := cov)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t) < 0 := by
    rw [hInt]
    have hd2 : (0 : ℝ) < (min 1 c₀) ^ 2 := by positivity
    have hmul : (min 1 c₀) ^ 2 * (∫ t in a..b, idxAlong (cov := cov)
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V (covAlong cov V) t) < 0 :=
      mul_neg_of_pos_of_neg hd2 hint
    linarith
  -- the calculus lemma
  have hderiv : HasDerivAt (deriv E) (2 * (∫ t in a..b, idxAlong (cov := cov)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) (fun s => min 1 c₀ • V s)
      (covAlong cov (fun s => min 1 c₀ • V s)) t)) 0 := by
    rw [hEdef]
    exact hsec
  have h00 : HasDerivAt E (deriv E 0) 0 := hdiff0.hasDerivAt
  have hev : (∀ᶠ σ in 𝓝[>] (0 : ℝ), E σ < E 0) ∨ (∀ᶠ σ in 𝓝[<] (0 : ℝ), E σ < E 0) :=
    eventually_lt_or_eventually_lt_of_deriv_deriv_neg h00 hderiv hval hdifev
  have hE0 : (∫ t in a..b, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
        ((0 : ℝ) • (min 1 c₀ • V s))) t) ^ 2)
      = ∫ t in a..b, (curveSpeed (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hfun : (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
        ((0 : ℝ) • (min 1 c₀ • V s)))
        = (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) := by
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

/-- **The index integrand of a parallel field is minus the curvature pairing.**  If `∇V = 0` then
`idxAlong γ V (∇V) t = -⟨R(V t, γ'(t))γ'(t), V t⟩`, so for a *positive* curvature pairing the
integrand is negative. -/
theorem idxAlong_eq_neg_of_parallel (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hpar : covAlong cov V t = 0) :
    idxAlong (cov := cov) γ V (covAlong cov V) t
      = -inner ℝ (curvVec cov (γ t) (V t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t)) (V t) := by
  rw [idxAlong, hpar, inner_zero_left, zero_sub]

/-- **The index integral of a parallel field with positive curvature pairing is negative.** -/
theorem integral_idxAlong_neg_of_parallel
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s)
    (hpar : ∀ s ∈ Icc (a - 1) (b + 1), covAlong cov V s = 0)
    (hpos : ∀ t ∈ Icc a b, 0 < inner ℝ (curvVec cov (γ t) (V t)
      (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (V t)) :
    ∫ t in a..b, idxAlong (cov := cov) γ V (covAlong cov V) t < 0 := by
  -- the pointwise identity
  have hpoint : ∀ t ∈ Icc a b, idxAlong (cov := cov) γ V (covAlong cov V) t
      = -(inner ℝ (curvVec cov (γ t) (V t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t)) (V t)) := by
    intro t ht
    exact idxAlong_eq_neg_of_parallel (cov := cov) htor
      (hpar t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  -- continuity of the curvature pairing
  have hcont : ContinuousOn (fun t : ℝ => inner ℝ (curvVec cov (γ t) (V t)
      (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (V t)) (Icc a b) := by
    have h1 : ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ V (covAlong cov V) t)
        (Icc a b) :=
      Submission.ConjEnergy.continuousOn_idxAlong_of_smooth (cov := cov) htor hab.le hγ hne hVs
    refine (h1.neg).congr ?_
    intro t ht
    show inner ℝ (curvVec cov (γ t) (V t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t)) (V t)
      = -(idxAlong (cov := cov) γ V (covAlong cov V) t)
    rw [hpoint t ht, neg_neg]
  have hInt : (∫ t in a..b, idxAlong (cov := cov) γ V (covAlong cov V) t)
      = -(∫ t in a..b, inner ℝ (curvVec cov (γ t) (V t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t)) (V t)) := by
    rw [intervalIntegral.integral_congr (fun t ht =>
      hpoint t (by rwa [uIcc_of_le hab.le] at ht)), intervalIntegral.integral_neg]
  have hposint : 0 < ∫ t in a..b, inner ℝ (curvVec cov (γ t) (V t)
      (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (V t) :=
    Commons.MeasureTheory.IntervalIntegral.integral_pos_of_continuousOn_of_pos hab hcont hpos
  rw [hInt]
  linarith

/-- **The energy of a geodesic variation of a ray with positive curvature pairing is strict
smaller than the energy of the ray itself**, on one side of `σ = 0`.  This is the *geometric*
shortening statement: it combines the negative index integral
(`integral_idxAlong_neg_of_parallel`) with `exists_energy_lt_of_integral_neg`. -/
theorem exists_energy_lt_of_positive_curvature
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hpar : ∀ s ∈ Icc (a - 1) (b + 1), covAlong cov V s = 0)
    (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < inner ℝ
      (curvVec cov (GExp (cov := cov) hmet p (t • ξ)) (V t)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t)) (V t)) :
    ∃ d : ℝ, 0 < d ∧
      (((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) ^ 2) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          (∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
              (σ • (d • V s))) t) ^ 2)
          < ∫ t in a..b, (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t) ^ 2))) := by
  refine exists_energy_lt_of_integral_neg (cov := cov) hmet htor hξ hVs hab ?_
  exact integral_idxAlong_neg_of_parallel (cov := cov) hmet htor hab
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξ)
    (fun s => Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξ s)
    hVs hpar hpos

/-- **The shortening in its geometric form: a shorter curve of *length* strictly less than `L`.**
For a unit-speed `GExp`-ray of length `L` and a *parallel* field `V` with positive curvature pairing,
there is a scaling `d > 0` such that the curves `t ↦ GExp (γ t) (σ • (d • V t))` have
`curveLength < L` for all small `σ` on one side of `0`.

The transfer from energy to length is Cauchy–Schwarz:
`L(c_σ) = ∫ curveSpeed ≤ √(L · E(σ)) < √(L·L) = L` since `E(σ) < E(0) = L`. -/
theorem exists_curveLength_lt_of_positive_curvature
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0) (hξ1 : ‖ξ‖ = 1)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {L : ℝ}
    (hVs : ∀ s ∈ Icc (0 - 1) (L + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hpar : ∀ s ∈ Icc (0 - 1) (L + 1), covAlong cov V s = 0)
    (hL : 0 < L)
    (hpos : ∀ t ∈ Icc (0 : ℝ) L, 0 < inner ℝ
      (curvVec cov (GExp (cov := cov) hmet p (t • ξ)) (V t)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t)) (V t)) :
    ∃ d : ℝ, 0 < d ∧
      ((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
            (GExp (cov := cov) hmet p (t • ξ)) (σ • (d • V t))) 0 L < L) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
            (GExp (cov := cov) hmet p (t • ξ)) (σ • (d • V t))) 0 L < L)) := by
  classical
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ) with hγdef
  obtain ⟨c₀, hc₀pos, hspec⟩ :=
    Submission.EnergyRayGlobal.energy_second_deriv_ray' (cov := cov) hmet htor hξ
      (fun s hs => hVs s ⟨by linarith [hs.1], hs.2⟩) hL
  obtain ⟨c₁, hc₁pos, hsmooth⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_ray_family (cov := cov) hmet htor hξ
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
      (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
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
    integral_idxAlong_neg_of_parallel (cov := cov) hmet htor hL
      (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hξ)
      (fun s => Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξ s)
      hVs hpar hpos
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
  -- the energy of the ray at `0`
  have hspeed1 : ∀ t : ℝ, t ≠ 0 → curveSpeed (I := I) γ t = 1 := by
    intro t ht
    rw [hγdef, Submission.ConjEnergy.curveSpeed_ray (cov := cov) hmet p hξ ht, hξ1]
  have hEnonneg : ∀ σ : ℝ, 0 ≤ E σ := by
    intro σ
    show 0 ≤ ∫ t in (0 : ℝ)..L, (curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
        (σ • (d • V s))) t) ^ 2
    exact intervalIntegral.integral_nonneg hL.le (fun t _ => sq_nonneg _)
  have hE0 : E 0 = L := by
    show (∫ t in (0 : ℝ)..L, (curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet
      (GExp (cov := cov) hmet p (s • ξ)) ((0 : ℝ) • (d • V s))) t) ^ 2) = L
    have hfun : (fun s : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
        ((0 : ℝ) • (d • V s))) = γ := by
      funext s
      rw [hγdef, zero_smul, GExp_zero]
    rw [hfun]
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using measure_singleton (0 : ℝ)
    have hae : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) L → (curveSpeed (I := I) γ t) ^ 2 = (1 : ℝ) := by
      filter_upwards [hne] with t ht _
      rw [hspeed1 t ht, one_pow]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const,
      smul_eq_mul, mul_one, sub_zero]
  -- the length bound
  have hlen : ∀ σ : ℝ, ContinuousOn (fun t : ℝ => curveSpeed (I := I)
      (fun t' : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet p (t' • ξ))
        (σ • (d • V t'))) t) (Icc 0 L) →
      curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t • ξ)) (σ • (d • V t))) 0 L ≤ Real.sqrt (L * E σ) := by
    intro σ hcont
    have hcs := Commons.MeasureTheory.IntervalIntegral.sq_integral_le_mul_integral_sq
      (f := fun t : ℝ => curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t' • ξ)) (σ • (d • V t'))) t) hL.le
      (hcont.intervalIntegrable_of_Icc hL.le)
      ((hcont.pow 2).intervalIntegrable_of_Icc hL.le)
    rw [sub_zero] at hcs
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..L, curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t' • ξ)) (σ • (d • V t'))) t := by
      refine intervalIntegral.integral_nonneg hL.le (fun t _ => ?_)
      exact curveSpeed_nonneg (I := I) _ t
    rw [curveLength_def]
    show (∫ t in (0 : ℝ)..L, curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t' • ξ)) (σ • (d • V t'))) t)
      ≤ Real.sqrt (L * ∫ t in (0 : ℝ)..L, (curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t' • ξ)) (σ • (d • V t'))) t) ^ 2)
    exact Real.le_sqrt_of_sq_le hcs
  rcases hev0 with h | h
  · refine ⟨d, hdpos, Or.inl ?_⟩
    filter_upwards [h, (hsmooth d ⟨hdpos, hdc₁⟩).filter_mono nhdsWithin_le_nhds]
      with σ hσE hσsm
    have h1 : curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t • ξ)) (σ • (d • V t))) 0 L
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
        (GExp (cov := cov) hmet p (t • ξ)) (σ • (d • V t))) 0 L
        ≤ Real.sqrt (L * E σ) := hlen σ hσsm.2
    have h2 : Real.sqrt (L * E σ) < L := by
      rw [Real.sqrt_lt' hL]
      have h3 := mul_lt_mul_of_pos_left hσE hL
      rw [hE0] at h3
      simpa only [pow_two] using h3
    linarith

end

end Submission.EnergyShorten


