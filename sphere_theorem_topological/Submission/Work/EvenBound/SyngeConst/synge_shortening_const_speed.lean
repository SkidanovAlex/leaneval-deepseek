import Mathlib
import Submission.Work.EvenBound.Imports

namespace Work.EvenBound.SyngeConst

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open scoped Interval
open scoped MeasureTheory
open MeasureTheory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Synge's shortening lemma, constant-speed form.**  A closed geodesic `γ` of *constant* speed
`c > 0` (so length `c * L` on `[0,L]`) carrying a smooth, parallel, periodic, unit, normal field `X`
can be shortened by closed curves: for all small `σ` on one side of `0` the curves
`t ↦ GExp (γ t) (σ • (d • X t))` are closed and have length `< c * L`.

This is a copy of `Submission.SyngeShorten.exists_shorter_closed_curve` (the case `c = 1`) with the
unit-speed hypothesis `curveSpeed γ = 1` replaced by constant speed `c`: the only places the number
`1` enters are `curveSpeed γ = 1` (giving `E(0) = L`, the energy of the geodesic) and the final
Cauchy–Schwarz step, which becomes `length ≤ √(L · E σ) < √(L · c² L) = c L`.  The underlying second
variation input `Submission.EnergyGeoShorten.exists_energy_lt_of_positive_curvature_geodesic` (and
`Submission.EnergyShorten.exists_energy_lt_of_positive_curvature`) already carry no norm or
unit-speed hypothesis; only the length transfer
`Submission.EnergyGeoShorten.exists_curveLength_lt_of_positive_curvature_geodesic` has to be redone
with the constant speed `c` and conclusion `< c * L`. -/
theorem synge_shortening_const_speed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (hloop : γ L = γ 0)
    (hspeed : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = c)
    {X : (t : ℝ) → TangentSpace I (γ t)}
    (hXs : ∀ s ∈ Set.Icc (0 - 1) (L + 1),
      Submission.JacobiGlobal.SmoothAlongAt (I := I) γ X s)
    (hXpar : ∀ s ∈ Set.Icc (0 - 1) (L + 1), Submission.JacobiGlobal.covAlong cov X s = 0)
    (hXper : X L = X 0)
    (hX1 : ∀ t ∈ Set.Icc (0 : ℝ) L, ‖X t‖ = 1)
    (hXnorm : ∀ t ∈ Set.Icc (0 : ℝ) L,
      inner ℝ (X t) (Submission.Geodesic.curveVelocity (I := I) γ t) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) u v v) u) :
    ∃ d : ℝ, 0 < d ∧
      (((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          Submission.Length.curveLength (I := I)
            (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • (d • X t))) 0 L < c * L ∧
          Submission.GlobalExp.GExp (cov := cov) hmet (γ L) (σ • (d • X L))
            = Submission.GlobalExp.GExp (cov := cov) hmet (γ 0) (σ • (d • X 0))) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          Submission.Length.curveLength (I := I)
            (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • (d • X t))) 0 L < c * L ∧
          Submission.GlobalExp.GExp (cov := cov) hmet (γ L) (σ • (d • X L))
            = Submission.GlobalExp.GExp (cov := cov) hmet (γ 0) (σ • (d • X 0))))) := by
  classical
  -- The velocity has constant norm `c` on `[0,L]`.
  have hvel : ∀ t ∈ Set.Icc (0 : ℝ) L,
      ‖Submission.Geodesic.curveVelocity (I := I) γ t‖ = c := by
    intro t ht
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) γ t]
    exact hspeed t ht
  -- Positivity of the curvature pairing at the *true* velocity (norm `c`, not `1`).
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < inner ℝ
      (Submission.CurvatureVec.curvVec cov (γ t) (X t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)) (X t) := by
    intro t ht
    set w : TangentSpace I (γ t) := (c⁻¹ : ℝ) • Submission.Geodesic.curveVelocity (I := I) γ t
      with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hc)), hvel t ht]
      exact inv_mul_cancel₀ (ne_of_gt hc)
    have hwo : inner ℝ (X t) w = 0 := by
      rw [hw, inner_smul_right, hXnorm t ht, mul_zero]
    have hv : Submission.Geodesic.curveVelocity (I := I) γ t = c • w := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
    rw [hv]
    have hcurvred : inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) (X t) (c • w) (c • w)) (X t)
        = c ^ 2 * inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) (X t) w w) (X t) := by
      simp only [Submission.CurvatureVec.curvVec_smul_middle,
        Submission.CurvatureVec.curvVec_smul_right, smul_smul,
        inner_smul_left, starRingEnd_apply, star_trivial]
      ring
    rw [hcurvred]
    have hc2 : (0 : ℝ) < c ^ 2 := by positivity
    exact mul_pos hc2 (lt_of_lt_of_le hδ (hcurv t ht (X t) w (hX1 t ht) hwn hwo))
  -- The energy shortening input.
  obtain ⟨c₀, hc₀pos, hspec⟩ :=
    Submission.EnergyGeoGlobal.energy_second_deriv_geodesic' (cov := cov) hmet htor
      (contMDiffOn_univ.mpr hγsm) hgeo hne
      (fun s hs => hXs s ⟨by linarith [hs.1], hs.2⟩) hL
  obtain ⟨c₁, hc₁pos, hsmooth⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_geodesic_family (cov := cov) hmet htor
      (contMDiffOn_univ.mpr hγsm)
      (fun s hs => hXs s ⟨by linarith [hs.1], hs.2⟩) hL
  set d : ℝ := min 1 (min c₀ c₁) with hddef
  have hdpos : 0 < d := by rw [hddef]; positivity
  have hdc₀ : d ≤ c₀ := by
    rw [hddef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hdc₁ : d ≤ c₁ := by
    rw [hddef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hdIoc : d ∈ Set.Ioc (0 : ℝ) c₀ := ⟨hdpos, hdc₀⟩
  obtain ⟨hsec, hdiff0, hdifev⟩ := hspec d hdIoc
  set E : ℝ → ℝ := fun σ : ℝ => ∫ t in (0 : ℝ)..L, (Submission.Length.curveSpeed (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (σ • (d • X s))) t) ^ 2
    with hEdef
  -- The scaled index integral is negative.
  have hcovs : Submission.JacobiGlobal.covAlong cov (fun s : ℝ => d • X s)
      = fun s : ℝ => d • Submission.JacobiGlobal.covAlong cov X s := by
    funext v
    exact Submission.IndexScale.covAlong_smul (cov := cov) htor γ X d v
  have hpoint : ∀ t : ℝ, Submission.IndexIntrinsic.idxAlong (cov := cov) γ (fun s => d • X s)
      (Submission.JacobiGlobal.covAlong cov (fun s => d • X s)) t
      = d ^ 2 * Submission.IndexIntrinsic.idxAlong (cov := cov) γ X
          (Submission.JacobiGlobal.covAlong cov X) t := by
    intro t
    rw [hcovs]
    exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor γ X
      (Submission.JacobiGlobal.covAlong cov X) d t
  have hInt : (∫ t in (0 : ℝ)..L, Submission.IndexIntrinsic.idxAlong (cov := cov) γ (fun s => d • X s)
      (Submission.JacobiGlobal.covAlong cov (fun s => d • X s)) t)
      = d ^ 2 * ∫ t in (0 : ℝ)..L, Submission.IndexIntrinsic.idxAlong (cov := cov) γ X
          (Submission.JacobiGlobal.covAlong cov X) t := by
    rw [intervalIntegral.integral_congr (fun t _ => hpoint t), intervalIntegral.integral_const_mul]
  have hneg : ∫ t in (0 : ℝ)..L, Submission.IndexIntrinsic.idxAlong (cov := cov) γ X
      (Submission.JacobiGlobal.covAlong cov X) t < 0 :=
    Submission.EnergyShorten.integral_idxAlong_neg_of_parallel (cov := cov) hmet htor hL
      hγsm hne hXs hXpar hpos
  have hval : 2 * (∫ t in (0 : ℝ)..L, Submission.IndexIntrinsic.idxAlong (cov := cov) γ
      (fun s => d • X s)
      (Submission.JacobiGlobal.covAlong cov (fun s => d • X s)) t) < 0 := by
    rw [hInt]
    have hd2 : (0 : ℝ) < d ^ 2 := by positivity
    have hmul : d ^ 2 * (∫ t in (0 : ℝ)..L, Submission.IndexIntrinsic.idxAlong (cov := cov) γ X
        (Submission.JacobiGlobal.covAlong cov X) t) < 0 := mul_neg_of_pos_of_neg hd2 hneg
    linarith
  have hderiv : HasDerivAt (deriv E) (2 * (∫ t in (0 : ℝ)..L,
      Submission.IndexIntrinsic.idxAlong (cov := cov) γ (fun s => d • X s)
        (Submission.JacobiGlobal.covAlong cov (fun s => d • X s)) t)) 0 := by
    rw [hEdef]
    exact hsec
  have h00 : HasDerivAt E (deriv E 0) 0 := hdiff0.hasDerivAt
  have hev0 : (∀ᶠ σ in 𝓝[>] (0 : ℝ), E σ < E 0) ∨ (∀ᶠ σ in 𝓝[<] (0 : ℝ), E σ < E 0) :=
    Submission.DerivShorten.eventually_lt_or_eventually_lt_of_deriv_deriv_neg h00 hderiv hval hdifev
  -- `E 0 = c ^ 2 * L`: the energy of the geodesic `γ`, of constant speed `c`.
  have hE0 : E 0 = c ^ 2 * L := by
    show (∫ t in (0 : ℝ)..L, (Submission.Length.curveSpeed (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s)
        ((0 : ℝ) • (d • X s))) t) ^ 2) = c ^ 2 * L
    have hfun : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s)
        ((0 : ℝ) • (d • X s))) = γ := by
      funext s
      rw [zero_smul, Submission.GlobalExp.GExp_zero]
    rw [hfun]
    have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) L →
        (Submission.Length.curveSpeed (I := I) γ t) ^ 2 = c ^ 2 := by
      filter_upwards with t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) L := by
        rw [Set.uIoc_of_le hL.le] at ht
        exact ⟨ht.1.le, ht.2⟩
      rw [hspeed t ht']
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero]
    ring
  -- The Cauchy-Schwarz length transfer.
  have hlen : ∀ σ : ℝ, ContinuousOn (fun t : ℝ => Submission.Length.curveSpeed (I := I)
      (fun t' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
        (γ t') (σ • (d • X t'))) t) (Set.Icc 0 L) →
      Submission.Length.curveLength (I := I) (fun t : ℝ => Submission.GlobalExp.GExp
        (cov := cov) hmet (γ t) (σ • (d • X t))) 0 L ≤ Real.sqrt (L * E σ) := by
    intro σ hcont
    have hcs := Commons.MeasureTheory.IntervalIntegral.sq_integral_le_mul_integral_sq
      (f := fun t : ℝ => Submission.Length.curveSpeed (I := I)
        (fun t' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
          (γ t') (σ • (d • X t'))) t) hL.le
      (hcont.intervalIntegrable_of_Icc hL.le)
      ((hcont.pow 2).intervalIntegrable_of_Icc hL.le)
    rw [sub_zero] at hcs
    rw [Submission.Length.curveLength_def]
    show (∫ t in (0 : ℝ)..L, Submission.Length.curveSpeed (I := I)
        (fun t' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
          (γ t') (σ • (d • X t'))) t) ≤ Real.sqrt (L * ∫ t in (0 : ℝ)..L,
        (Submission.Length.curveSpeed (I := I) (fun t' : ℝ => Submission.GlobalExp.GExp
          (cov := cov) hmet (γ t') (σ • (d • X t'))) t) ^ 2)
    exact Real.le_sqrt_of_sq_le hcs
  -- The shortened curves are closed.
  have hclosed : ∀ σ : ℝ, Submission.GlobalExp.GExp (cov := cov) hmet (γ L) (σ • (d • X L))
      = Submission.GlobalExp.GExp (cov := cov) hmet (γ 0) (σ • (d • X 0)) := by
    intro σ
    have h1 : (σ • (d • X L) : TangentSpace I (γ L)) = σ • (d • X 0) := by
      rw [hXper]
    rw [h1, hloop]
  rcases hev0 with h | h
  · refine ⟨d, hdpos, Or.inl ?_⟩
    filter_upwards [h, (hsmooth d ⟨hdpos, hdc₁⟩).filter_mono nhdsWithin_le_nhds]
      with σ hσE hσsm
    have h1 : Submission.Length.curveLength (I := I) (fun t : ℝ => Submission.GlobalExp.GExp
        (cov := cov) hmet (γ t) (σ • (d • X t))) 0 L ≤ Real.sqrt (L * E σ) := hlen σ hσsm.2
    have h2 : Real.sqrt (L * E σ) < c * L := by
      rw [Real.sqrt_lt' (mul_pos hc hL)]
      have h3 := mul_lt_mul_of_pos_left hσE hL
      rw [hE0] at h3
      nlinarith [h3]
    exact ⟨lt_of_le_of_lt h1 h2, hclosed σ⟩
  · refine ⟨d, hdpos, Or.inr ?_⟩
    filter_upwards [h, (hsmooth d ⟨hdpos, hdc₁⟩).filter_mono nhdsWithin_le_nhds]
      with σ hσE hσsm
    have h1 : Submission.Length.curveLength (I := I) (fun t : ℝ => Submission.GlobalExp.GExp
        (cov := cov) hmet (γ t) (σ • (d • X t))) 0 L ≤ Real.sqrt (L * E σ) := hlen σ hσsm.2
    have h2 : Real.sqrt (L * E σ) < c * L := by
      rw [Real.sqrt_lt' (mul_pos hc hL)]
      have h3 := mul_lt_mul_of_pos_left hσE hL
      rw [hE0] at h3
      nlinarith [h3]
    exact ⟨lt_of_le_of_lt h1 h2, hclosed σ⟩

end Work.EvenBound.SyngeConst
