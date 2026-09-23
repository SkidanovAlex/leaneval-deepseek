import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra

namespace Work.OddBound.indexTransfer

/-- Transfer of a second derivative along the reparametrisation `σ ↦ σ * d` (`d ≠ 0`):
if `σ ↦ F (σ * d)` has second derivative `L` at `0`, so does `F`, with the second
derivative scaled by `d⁻²`. -/
lemma hasDerivAt_deriv_comp_mul_right {F : ℝ → ℝ} {L d : ℝ} (hd : d ≠ 0)
    (h : HasDerivAt (deriv (fun σ : ℝ => F (σ * d))) L 0) :
    HasDerivAt (deriv F) (L / d ^ 2) 0 := by
  have hderiv : deriv (fun σ : ℝ => F (σ * d)) = fun σ : ℝ => deriv F (σ * d) * d := by
    have hfun : (fun σ : ℝ => F (σ * d)) = fun σ : ℝ => F (d * σ) := by
      funext σ; rw [mul_comm]
    rw [hfun]
    funext σ
    rw [deriv_comp_mul_left, smul_eq_mul, mul_comm d σ]
    exact mul_comm _ _
  rw [hderiv] at h
  have h₂ : HasDerivAt (fun σ : ℝ => deriv F (σ * d)) (L / d) 0 := by
    have hdiv := h.div_const d
    refine hdiv.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext σ
    rw [mul_div_cancel_right₀ _ hd]
  have h₃ : HasDerivAt (deriv F) ((L / d) * d⁻¹) 0 := by
    have h' : HasDerivAt (fun σ : ℝ => deriv F (σ * d)) (L / d) ((fun τ : ℝ => τ * d⁻¹) 0) := by
      simpa using h₂
    have hcomp : HasDerivAt ((fun σ : ℝ => deriv F (σ * d)) ∘ fun τ : ℝ => τ * d⁻¹)
        ((L / d) * d⁻¹) 0 := h'.comp 0 (hasDerivAt_mul_const d⁻¹)
    refine hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext τ
    show deriv F τ = deriv F ((τ * d⁻¹) * d)
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have hval : (L / d) * d⁻¹ = L / d ^ 2 := by field_simp
  rwa [hval] at h₃

theorem secondVariation_unscaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ℕ∞) : WithTop ℕ∞)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ Set.univ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    (hVs : ∀ s ∈ Set.Icc (a - 1) (b + 1), Submission.JacobiGlobal.SmoothAlongAt (I := I) γ V s)
    (hab : a < b) :
    (HasDerivAt (deriv (fun σ : ℝ => intervalIntegral (fun t : ℝ =>
        (Submission.Length.curveSpeed (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2)
        a b MeasureTheory.volume))
        (2 * intervalIntegral (fun t : ℝ => Submission.IndexIntrinsic.idxAlong (cov := cov) γ V
          (Submission.JacobiGlobal.covAlong cov V) t) a b MeasureTheory.volume) 0) ∧
    (DifferentiableAt ℝ (fun σ : ℝ => intervalIntegral (fun t : ℝ =>
        (Submission.Length.curveSpeed (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2)
        a b MeasureTheory.volume) 0) ∧
    (∀ᶠ σ in nhds (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => intervalIntegral (fun t : ℝ =>
        (Submission.Length.curveSpeed (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2)
        a b MeasureTheory.volume) σ) := by
  -- the rescaled form, available for every `d` in a small interval of scales
  obtain ⟨c₀, _hc₀pos, hspec⟩ :=
    Submission.EnergyGeoGlobal.energy_second_deriv_geodesic' (cov := cov) hmet htor hγsm hgeo hne hVs hab
  set d : ℝ := c₀ / 2 with hd_def
  have hdpos : 0 < d := by rw [hd_def]; linarith
  have hdle : d ≤ c₀ := by rw [hd_def]; linarith
  have hdne : d ≠ 0 := ne_of_gt hdpos
  obtain ⟨h1, h2, h3⟩ := hspec d ⟨hdpos, hdle⟩
  -- the two energy functions `E` (the target) and `G` (its reparametrisation `σ ↦ E (σ * d)`)
  set E : ℝ → ℝ := fun σ : ℝ => intervalIntegral (fun t : ℝ =>
      (Submission.Length.curveSpeed (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (σ • V s)) t) ^ 2)
      a b MeasureTheory.volume with hE_def
  set G : ℝ → ℝ := fun σ : ℝ => intervalIntegral (fun t : ℝ =>
      (Submission.Length.curveSpeed (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2)
      a b MeasureTheory.volume with hG_def
  -- the index integral of `V`, and the second variation of `G`
  set I : ℝ := intervalIntegral (fun t : ℝ => Submission.IndexIntrinsic.idxAlong (cov := cov) γ V
      (Submission.JacobiGlobal.covAlong cov V) t) a b MeasureTheory.volume with hI_def
  set L : ℝ := 2 * intervalIntegral (fun t : ℝ => Submission.IndexIntrinsic.idxAlong (cov := cov) γ
      (fun s : ℝ => d • V s) (Submission.JacobiGlobal.covAlong cov (fun s : ℝ => d • V s)) t)
      a b MeasureTheory.volume with hL_def
  show (HasDerivAt (deriv E) (2 * I) 0) ∧ (DifferentiableAt ℝ E 0) ∧
    (∀ᶠ σ in nhds (0 : ℝ), DifferentiableAt ℝ E σ)
  have h1G : HasDerivAt (deriv G) L 0 := by rw [hL_def]; exact h1
  -- `G σ = E (σ * d)`, because `σ • (d • V s) = (σ * d) • V s`
  have hG_eq : G = fun σ : ℝ => E (σ * d) := by
    funext σ
    simp only [hG_def, hE_def]
    rw [show (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (σ • (d • V s)))
        = (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) ((σ * d) • V s)) from by
      funext s; rw [smul_smul]]
  have h1b : HasDerivAt (deriv (fun σ : ℝ => E (σ * d))) L 0 :=
    h1G.congr_of_eventuallyEq ((Filter.EventuallyEq.of_eq hG_eq.symm).deriv)
  have hfinal : HasDerivAt (deriv E) (L / d ^ 2) 0 :=
    hasDerivAt_deriv_comp_mul_right hdne h1b
  -- the index integrand is homogeneous of degree two, so `L / d ^ 2 = 2 * I`
  have hsmul : ∀ (σ : ℝ) (s : ℝ), (σ * d⁻¹) • (d • V s) = σ • V s := by
    intro σ s
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hdne, mul_one]
  have hIdxpt : ∀ t : ℝ, Submission.IndexIntrinsic.idxAlong (cov := cov) γ (fun s : ℝ => d • V s)
      (fun s : ℝ => Submission.JacobiGlobal.covAlong cov (fun s' : ℝ => d • V s') s) t
      = d ^ 2 * Submission.IndexIntrinsic.idxAlong (cov := cov) γ V
        (Submission.JacobiGlobal.covAlong cov V) t := by
    intro t
    have hZ : (fun s : ℝ => Submission.JacobiGlobal.covAlong cov (fun s' : ℝ => d • V s') s)
        = fun s : ℝ => d • Submission.JacobiGlobal.covAlong cov V s := by
      funext s
      exact Submission.IndexScale.covAlong_smul (cov := cov) htor γ V d s
    rw [hZ]
    exact Submission.IndexScale.idxAlong_smul (cov := cov) hmet htor γ V
      (Submission.JacobiGlobal.covAlong cov V) d t
  have hLval : L = 2 * (d ^ 2 * I) := by
    rw [hL_def, hI_def]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => hIdxpt t)
  have hval : L / d ^ 2 = 2 * I := by
    rw [hLval]; field_simp
  -- `E = fun τ ↦ G (τ * d⁻¹)`, the inverse reparametrisation
  have hfun : E = fun τ : ℝ => G (τ * d⁻¹) := by
    funext τ
    simp only [hE_def, hG_def]
    rw [show (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) ((τ * d⁻¹) • (d • V s)))
        = (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ s) (τ • V s)) from by
      funext s; rw [hsmul τ s]]
  refine ⟨?_, ?_, ?_⟩
  · rw [hval] at hfinal
    exact hfinal
  · rw [hfun]
    have h2' : DifferentiableAt ℝ G ((fun τ : ℝ => τ * d⁻¹) 0) := by simpa using h2
    exact h2'.comp 0 (differentiableAt_id.mul_const d⁻¹)
  · have hcont : Filter.Tendsto (fun σ : ℝ => σ * d⁻¹) (nhds (0:ℝ)) (nhds (0:ℝ)) := by
      simpa using ((continuousAt_id (x := (0:ℝ))).mul_const d⁻¹).tendsto
    have hpre : ∀ᶠ σ in nhds (0:ℝ), DifferentiableAt ℝ G (σ * d⁻¹) :=
      hcont.eventually h3
    filter_upwards [hpre] with σ hσ
    rw [hfun]
    exact hσ.comp σ (differentiableAt_id.mul_const d⁻¹)

end Work.OddBound.indexTransfer
