import Mathlib
import Submission.Work.Diff.C.jacobi_modulus_log_deriv_lower
import Submission.Work.Diff.C.hess_dist_jacobi_shapeOp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open Bundle
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic Submission.JacobiGlobal

/-!
# The log-derivative identity for the modulus of a Jacobi field

This is the first piece of the `hHess`-substitution in the geodesic-sphere size estimate
(`Work.Diff.C.far_sphere_size`): the classical identity

  `(d/dt) (½ log ⟪J t, J t⟫) = ⟪∇_{γ'} J (t), J t⟫ / ⟪J t, J t⟫`,

i.e. the radial derivative `(log ‖J‖)'` of a Jacobi field along a unit-speed geodesic equals the
shape operator of the geodesic spheres applied to `J`.  It follows immediately from the proved
`Work.Diff.C.jml_hasDerivAt_inner_self` (`(⟪J,J⟫)' = 2⟪∇_{γ'}J, J⟫`) together with the chain rule
for `Real.log`; no Jacobi theory is needed here.

Feeding `⟪∇_{γ'}J, J⟫/⟪J,J⟫ = rhess (rdist q) (γ t) (J t) (J t) / ⟪J t, J t⟫` (the bridge supplied by
`Work.Diff.C.hess_dist_jacobi_shapeOp` for `J(0) = 0`) and the two-sided shape-operator bound
`Work.Diff.C.rhess_rdist_bound_of_hHess` gives the `hHess` version of the Sturm/Riccati comparison
that `Work.Diff.C.jacobi_modulus_log_deriv_lower` performs under a pointwise `CurvLe`.
-/

/-- Real-variable form: if `g` has derivative `2 m` at `t` and `0 < g t`, then `½ log g` has
derivative `m / g t`. -/
theorem hasDerivAt_log_half {g m : ℝ → ℝ} {t : ℝ} (hg : HasDerivAt g (2 * m t) t)
    (hpos : 0 < g t) :
    HasDerivAt (fun s : ℝ => Real.log (g s) / 2) (m t / g t) t := by
  have hg' : HasDerivAt (fun s : ℝ => Real.log (g s)) ((g t)⁻¹ * (2 * m t)) t :=
    (Real.hasDerivAt_log (ne_of_gt hpos)).comp t hg
  have h2 : HasDerivAt (fun s : ℝ => Real.log (g s) / 2) (((g t)⁻¹ * (2 * m t)) / 2) t :=
    hg'.div_const 2
  have hval : ((g t)⁻¹ * (2 * m t)) / 2 = m t / g t := by
    field_simp
  rwa [hval] at h2

open Bundle in
/-- **The log-derivative identity for a Jacobi field.**  Along a `C^∞` curve `γ` with nowhere
vanishing velocity and a Jacobi field `J`, at every `t` with `J t ≠ 0`,

  `(d/dt) (½ log ⟪J t, J t⟫) = ⟪∇_{γ'} J (t), J t⟫ / ⟪J t, J t⟫`. -/
theorem jld_log_deriv_of_jacobi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {t : ℝ} (ht : J t ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log (Inner.inner ℝ (J s) (J s)) / 2)
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t)
        / Inner.inner ℝ (J t) (J t)) t := by
  have hdiff := jml_hasDerivAt_inner_self (I := I) (M := M) (cov := cov) hmet htor hγ hJ hne t
  have hpos : 0 < Inner.inner ℝ (J t) (J t) := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr ht) 2
  have h := hasDerivAt_log_half (g := fun s : ℝ => Inner.inner ℝ (J s) (J s))
    (m := fun _ : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t))
    hdiff hpos
  simpa using h

open Bundle in
/-- **The log-derivative of a Jacobi field with `J(0) = 0` is the shape operator.**  In the setting
of `Work.Diff.C.hess_dist_jacobi_shapeOp` (the ray `t ↦ GExp p (t • u)` is minimising on `[0,d]` and
`rdist p` is smooth with unit gradient at its endpoint), for `V` orthogonal to `rgrad (rdist p)` at
the endpoint and `V ≠ 0` there are a Jacobi field `Z` along the ray with `Z 0 = 0`, `Z d = V` and

  `(d/dt) (½ log ⟪Z t, Z t⟫)|_{t=d} = rhess cov (rdist p) (GExp p (d • u)) V V / ⟪V, V⟫`.

This is the input of the operator (Loewner) Riccati comparison for the geodesic-sphere size: it
converts the *two-sided* shape-operator bound (`Work.Diff.C.rhess_rdist_bound_of_hHess`) into a bound
on `(log ‖J‖)'`.  (`Work.Diff.C.jld_log_deriv_of_jacobi` is the log-derivative identity;
`Work.Diff.C.hess_dist_jacobi_shapeOp` provides `Z` and the bridge
`rhess … V V + (⟪rgrad (rdist p), V⟫)²/d = ⟪covAlong Z d, V⟫`.) -/
theorem jld_log_deriv_eq_rhess
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (p : M) {d : ℝ} (hd : 0 < d) {u : TangentSpace I p} (hu : ‖u‖ = 1)
    (hKd : Real.sqrt K * d < Real.pi)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) d,
      Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
        = ENNReal.ofReal t)
    (hminW : ∀ w : TangentSpace I p, ∀ᶠ s in 𝓝 (0 : ℝ),
      Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + s • w))
        = ENNReal.ofReal ‖(d • u) + s • w‖)
    (hF : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
    (hunit : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) = 1)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) I ((⊤ : ENat) : WithTop ENat)
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)))
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I)
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) t ≠ 0)
    (V : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
    (hV : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) V = 0)
    (hVne : V ≠ 0) :
    ∃ Z : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)),
      (∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) Z t) ∧
      Z 0 = 0 ∧ Z d = V ∧
      HasDerivAt (fun s : ℝ => Real.log (Inner.inner ℝ (Z s) (Z s)) / 2)
        (Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V
          / Inner.inner ℝ V V) d := by
  obtain ⟨Z, hjac, hZ0, hZd, hbridge⟩ :=
    hess_dist_jacobi_shapeOp (I := I) (M := M) (cov := cov) hmet htor hK hcurv p hd hu hKd
      hmin hminW hF hunit V
  refine ⟨Z, hjac, hZ0, hZd, ?_⟩
  have hld := jld_log_deriv_of_jacobi (I := I) (M := M) (cov := cov) hmet htor hγ hjac hne
    (t := d) (by rw [hZd]; exact hVne)
  have hterm : (Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M)
      (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) V) ^ 2 / d = 0 := by
    rw [hV]; ring
  have hcov : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) (Z d)
      = Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V := by
    rw [hZd]
    linarith [hbridge, hterm]
  rw [hcov, hZd] at hld
  exact hld

open Bundle in
/-- **`(log ‖J‖)'` for a Jacobi field** — the form of `Work.Diff.C.jld_log_deriv_of_jacobi` used by
the modulus comparison.  Unlike that lemma it is stated with `Real.log ‖J t‖` and therefore does not
need the caller to rewrite `⟪J,J⟫` as `‖J‖²`. -/
theorem jld_log_norm_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {t : ℝ} (ht : J t ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log ‖J s‖)
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t)
        / Inner.inner ℝ (J t) (J t)) t := by
  have h1 := jld_log_deriv_of_jacobi (I := I) (M := M) (cov := cov) hmet htor hγ hJ hne ht
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [real_inner_self_eq_norm_sq, Real.log_pow]
  push_cast
  ring

open Bundle in
/-- **The two-field pairing identity.**  For two Jacobi fields `J`, `K` along a `C^∞` curve `γ` with
nowhere vanishing velocity,

  `(d/dt) ⟪∇_{γ'} J, K⟫ = ⟪∇_{γ'} J, ∇_{γ'} K⟫ − ⟪R(J, γ')γ', K⟫`.

This polarises the proved `Work.Diff.C.jml_hasDerivAt_inner_covAlong` (the case `K = J`), via the
polarised index identity `Submission.IndexIntrinsic2.hasDerivAt_inner_bilAlong`; the only input on
`K` is that its chart coordinates in the chart of `J` are `C^∞`
(`Submission.JacobiGlobal.contDiffOn_chartCoords_of_isJacobiAt`), while the Jacobi equation is used
for `J` alone. -/
theorem jml_hasDerivAt_inner_covAlong_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J K : (t : ℝ) → TangentSpace I (γ t)}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hK : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ K t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0) :
    ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s) (K s))
      (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t)
          (Submission.JacobiGlobal.covAlong cov K t)
        - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) (J t)
            (Submission.Geodesic.curveVelocity (I := I) γ t)
            (Submission.Geodesic.curveVelocity (I := I) γ t)) (K t)) t := by
  intro t
  obtain ⟨x₀, η, hηpos, hηle, hsrcIcc, hcdu, hcdy, hframe, hjacIcc⟩ :=
    Submission.JacobiCoordsEq.exists_chartCoords_contDiffOn_eq (cov := cov) htor (γ := γ) (J := J)
      (s := t) (ε := 1) one_pos hγ.contMDiffOn (hJ t)
  -- chart coordinates of `γ`, `J` and `K`, all in the chart `x₀`
  set u : ℝ → E := Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ with hudef
  set y : ℝ → E := Submission.JacobiCoords.chartCoords (I := I) x₀ γ J with hydef
  set z : ℝ → E := Submission.JacobiCoords.chartCoords (I := I) x₀ γ K with hzdef
  have hUsub : Set.Ioo (t - η) (t + η) ⊆ Set.Icc (t - η) (t + η) := fun s hs => ⟨hs.1.le, hs.2.le⟩
  have htU : t ∈ Set.Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  have hUopen : IsOpen (Set.Ioo (t - η) (t + η)) := isOpen_Ioo
  have hsrcU : ∀ s ∈ Set.Ioo (t - η) (t + η), γ s ∈ (chartAt H x₀).source :=
    fun s hs => hsrcIcc s (hUsub hs)
  have hsrc : γ t ∈ (chartAt H x₀).source := hsrcU t htU
  have hcduO : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) u (Set.Ioo (t - η) (t + η)) := by
    rw [hudef]; exact hcdu.mono hUsub
  have hcdyO : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) y (Set.Ioo (t - η) (t + η)) := by
    rw [hydef]; exact hcdy.mono hUsub
  have hcdzO : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) z (Set.Ioo (t - η) (t + η)) := by
    rw [hzdef]
    exact Submission.JacobiGlobal.contDiffOn_chartCoords_of_isJacobiAt (cov := cov) htor hUopen
      (hγ.contMDiffOn.mono hUsub) hsrcU (fun s _ => hK s)
  have hcduO' : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (deriv u) (Set.Ioo (t - η) (t + η)) :=
    hcduO.deriv_of_isOpen hUopen (le_of_eq (by simp))
  have hcdyO' : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (deriv y) (Set.Ioo (t - η) (t + η)) :=
    hcdyO.deriv_of_isOpen hUopen (le_of_eq (by simp))
  have hduEv : ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcduO
  have hdyEv : ∀ᶠ s in 𝓝 t, HasDerivAt y (deriv y s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcdyO
  have hdzEv : ∀ᶠ s in 𝓝 t, HasDerivAt z (deriv z s) s :=
    Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcdzO
  have hddu : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcduO').self_of_nhds
  have hddy : HasDerivAt (deriv y) (deriv (deriv y) t) t :=
    (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen htU hcdyO').self_of_nhds
  have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H x₀).source :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htU) hsrcU
  have hutgtAt : ∀ s ∈ Set.Ioo (t - η) (t + η), u s ∈ (extChartAt I x₀).target := by
    intro s hs
    rw [hudef, Submission.IntrinsicVariation.chartCoord]
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsrcU s hs)
  have hutgtEv : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htU) hutgtAt
  have hγeqEv : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htU] with s hs
    rw [hudef, Submission.IntrinsicVariation.chartCoord]
    exact (PartialEquiv.left_inv (extChartAt I x₀)
      (by rw [extChartAt_source]; exact hsrcU s hs)).symm
  have hframeEv : ∀ᶠ s in 𝓝 t, Submission.Geodesic.frameVector (I := I) x₀ (γ s) (y s) = J s := by
    filter_upwards [isOpen_Ioo.mem_nhds htU] with s hs
    rw [hydef]
    exact hframe s (hUsub hs)
  have hframeKEv : ∀ᶠ s in 𝓝 t, Submission.Geodesic.frameVector (I := I) x₀ (γ s) (z s) = K s := by
    filter_upwards [isOpen_Ioo.mem_nhds htU] with s hs
    rw [hzdef]
    exact Submission.JacobiCoords.frameVector_chartCoords (I := I) (hsrcU s hs)
  have hjac : Submission.BonnetMyers.DtDsP cov x₀ u y (deriv u) (deriv y) t
      + Submission.Rauch.chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (deriv u t) = 0 := by
    have h := hjacIcc t ⟨htU.1.le, htU.2.le⟩
    simpa only [hudef, hydef] using h
  -- the covariant derivative of `J` in the coordinates `(u, y)`
  have hZev : (fun s : ℝ => Submission.JacobiGlobal.covAlong cov J s) =ᶠ[𝓝 t]
      (fun s : ℝ => Submission.Geodesic.frameVector (I := I) x₀ (γ s)
        (Submission.BonnetMyers.DtQ cov x₀ u y (deriv u) (deriv y) s)) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htU) (fun s hs => ?_)
    have hVsm : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ J s :=
      Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ hγ.contMDiffOn
    have hsrcEv' : ∀ᶠ r in 𝓝 s, γ r ∈ (chartAt H x₀).source :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) hsrcU
    have hutgtEv' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) hutgtAt
    have hγeqEv' : γ =ᶠ[𝓝 s] fun r => (extChartAt I x₀).symm (u r) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      rw [hudef, Submission.IntrinsicVariation.chartCoord]
      exact (PartialEquiv.left_inv (extChartAt I x₀)
        (by rw [extChartAt_source]; exact hsrcU r hr)).symm
    have hduEv' : ∀ᶠ r in 𝓝 s, HasDerivAt u (deriv u r) r :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcduO
    have hdyEv' : ∀ᶠ r in 𝓝 s, HasDerivAt y (deriv y r) r :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcdyO
    have hframeEv' : ∀ᶠ r in 𝓝 s, Submission.Geodesic.frameVector (I := I) x₀ (γ r) (y r) = J r := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      rw [hydef]
      exact hframe r (hUsub hr)
    exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor (γ := γ) (V := J) (t := s)
      hγ.contMDiffOn (hne s) hVsm (x₀ := x₀) (u := u) (w := deriv u) (y := y) (y' := deriv y)
      (hsrcU s hs) hsrcEv' hutgtEv' hγeqEv' hduEv' hframeEv' hdyEv'
  -- the covariant derivative of `K` in the same coordinates
  have hYev : (fun s : ℝ => Submission.JacobiGlobal.covAlong cov K s) =ᶠ[𝓝 t]
      (fun s : ℝ => Submission.Geodesic.frameVector (I := I) x₀ (γ s)
        (Submission.BonnetMyers.DtQ cov x₀ u z (deriv u) (deriv z) s)) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htU) (fun s hs => ?_)
    have hVsm : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ K s :=
      Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hK hγ.contMDiffOn
    have hsrcEv' : ∀ᶠ r in 𝓝 s, γ r ∈ (chartAt H x₀).source :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) hsrcU
    have hutgtEv' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) hutgtAt
    have hγeqEv' : γ =ᶠ[𝓝 s] fun r => (extChartAt I x₀).symm (u r) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      rw [hudef, Submission.IntrinsicVariation.chartCoord]
      exact (PartialEquiv.left_inv (extChartAt I x₀)
        (by rw [extChartAt_source]; exact hsrcU r hr)).symm
    have hduEv' : ∀ᶠ r in 𝓝 s, HasDerivAt u (deriv u r) r :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcduO
    have hdzEv' : ∀ᶠ r in 𝓝 s, HasDerivAt z (deriv z r) r :=
      Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn hUopen hs hcdzO
    have hframeEv' : ∀ᶠ r in 𝓝 s, Submission.Geodesic.frameVector (I := I) x₀ (γ r) (z r) = K r := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      rw [hzdef]
      exact Submission.JacobiCoords.frameVector_chartCoords (I := I) (hsrcU r hr)
    exact Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor (γ := γ) (V := K) (t := s)
      hγ.contMDiffOn (hne s) hVsm (x₀ := x₀) (u := u) (w := deriv u) (y := z) (y' := deriv z)
      (hsrcU s hs) hsrcEv' hutgtEv' hγeqEv' hduEv' hframeEv' hdzEv'
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t := hγ.contMDiffAt.mdifferentiableAt (by simp)
  have hVev : J =ᶠ[𝓝 t]
      (fun s : ℝ => Submission.Geodesic.frameVector (I := I) x₀ (γ s) (y s)) := by
    filter_upwards [hframeEv] with s hs
    exact hs.symm
  have hWev : K =ᶠ[𝓝 t]
      (fun s : ℝ => Submission.Geodesic.frameVector (I := I) x₀ (γ s) (z s)) := by
    filter_upwards [hframeKEv] with s hs
    exact hs.symm
  have hres := Submission.IndexIntrinsic2.hasDerivAt_inner_bilAlong (cov := cov) hmet htor x₀
    (γ := γ) (V := J) (Z := Submission.JacobiGlobal.covAlong cov J)
    (W := K) (Y := Submission.JacobiGlobal.covAlong cov K)
    (u := u) (w := deriv u) (w' := deriv (deriv u))
    (J := y) (J' := deriv y) (J'' := deriv (deriv y)) (Wc := z) (Wc' := deriv z) (t := t)
    hsrc hutgtEv hγeqEv hduEv hγmd hddu hdyEv.self_of_nhds hddy hjac hVev hZev
    hdzEv.self_of_nhds hWev hYev
  simpa only [Submission.IndexIntrinsic2.bilAlong] using hres

end Work.Diff.C
