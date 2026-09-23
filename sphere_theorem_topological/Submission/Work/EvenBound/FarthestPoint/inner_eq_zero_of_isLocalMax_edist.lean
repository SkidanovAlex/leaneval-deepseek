import Mathlib
import Submission.Work.EvenBound.Imports
import Submission.Work.EvenBound.FarthestPoint.hasDerivAt_norm_comp
import Submission.Work.EvenBound.FarthestPoint.edist_GExp_eq_norm_of_injAtLeast

namespace Work.EvenBound.FarthestPoint

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

private lemma hasDerivAt_extChartAt_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {x₀ : M} {σ : ℝ → M} (hσ0 : σ 0 = x₀) (hσ : MDifferentiableAt 𝓘(ℝ) I σ 0) :
    HasDerivAt (fun s : ℝ => (extChartAt I x₀) (σ s)) (curveVelocity (I := I) σ 0) 0 := by
  have he : MDifferentiableAt I 𝓘(ℝ, E) (fun z : M => (extChartAt I x₀) z) (σ 0) := by
    rw [hσ0]
    exact mdifferentiableAt_extChartAt (I := I) (x := x₀) (y := x₀) (mem_chart_source H x₀)
  show HasDerivAt ((fun z : M => (extChartAt I x₀) z) ∘ σ) (curveVelocity (I := I) σ 0) 0
  have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0 :=
    MDifferentiableAt.comp (I := 𝓘(ℝ)) (I' := I) (I'' := 𝓘(ℝ, E)) (x := (0:ℝ))
      (f := σ) (g := fun z : M => (extChartAt I x₀) z) he hσ
  have hdiff : DifferentiableAt ℝ ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0 :=
    (mdifferentiableAt_iff_differentiableAt).mp hcomp
  have hval : (fderiv ℝ ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0) 1 = curveVelocity (I := I) σ 0 := by
    have h1 : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ((fun z : M => (extChartAt I x₀) z) ∘ σ) 0
        = mfderiv 𝓘(ℝ) I σ 0 := by
      have hchain := mfderiv_comp (I := 𝓘(ℝ)) (I' := I) (I'' := 𝓘(ℝ, E)) (x := (0:ℝ))
        (f := σ) (g := fun z : M => (extChartAt I x₀) z) he hσ
      rw [hσ0] at hchain
      rw [hchain, mfderiv_extChartAt_self]
      exact ContinuousLinearMap.id_comp _
    rw [← mfderiv_eq_fderiv, h1]
    rfl
  rw [← hval]
  exact hdiff.hasFDerivAt.hasDerivAt

/-- **The first variation formula at a local maximum of the distance function (no curvature
hypothesis).**  Let `x ∈ M`, `v ∈ T_xM` a unit vector, `L > 0`, `y = GExp x (L • v)` with the ray of
`v` *minimising* at `L` (`d(x,y) = L`), **strictly inside the injectivity radius** (`∃ ρ, L < ρ` and
`InjAtLeast hmet x ρ`; equivalently: the ray is minimising strictly beyond `L`), and `L` **not a
conjugate time** for the ray.  Let `c` be a `C^∞` curve through `y = c t₀` at which `τ ↦ d(x, c τ)`
has a local maximum.  Then the velocity of `c` at `t₀` is **orthogonal** to the velocity of the
minimising ray at its end:

`⟪c'(t₀), (d/dt) (t ↦ GExp x (t • v)) |_{t=L}⟫ = 0`.

The strict-injectivity hypothesis is *not* redundant: at a non-conjugate cut point (e.g. the flat
torus, `L = 1/2`) the conclusion fails, and `d(x, ·)` is not differentiable there.

*Proof route (which is why no curvature bound appears in the statement).*  Put
`V' := ((d GExp_x)_{L v})⁻¹ V` where `V` is (the chart image of) the velocity of `c` at `t₀` — this
exists because `L` is not a conjugate time (`Submission.SingularConj.singular_imp_conjTime`), — and
`u_τ := L • v + τ • V'`.  By Gauss's lemma (`Submission.Gauss.gauss_lemma_fderiv`),
`⟪v, V'⟫ = ⟪w, V⟫` where `w = (d/dt)(t ↦ GExp x (t • v))|_L` is the ray velocity at `L`.  Choose
`ρ` with `L < ρ` and `InjAtLeast hmet x ρ` (the hypothesis `hinj`): for small `|τ|` one has
`‖u_τ‖ < ρ`, so `d(x, GExp x u_τ) = ‖u_τ‖ = L + τ⟪v,V'⟫ + O(τ²) = L + τ⟪V,w⟫ + O(τ²)` by
`Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast`.  The curves `τ ↦ GExp x u_τ` and
`τ ↦ c (t₀ + τ)` are *tangent* at `τ = 0` (same point `y`, same velocity `V`), so their distance is
`o(τ)`; hence `d(x, c(t₀+τ)) ≥ L + τ⟪V,w⟫ - o(τ)`.  The maximum gives `d(x, c(t₀+τ)) ≤ d(x,y) = L`
for `τ` of both signs, and dividing by `τ` in the two cases yields `⟪V,w⟫ = 0`. -/
theorem inner_eq_zero_of_isLocalMax_edist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x y : M} {v : TangentSpace I x} (hv : ‖v‖ = 1) {L : ℝ} (hL : 0 < L)
    (hy : Submission.GlobalExp.GExp (cov := cov) hmet x (L • v) = y)
    (hmin : Manifold.riemannianEDist I x y = ENNReal.ofReal L)
    (hinj : ∃ ρ : ℝ, L < ρ ∧ Submission.InjRadius.InjAtLeast hmet x ρ)
    (hnc : ¬ Submission.ConjRadius.IsConjugateTime cov
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (t • v)) L)
    {c : ℝ → M} {t₀ : ℝ} (hc : c t₀ = y) (hcsm : ContMDiff 𝓘(ℝ) I ∞ c)
    (hmax : ∀ᶠ τ in 𝓝 t₀, Manifold.riemannianEDist I x (c τ) ≤ Manifold.riemannianEDist I x (c t₀)) :
    inner ℝ (Submission.Geodesic.curveVelocity (I := I) c t₀)
      (Submission.Geodesic.curveVelocity (I := I)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (t • v)) L) = 0 := by
  obtain ⟨ρ, hLρ, hInj⟩ := hinj
  subst hy
  set pt : M := GExp (cov := cov) hmet x (L • v) with hptdef
  have hvne : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  have hLvnorm : ‖(L • v : TangentSpace I x)‖ = L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, hv, mul_one]
  have hLvne : (L • v : TangentSpace I x) ≠ 0 := by
    intro h
    have h1 : ‖(L • v : TangentSpace I x)‖ = 0 := by rw [h, norm_zero]
    rw [hLvnorm] at h1
    exact hL.ne' h1
  have hunit : unitOf (L • v) hLvne = v := by
    rw [unitOf, hLvnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hL), one_smul]
  set A : E →L[ℝ] E := mfderiv 𝓘(ℝ,E) I
      (fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u))
      (show E from (L • v)) with hAdef
  have hAinv : A.IsInvertible := by
    by_contra hcon
    rw [hAdef] at hcon
    have h := (Submission.SingularConj.singular_imp_conjTime (cov := cov) hmet htor) x hLvne hcon
    have hfun : (fun s : ℝ => GExp (cov := cov) hmet x (s • unitOf (L • v) hLvne))
        = (fun t : ℝ => GExp (cov := cov) hmet x (t • v)) := by
      funext s; rw [hunit]
    rw [hLvnorm, hfun] at h
    exact hnc h
  obtain ⟨Ae, hAe⟩ := hAinv
  set Ψ : E → E := fun u => (extChartAt I pt)
      (GExp (cov := cov) hmet x (show TangentSpace I x from u)) with hΨdef
  have hΨdiff : ContDiffAt ℝ 1 Ψ (L • v) := by
    have hf1 : ContMDiffAt 𝓘(ℝ,E) I 1
        (fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u)) (L • v) :=
      Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet x (L • v)
    have h2 := (contMDiffAt_iff_target.mp hf1).2
    have h3 : (⇑(extChartAt I pt)) ∘
        (fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u)) = Ψ := by
      rw [hΨdef]; rfl
    rw [h3] at h2
    exact h2.contDiffAt
  have hΨderiv : fderiv ℝ Ψ (show E from (L • v)) = (Ae : E →L[ℝ] E) := by
    have key : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) Ψ (show E from (L • v)) = (Ae : E →L[ℝ] E) := by
      have hchain := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := I) (I'' := 𝓘(ℝ,E)) (x := (show E from (L • v)))
        (f := fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u))
        (g := fun z : M => (extChartAt I pt) z)
        (mdifferentiableAt_extChartAt (I := I) (x := pt) (y := pt) (mem_chart_source H pt))
        ((Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet x (L • v)).mdifferentiableAt one_ne_zero)
      have h4 : (fun z : M => (extChartAt I pt) z) ∘
          (fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u)) = Ψ := by
        rw [hΨdef]; rfl
      rw [h4] at hchain
      rw [hchain, mfderiv_extChartAt_self, ContinuousLinearMap.id_comp]
      rw [hAe, hAdef]
    rw [← mfderiv_eq_fderiv]
    exact key
  have hstrict : HasStrictFDerivAt Ψ (Ae : E →L[ℝ] E) (show E from (L • v)) := by
    have h := hΨdiff.hasStrictFDerivAt (by norm_num : (1:ℕ∞ω) ≠ 0)
    rw [hΨderiv] at h
    exact h
  set ψ : E → E := hstrict.localInverse Ψ Ae (show E from (L • v)) with hψdef
  have hψ_image : ψ ((extChartAt I pt) pt) = show E from (L • v) :=
    hstrict.localInverse_apply_image
  have hψ_right : ∀ᶠ z in 𝓝 ((extChartAt I pt) pt), (extChartAt I pt) (GExp (cov := cov) hmet x (ψ z)) = z :=
    hstrict.eventually_right_inverse
  have hψ_deriv : HasFDerivAt ψ (Ae.symm : E →L[ℝ] E) ((extChartAt I pt) pt) :=
    hstrict.to_localInverse.hasFDerivAt
  have hψ_cont : ContinuousAt ψ ((extChartAt I pt) pt) := hψ_deriv.continuousAt
  have hfs : (show TangentSpace I x from (show E from (L • v))) = (L : ℝ) • v := rfl
  have hfsnorm : ‖(show TangentSpace I x from (show E from (L • v)))‖ = L := by
    rw [hfs, norm_smul, Real.norm_eq_abs, abs_of_pos hL, hv, mul_one]
  -- the linear functional of the problem: `lam X = ⟪v, (d exp_x)_{Lv}^{-1} X⟫`
  let lam : TangentSpace I pt → ℝ := fun X =>
    inner ℝ v (show TangentSpace I x from (Ae.symm (show E from X)))
  have hlam_def : ∀ X : TangentSpace I pt,
      lam X = inner ℝ v (show TangentSpace I x from (Ae.symm (show E from X))) := fun X => rfl
  have hlam_lin : ∀ (X Y : TangentSpace I pt) (a : ℝ), lam (X + a • Y) = lam X + a * lam Y := by
    intro X Y a
    rw [hlam_def, hlam_def, hlam_def]
    have h1 : (show E from (X + a • Y) : E) = (show E from X) + a • (show E from Y) := rfl
    rw [h1, map_add, map_smul]
    rw [show (show TangentSpace I x from (Ae.symm (show E from X) + a • Ae.symm (show E from Y)))
        = (show TangentSpace I x from (Ae.symm (show E from X)))
          + a • (show TangentSpace I x from (Ae.symm (show E from Y))) from rfl]
    rw [inner_add_right, inner_smul_right]
  -- ================= the master derivative statement =================
  have master : ∀ (σ : ℝ → M) (X : TangentSpace I pt), σ 0 = pt → ContinuousAt σ 0 →
      HasDerivAt (fun s : ℝ => (extChartAt I pt) (σ s)) (show E from X) 0 →
      HasDerivAt (fun s : ℝ => (Manifold.riemannianEDist I x (σ s)).toReal) (lam X) 0 := by
    intro σ X hσ0 hσcont hσchart
    have h1 : HasDerivAt (fun s : ℝ => ψ ((extChartAt I pt) (σ s))) (Ae.symm (show E from X)) 0 := by
      have h2 : HasFDerivAt ψ (Ae.symm : E →L[ℝ] E) ((extChartAt I pt) (σ 0)) := by
        rw [hσ0]
        exact hψ_deriv
      exact h2.comp_hasDerivAt 0 hσchart
    have hγ0 : ψ ((extChartAt I pt) (σ 0)) = show E from (L • v) := by
      rw [hσ0]
      exact hψ_image
    have h1f : HasDerivAt (fun s : ℝ => (show TangentSpace I x from ψ ((extChartAt I pt) (σ s))))
        (show TangentSpace I x from (Ae.symm (show E from X))) 0 := h1
    have hnef : (fun s : ℝ => (show TangentSpace I x from ψ ((extChartAt I pt) (σ s)))) 0 ≠ 0 := by
      show (show TangentSpace I x from ψ ((extChartAt I pt) (σ 0))) ≠ 0
      rw [hγ0]
      exact hLvne
    have h3 := hasDerivAt_norm_comp h1f hnef
    have hderiv_eq : (inner ℝ (show TangentSpace I x from ψ ((extChartAt I pt) (σ 0)))
          (show TangentSpace I x from (Ae.symm (show E from X)))
        / ‖(show TangentSpace I x from ψ ((extChartAt I pt) (σ 0)))‖) = lam X := by
      rw [hlam_def, hγ0, hfsnorm, hfs, inner_smul_left, starRingEnd_apply, star_trivial]
      field_simp
    have h3' : HasDerivAt (fun s : ℝ => ‖(show TangentSpace I x from ψ ((extChartAt I pt) (σ s)))‖) (lam X) 0 :=
      h3.congr_deriv hderiv_eq
    -- the eventual agreement with the distance function
    have hsrc_ev : ∀ᶠ s in 𝓝 (0:ℝ), σ s ∈ (extChartAt I pt).source := by
      refine hσcont.preimage_mem_nhds ?_
      rw [hσ0]
      exact extChartAt_source_mem_nhds (I := I) pt
    have heσ : ContinuousAt (fun s : ℝ => (extChartAt I pt) (σ s)) 0 := by
      have h1 : ContinuousAt (fun z : M => (extChartAt I pt) z) (σ 0) := by
        rw [hσ0]
        exact continuousAt_extChartAt (I := I) pt
      exact ContinuousAt.comp (f := σ) (g := fun z : M => (extChartAt I pt) z) h1 hσcont
    have htend_e : Tendsto (fun s : ℝ => (extChartAt I pt) (σ s)) (𝓝 (0:ℝ))
        (𝓝 ((extChartAt I pt) pt)) := by
      have h := heσ.tendsto
      rwa [hσ0] at h
    have hψ_right_ev : ∀ᶠ s in 𝓝 (0:ℝ),
        (extChartAt I pt) (GExp (cov := cov) hmet x (ψ ((extChartAt I pt) (σ s))))
          = (extChartAt I pt) (σ s) :=
      htend_e.eventually hψ_right
    have hψσ_cont : ContinuousAt (fun s : ℝ => ψ ((extChartAt I pt) (σ s))) 0 := by
      have h1 : ContinuousAt ψ ((extChartAt I pt) (σ 0)) := by
        rw [hσ0]
        exact hψ_cont
      exact ContinuousAt.comp (f := fun s : ℝ => (extChartAt I pt) (σ s))
        (g := ψ) h1 heσ
    have hGx_cont : ContinuousAt (fun s : ℝ => GExp (cov := cov) hmet x (ψ ((extChartAt I pt) (σ s)))) 0 := by
      have h1 : ContinuousAt (fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u))
          (ψ ((extChartAt I pt) (σ 0))) := by
        rw [hγ0]
        exact (Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet x (L • v)).continuousAt
      exact ContinuousAt.comp (f := fun s : ℝ => ψ ((extChartAt I pt) (σ s)))
        (g := fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u)) h1 hψσ_cont
    have hGx_src_ev : ∀ᶠ s in 𝓝 (0:ℝ), GExp (cov := cov) hmet x (ψ ((extChartAt I pt) (σ s))) ∈ (extChartAt I pt).source := by
      refine hGx_cont.preimage_mem_nhds ?_
      rw [hγ0]
      have h2 : GExp (cov := cov) hmet x (show TangentSpace I x from (show E from (L • v))) = pt := rfl
      rw [h2]
      exact extChartAt_source_mem_nhds (I := I) pt
    have hhit : ∀ᶠ s in 𝓝 (0:ℝ), GExp (cov := cov) hmet x (ψ ((extChartAt I pt) (σ s))) = σ s := by
      filter_upwards [hψ_right_ev, hsrc_ev, hGx_src_ev] with s h1 h2 h3
      exact (extChartAt I pt).injOn h3 h2 h1
    have hsmall : ∀ᶠ s in 𝓝 (0:ℝ), ‖(show TangentSpace I x from ψ ((extChartAt I pt) (σ s)))‖ < ρ := by
      have htend : Tendsto (fun s : ℝ => ψ ((extChartAt I pt) (σ s))) (𝓝 (0:ℝ)) (𝓝 (show E from (L • v))) := by
        have h := hψσ_cont.tendsto
        rwa [hγ0] at h
      have htend' : Tendsto (fun s : ℝ => (show TangentSpace I x from ψ ((extChartAt I pt) (σ s))))
          (𝓝 (0:ℝ)) (𝓝 (show TangentSpace I x from (show E from (L • v)))) := htend
      have h2 : Tendsto (fun s : ℝ => ‖(show TangentSpace I x from ψ ((extChartAt I pt) (σ s)))‖)
          (𝓝 (0:ℝ)) (𝓝 L) := by
        have h := (continuous_norm.tendsto (show TangentSpace I x from (show E from (L • v)))).comp htend'
        rwa [hfsnorm] at h
      exact h2.eventually_lt_const hLρ
    have heq : ∀ᶠ s in 𝓝 (0:ℝ),
        (Manifold.riemannianEDist I x (σ s)).toReal
          = ‖(show TangentSpace I x from ψ ((extChartAt I pt) (σ s)))‖ := by
      filter_upwards [hhit, hsmall] with s h1 h2
      have H' : Manifold.riemannianEDist I x (σ s)
          = Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (ψ ((extChartAt I pt) (σ s)))) := by
        rw [h1]
      have H : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (ψ ((extChartAt I pt) (σ s))))
          = ENNReal.ofReal ‖(show TangentSpace I x from ψ ((extChartAt I pt) (σ s)))‖ :=
        edist_GExp_eq_norm_of_injAtLeast (cov := cov) hmet htor (x := x) (r := ρ) hInj h2
      rw [H', H, ENNReal.toReal_ofReal (norm_nonneg _)]
    exact h3'.congr_of_eventuallyEq heq
  -- ================= (a) the curve c =================
  have hVchart : HasDerivAt (fun s : ℝ => (extChartAt I pt) (c (t₀ + s)))
      (show E from (show TangentSpace I pt from curveVelocity (I := I) c t₀)) 0 := by
    have hσ0 : (fun s : ℝ => c (t₀ + s)) 0 = pt := by
      show c (t₀ + 0) = pt
      rw [add_zero]
      exact hc
    have hσmd : MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ => c (t₀ + s)) 0 := by
      have hshift : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => t₀ + s) 0 := by
        rw [mdifferentiableAt_iff_differentiableAt]
        exact (differentiableAt_const t₀).add differentiableAt_id
      exact MDifferentiableAt.comp (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (I'' := I) (x := (0:ℝ))
        (f := fun s : ℝ => t₀ + s) (g := c)
        ((hcsm (t₀ + 0)).mdifferentiableAt (by norm_num : (∞ : ℕ∞ω) ≠ 0)) hshift
    have hvel : curveVelocity (I := I) (fun s : ℝ => c (t₀ + s)) 0 = curveVelocity (I := I) c t₀ := by
      have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := c) (c := 1) (d := t₀) (t := 0)
        (by simpa using (hcsm t₀).mdifferentiableAt (by norm_num : (∞ : ℕ∞ω) ≠ 0) :
          MDifferentiableAt 𝓘(ℝ) I c (1 * 0 + t₀))
      rw [one_mul, zero_add, one_smul] at h
      have hev : (fun s : ℝ => c (1 * s + t₀)) =ᶠ[𝓝 (0:ℝ)] (fun s : ℝ => c (t₀ + s)) := by
        filter_upwards with s
        rw [one_mul, add_comm]
      rw [Submission.RayJacobi.curveVelocity_congr (I := I) hev] at h
      exact h
    have h := hasDerivAt_extChartAt_comp (I := I) (x₀ := pt) hσ0 hσmd
    rw [hvel] at h
    exact h
  have hcderiv : HasDerivAt (fun s : ℝ => (Manifold.riemannianEDist I x (c (t₀ + s))).toReal)
      (lam (show TangentSpace I pt from curveVelocity (I := I) c t₀)) 0 := by
    refine master (fun s : ℝ => c (t₀ + s)) (show TangentSpace I pt from curveVelocity (I := I) c t₀) ?_ ?_ ?_
    · show c (t₀ + 0) = pt
      rw [add_zero]
      exact hc
    · have hshift : ContinuousAt (fun s : ℝ => t₀ + s) 0 := continuousAt_const.add continuousAt_id
      exact ContinuousAt.comp (f := fun s : ℝ => t₀ + s) (g := c)
        ((hcsm (t₀ + 0)).continuousAt) hshift
    · exact hVchart
  have hlocmax : IsLocalMax (fun s : ℝ => (Manifold.riemannianEDist I x (c (t₀ + s))).toReal) 0 := by
    have h1 : ∀ᶠ s in 𝓝 (0:ℝ),
        Manifold.riemannianEDist I x (c (t₀ + s)) ≤ Manifold.riemannianEDist I x (c t₀) := by
      have ht : Tendsto (fun s : ℝ => t₀ + s) (𝓝 (0:ℝ)) (𝓝 t₀) := by
        have h1 : Tendsto (fun _ : ℝ => t₀) (𝓝 (0:ℝ)) (𝓝 t₀) := tendsto_const_nhds
        have h2 : Tendsto (fun s : ℝ => s) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := tendsto_id
        simpa using h1.add h2
      exact ht.eventually hmax
    refine h1.mono ?_
    intro s hs
    have hfin : Manifold.riemannianEDist I x (c (t₀ + 0)) ≠ ⊤ := by
      rw [add_zero, hc, hmin]
      exact ENNReal.ofReal_ne_top
    exact ENNReal.toReal_mono hfin (by simpa using hs)
  have hlamV : lam (show TangentSpace I pt from curveVelocity (I := I) c t₀) = 0 :=
    IsLocalMax.hasDerivAt_eq_zero hlocmax hcderiv
  -- ================= (b) the ray velocity =================
  set ray : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet x (t • v) with hraydef
  have hAev : (show E from curveVelocity (I := I) ray L) = Ae (show E from v) := by
    have h := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
      (f := fun u : E => GExp (cov := cov) hmet x (show TangentSpace I x from u))
      (σ := fun s : ℝ => s • v) (σ' := fun _ : ℝ => v)
      (γ := ray) (t := L)
      (by simpa using (hasDerivAt_id L).smul_const v)
      ((Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet x (L • v)).mdifferentiableAt one_ne_zero)
      (Filter.Eventually.of_forall (fun r => rfl))
    have hAfun : (Ae : E → E) = (A : E → E) :=
      congrArg (fun f : E →L[ℝ] E => (f : E → E)) hAe
    rw [h, hAfun, hAdef]
    rfl
  have hlamw : lam (show TangentSpace I pt from curveVelocity (I := I) ray L) = 1 := by
    rw [hlam_def]
    rw [show (show E from (show TangentSpace I pt from curveVelocity (I := I) ray L))
        = Ae (show E from v) from hAev]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rw [show (show TangentSpace I x from (show E from v)) = v from rfl]
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hwnorm : ‖(show TangentSpace I pt from curveVelocity (I := I) ray L)‖ = 1 := by
    have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet x hvne hL.ne'
    simpa [hraydef, hv] using h
  -- ================= (c) the Lipschitz bound for lam =================
  have hbound : ∀ X : TangentSpace I pt, |lam X| ≤ ‖X‖ := by
    intro X
    rcases eq_or_ne X 0 with hX | hX
    · subst hX
      have h0 : lam 0 = 0 := by
        rw [hlam_def]
        rw [show (show E from (0 : TangentSpace I pt)) = (0 : E) from rfl, map_zero]
        rw [show (show TangentSpace I x from (0 : E)) = (0 : TangentSpace I x) from rfl, inner_zero_right]
      rw [h0, norm_zero, abs_zero]
    · have hσ0 : (fun s : ℝ => GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X))) 0 = pt := by
        show GExp (cov := cov) hmet pt (show TangentSpace I pt from ((0:ℝ) • X)) = pt
        rw [zero_smul, GExp_zero]
      have hσmd : MDifferentiableAt 𝓘(ℝ) I
          (fun s : ℝ => GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X))) 0 :=
        ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet pt hX) 0).mdifferentiableAt
          (by norm_num : (∞ : ℕ∞ω) ≠ 0)
      have hσcont : ContinuousAt
          (fun s : ℝ => GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X))) 0 :=
        hσmd.continuousAt
      have hvel : curveVelocity (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X))) 0 = X :=
        Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet pt hX
      have hchart : HasDerivAt (fun s : ℝ => (extChartAt I pt)
          (GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X)))) (show E from X) 0 := by
        have h := hasDerivAt_extChartAt_comp (I := I) (x₀ := pt) hσ0 hσmd
        rw [hvel] at h
        exact h
      have hder := master (fun s : ℝ => GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X)))
        X hσ0 hσcont hchart
      have hbd : ∀ s : ℝ,
          |(Manifold.riemannianEDist I x (GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X)))).toReal
            - (Manifold.riemannianEDist I x pt).toReal| ≤ |s| * ‖X‖ := by
        intro s
        set Y : M := GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X)) with hYdef
        have hray : Manifold.riemannianEDist I pt Y ≤ ENNReal.ofReal (|s| * ‖X‖) := by
          have h := Submission.CutWitness.edist_GExp_le_norm (cov := cov) (p := pt) hmet
            (show TangentSpace I pt from (s • X))
          rw [norm_smul, Real.norm_eq_abs] at h
          simpa [hYdef] using h
        have hfin_pt : Manifold.riemannianEDist I x pt ≠ ⊤ := by rw [hmin]; exact ENNReal.ofReal_ne_top
        have hfin_ray : Manifold.riemannianEDist I pt Y ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top hray
        have htri1 : Manifold.riemannianEDist I x Y
            ≤ Manifold.riemannianEDist I x pt + Manifold.riemannianEDist I pt Y :=
          Manifold.riemannianEDist_triangle (I := I) (x := x) (y := pt) (z := Y)
        have hfinY : Manifold.riemannianEDist I x Y ≠ ⊤ :=
          ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfin_pt, hfin_ray⟩) htri1
        have h1 : (Manifold.riemannianEDist I x Y).toReal ≤ L + |s| * ‖X‖ := by
          have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin_pt, hfin_ray⟩) htri1
          rw [ENNReal.toReal_add hfin_pt hfin_ray, hmin, ENNReal.toReal_ofReal hL.le] at h2
          have h3 : (Manifold.riemannianEDist I pt Y).toReal ≤ |s| * ‖X‖ :=
            (ENNReal.toReal_mono ENNReal.ofReal_ne_top hray).trans_eq
              (ENNReal.toReal_ofReal (by positivity))
          linarith
        have h2 : L - |s| * ‖X‖ ≤ (Manifold.riemannianEDist I x Y).toReal := by
          have htri2 : Manifold.riemannianEDist I x pt
              ≤ Manifold.riemannianEDist I x Y + Manifold.riemannianEDist I Y pt :=
            Manifold.riemannianEDist_triangle (I := I) (x := x) (y := Y) (z := pt)
          have hfinYpt : Manifold.riemannianEDist I Y pt ≠ ⊤ := by
            rw [Manifold.riemannianEDist_comm]; exact hfin_ray
          have h3 : (Manifold.riemannianEDist I Y pt).toReal ≤ |s| * ‖X‖ := by
            have h4 : Manifold.riemannianEDist I Y pt ≤ ENNReal.ofReal (|s| * ‖X‖) := by
              rw [Manifold.riemannianEDist_comm]; exact hray
            exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h4).trans_eq
              (ENNReal.toReal_ofReal (by positivity))
          have h5 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinY, hfinYpt⟩) htri2
          rw [ENNReal.toReal_add hfinY hfinYpt, hmin, ENNReal.toReal_ofReal hL.le] at h5
          linarith
        rw [hYdef, hmin, ENNReal.toReal_ofReal hL.le, abs_le]
        exact ⟨by linarith, by linarith⟩
      have htend : Tendsto (fun s : ℝ =>
          |slope (fun s : ℝ => (Manifold.riemannianEDist I x
            (GExp (cov := cov) hmet pt (show TangentSpace I pt from (s • X)))).toReal) 0 s|)
          (𝓝[≠] (0:ℝ)) (𝓝 |lam X|) := hder.tendsto_slope.abs
      refine le_of_tendsto_of_tendsto htend tendsto_const_nhds ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hss : 0 < |s| := abs_pos.mpr hs
      have h0 : (Manifold.riemannianEDist I x
            (GExp (cov := cov) hmet pt (show TangentSpace I pt from ((0:ℝ) • X)))).toReal
          = (Manifold.riemannianEDist I x pt).toReal := by rw [zero_smul, GExp_zero]
      rw [slope_def_field, sub_zero, h0, abs_div, div_le_iff₀ hss, mul_comm]
      exact hbd s
  -- ================= (d) the quadratic argument =================
  set V : TangentSpace I pt := show TangentSpace I pt from curveVelocity (I := I) c t₀ with hVdef
  set w : TangentSpace I pt := show TangentSpace I pt from curveVelocity (I := I) ray L with hwdef
  have hquad : ∀ t : ℝ, t ^ 2 ≤ ‖V + t • w‖ ^ 2 := by
    intro t
    have h1 := hbound (V + t • w)
    have h2 : lam (V + t • w) = t := by
      rw [hlam_lin V w t, hlamV, hlamw]
      ring
    rw [h2] at h1
    refine (sq_le_sq).mpr ?_
    rwa [abs_of_nonneg (norm_nonneg (V + t • w))]
  have hexp : ∀ t : ℝ, ‖V + t • w‖ ^ 2 = ‖V‖ ^ 2 + 2 * t * inner ℝ V w + t ^ 2 := by
    intro t
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, inner_smul_right, mul_pow, sq_abs, hwnorm]
    ring
  have hmain : inner ℝ V w = 0 := by
    by_contra hne
    have h := hquad (-(‖V‖ ^ 2 + 1) / (2 * inner ℝ V w))
    rw [hexp] at h
    have h2 : 2 * (-(‖V‖ ^ 2 + 1) / (2 * inner ℝ V w)) * inner ℝ V w = -(‖V‖ ^ 2 + 1) := by
      field_simp
    rw [h2] at h
    linarith [sq_nonneg ‖V‖]
  show inner ℝ (curveVelocity (I := I) c t₀) (curveVelocity (I := I) ray L) = 0
  rw [hc]
  exact hmain

end

end Work.EvenBound.FarthestPoint
