import Mathlib
import Submission.Work.Diff.C.JacobiLogDeriv
import Submission.Work.Diff.C.jetFunction

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic Submission.JacobiCoords Submission.Jacobi Submission.Rauch Submission.ChartCurv
open Submission.ChartIndep Submission.JacobiVec Commons.Geometry.Manifold.Tangent
open Submission.ChartConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
    (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]

theorem frameVector_injective {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) :
    Function.Injective (frameVector (I := I) x₀ p) := by
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa [← extChartAt_source] using hp
  intro v w hvw
  have hv := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
    (e := trivializationAt E (TangentSpace I) x₀) hb v
  have hw := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
    (e := trivializationAt E (TangentSpace I) x₀) hb w
  have hvw' : (trivializationAt E (TangentSpace I) x₀).symmL ℝ p v
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ p w := hvw
  rw [← hv, ← hw, hvw']

theorem differentiableAt_coordChangeL_comp {x₀ x₁ : M} {γ : ℝ → M} {s : ℝ}
    (hs₀ : γ s ∈ (chartAt H x₀).source) (hs₁ : γ s ∈ (chartAt H x₁).source)
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ s) :
    DifferentiableAt ℝ (fun σ : ℝ => (Trivialization.coordChangeL ℝ
      (trivializationAt E (TangentSpace I) x₀)
      (trivializationAt E (TangentSpace I) x₁) (γ σ) : E →L[ℝ] E)) s := by
  have hb₀ : γ s ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa [← extChartAt_source] using hs₀
  have hb₁ : γ s ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by
    simpa [← extChartAt_source] using hs₁
  have hcc : ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] E)) ∞
      (fun q : M => (Trivialization.coordChangeL ℝ
        (trivializationAt E (TangentSpace I) x₀)
        (trivializationAt E (TangentSpace I) x₁) q : E →L[ℝ] E)) (γ s) :=
    (contMDiffOn_coordChangeL (𝕜 := ℝ)
      (trivializationAt E (TangentSpace I) x₀)
      (trivializationAt E (TangentSpace I) x₁)).contMDiffAt
      (((Trivialization.open_baseSet _).inter (Trivialization.open_baseSet _)).mem_nhds
        ⟨hb₀, hb₁⟩)
  have hmd : MDifferentiableAt 𝓘(ℝ) (modelWithCornersSelf ℝ (E →L[ℝ] E))
      (fun σ : ℝ => (Trivialization.coordChangeL ℝ
        (trivializationAt E (TangentSpace I) x₀)
        (trivializationAt E (TangentSpace I) x₁) (γ σ) : E →L[ℝ] E)) s :=
    MDifferentiableAt.comp (f := γ) (g := fun q : M => (Trivialization.coordChangeL ℝ
        (trivializationAt E (TangentSpace I) x₀)
        (trivializationAt E (TangentSpace I) x₁) q : E →L[ℝ] E)) s
      (hcc.mdifferentiableAt (by simp)) hγmd
  exact mdifferentiableAt_iff_differentiableAt.mp hmd

theorem deriv_clm_apply'' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → (E →L[ℝ] E)} {y : ℝ → E} {s : ℝ}
    (hA : DifferentiableAt ℝ A s) (hy : DifferentiableAt ℝ y s) :
    deriv (fun σ => (A σ) (y σ)) s = (deriv A s) (y s) + (A s) (deriv y s) := by
  rw [show deriv (fun σ => (A σ) (y σ)) s = fderiv ℝ (fun σ => (A σ) (y σ)) s 1 from rfl]
  rw [fderiv_clm_apply hA hy]
  simp only [add_apply]
  rw [show (A s ∘SL fderiv ℝ y s) 1 = A s (deriv y s) from rfl]
  rw [show ((fderiv ℝ A s).flip (y s)) 1 = (deriv A s) (y s) from by
    rw [ContinuousLinearMap.flip_apply]; rfl]
  exact add_comm _ _

theorem chartCoords_eq_coordChangeL {x₀ x₁ : M} {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace I (γ t)} {s : ℝ}
    (hs₀ : γ s ∈ (chartAt H x₀).source) (hs₁ : γ s ∈ (chartAt H x₁).source) :
    chartCoords (I := I) x₁ γ V s
      = Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) x₀)
          (trivializationAt E (TangentSpace I) x₁) (γ s)
          (chartCoords (I := I) x₀ γ V s) := by
  have hb₀ : γ s ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa [← extChartAt_source] using hs₀
  have hb₁ : γ s ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by
    simpa [← extChartAt_source] using hs₁
  rw [chartCoords]
  show (trivializationAt E (TangentSpace I) x₁).continuousLinearMapAt ℝ (γ s) (V s) = _
  rw [← frameVector_chartCoords (I := I) (x₀ := x₀) (γ := γ) (J := V) hs₀]
  rw [frameVector, Trivialization.symmL_apply _ hb₀,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (e := trivializationAt E (TangentSpace I) x₁) hb₁]
  rw [← Trivialization.mk_coordChangeL (R := ℝ)
      (e := trivializationAt E (TangentSpace I) x₀)
      (e' := trivializationAt E (TangentSpace I) x₁) ⟨hb₀, hb₁⟩
      (chartCoords (I := I) x₀ γ V s)]


theorem exists_smooth_section_jet {x₀ : M} {γ : ℝ → M} {s : ℝ}
    (hsrc : γ s ∈ (chartAt H x₀).source)
    (hne : curveVelocity (I := I) γ s ≠ 0) (a b : E) :
    ∃ W : Π q : M, TangentSpace I q,
      CMDiff ∞ (T% W) ∧
      coordFun x₀ W (γ s) = a ∧
      mvfderiv I (coordFun x₀ W) (γ s) (curveVelocity (I := I) γ s) = b := by
  obtain ⟨lam, hlsm, hl0, hl1⟩ := jetFunction (I := I) (γ s) (curveVelocity (I := I) γ s) hne
  obtain ⟨χ, -, hχsupp⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) (γ s)).mem_iff.mp
    ((chartAt H x₀).open_source.mem_nhds hsrc)
  have hUopen : IsOpen (chartAt H x₀).source := (chartAt H x₀).open_source
  have hσa : CMDiff[(chartAt H x₀).source] ∞ (T% (fun q : M => frameVector (I := I) x₀ q a)) :=
    fun q hq => (contMDiffAt_frameSection (I := I) x₀ a hq).contMDiffWithinAt
  have hσb : CMDiff[(chartAt H x₀).source] ∞ (T% (fun q : M => frameVector (I := I) x₀ q b)) :=
    fun q hq => (contMDiffAt_frameSection (I := I) x₀ b hq).contMDiffWithinAt
  have hlcd : CMDiff[(chartAt H x₀).source] ∞ (fun q : M => lam q) := hlsm.contMDiffOn
  have hτ : CMDiff[(chartAt H x₀).source] ∞
      (T% (fun q : M => frameVector (I := I) x₀ q a + lam q • frameVector (I := I) x₀ q b)) :=
    hσa.add_section (hlcd.smul_section hσb)
  refine ⟨fun q : M => (χ : M → ℝ) q • (frameVector (I := I) x₀ q a + lam q • frameVector (I := I) x₀ q b),
    ?_, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (I := I)
      (u := (chartAt H x₀).source)
      (s := fun q : M => frameVector (I := I) x₀ q a + lam q • frameVector (I := I) x₀ q b)
      (ψ := fun q : M => (χ : M → ℝ) q)
      (χ.contMDiff.contMDiffOn) hUopen hχsupp hτ
  · have hb : γ s ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      simpa [← extChartAt_source] using hsrc
    have key : coordFun x₀ (fun q : M => (χ : M → ℝ) q •
        (frameVector (I := I) x₀ q a + lam q • frameVector (I := I) x₀ q b)) (γ s)
        = (χ : M → ℝ) (γ s) • (a + lam (γ s) • b) := by
      simp only [coordFun, frameVector]
      rw [map_smul, map_add, map_smul,
        Trivialization.continuousLinearMapAt_symmL (R := ℝ)
          (e := trivializationAt E (TangentSpace I) x₀) hb a,
        Trivialization.continuousLinearMapAt_symmL (R := ℝ)
          (e := trivializationAt E (TangentSpace I) x₀) hb b]
    rw [key, SmoothBumpFunction.eq_one, hl0]
    simp
  · have hsrc' : ∀ᶠ q in 𝓝 (γ s), q ∈ (chartAt H x₀).source :=
      (chartAt H x₀).open_source.mem_nhds hsrc
    have hev : coordFun x₀ (fun q : M => (χ : M → ℝ) q •
        (frameVector (I := I) x₀ q a + lam q • frameVector (I := I) x₀ q b))
        =ᶠ[𝓝 (γ s)] fun q => a + lam q • b := by
      filter_upwards [χ.eventuallyEq_one, hsrc'] with q hq1 hq2
      have hbq : q ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
        simpa [← extChartAt_source] using hq2
      have key : coordFun x₀ (fun q : M => (χ : M → ℝ) q •
          (frameVector (I := I) x₀ q a + lam q • frameVector (I := I) x₀ q b)) q
          = (χ : M → ℝ) q • (a + lam q • b) := by
        simp only [coordFun, frameVector]
        rw [map_smul, map_add, map_smul,
          Trivialization.continuousLinearMapAt_symmL (R := ℝ)
            (e := trivializationAt E (TangentSpace I) x₀) hbq a,
          Trivialization.continuousLinearMapAt_symmL (R := ℝ)
            (e := trivializationAt E (TangentSpace I) x₀) hbq b]
      rw [key, hq1]
      simp
    rw [mvfderiv_congr_of_eventuallyEq (I := I) hev]
    have hcst_a : MDifferentiableAt I (modelWithCornersSelf ℝ E) (fun _ : M => a) (γ s) :=
      mdifferentiableAt_const
    have hcst_b : MDifferentiableAt I (modelWithCornersSelf ℝ E) (fun _ : M => b) (γ s) :=
      mdifferentiableAt_const
    have hlam : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun q : M => lam q) (γ s) :=
      hlsm.mdifferentiableAt (by simp)
    have hsmul : MDifferentiableAt I (modelWithCornersSelf ℝ E) (fun q : M => lam q • b) (γ s) := by
      have := hlam.smul hcst_b
      exact this
    have h1 : mvfderiv I (fun q : M => a + lam q • b) (γ s) (curveVelocity (I := I) γ s)
        = mvfderiv I (fun _ : M => a) (γ s) (curveVelocity (I := I) γ s)
          + mvfderiv I (fun q : M => lam q • b) (γ s) (curveVelocity (I := I) γ s) := by
      rw [show (fun q : M => a + lam q • b) = (fun _ : M => a) + (fun q : M => lam q • b) from rfl]
      rw [mvfderiv_add hcst_a hsmul]
      rfl
    have h2 : mvfderiv I (fun _ : M => a) (γ s) (curveVelocity (I := I) γ s) = 0 := by
      rw [mvfderiv_const]
      rfl
    have h3 : mvfderiv I (fun q : M => lam q • b) (γ s) (curveVelocity (I := I) γ s) = b := by
      rw [show (fun q : M => lam q • b) = (fun q : M => lam q) • (fun _ : M => b) from rfl]
      rw [mvfderiv_smul hlam hcst_b]
      simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
        mvfderiv_const, hl0, zero_smul, zero_add, hl1, one_smul]
    rw [h1, h2, h3, zero_add]


theorem frameVector_chartCovDeriv_eq_of_coords
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (σ : ℝ) → TangentSpace I (γ σ)} {x₀ x₁ : M}
    {u w u₁ w₁ y z : ℝ → E} {s : ℝ}
    (hs₀ : γ s ∈ (chartAt H x₀).source) (hs₁ : γ s ∈ (chartAt H x₁).source)
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ s)
    (hsrcEv₀ : ∀ᶠ σ in 𝓝 s, γ σ ∈ (chartAt H x₀).source)
    (hsrcEv₁ : ∀ᶠ σ in 𝓝 s, γ σ ∈ (chartAt H x₁).source)
    (huTgt : ∀ᶠ σ in 𝓝 s, u σ ∈ (extChartAt I x₀).target)
    (huTgt₁ : ∀ᶠ σ in 𝓝 s, u₁ σ ∈ (extChartAt I x₁).target)
    (hγ₀ : γ =ᶠ[𝓝 s] fun σ => (extChartAt I x₀).symm (u σ))
    (hγ₁ : γ =ᶠ[𝓝 s] fun σ => (extChartAt I x₁).symm (u₁ σ))
    (hu : ∀ᶠ σ in 𝓝 s, HasDerivAt u (w σ) σ)
    (hu₁ : ∀ᶠ σ in 𝓝 s, HasDerivAt u₁ (w₁ σ) σ)
    (hy : ∀ᶠ σ in 𝓝 s, frameVector (I := I) x₀ (γ σ) (y σ) = V σ)
    (hz : ∀ᶠ σ in 𝓝 s, frameVector (I := I) x₁ (γ σ) (z σ) = V σ)
    (hzd : ∀ᶠ σ in 𝓝 s, DifferentiableAt ℝ z σ)
    (hne : curveVelocity (I := I) γ s ≠ 0) :
    DifferentiableAt ℝ y s ∧
      frameVector (I := I) x₀ (γ s) (chartCovDeriv cov x₀ u w y s)
        = frameVector (I := I) x₁ (γ s) (chartCovDeriv cov x₁ u₁ w₁ z s) := by
  have hyV : ∀ᶠ σ in 𝓝 s, chartCoords (I := I) x₀ γ V σ = y σ := by
    filter_upwards [hy, hsrcEv₀] with σ h1 h2
    exact frameVector_injective (I := I) h2 (by rw [frameVector_chartCoords (I := I) h2, h1])
  have hzV : ∀ᶠ σ in 𝓝 s, chartCoords (I := I) x₁ γ V σ = z σ := by
    filter_upwards [hz, hsrcEv₁] with σ h1 h2
    exact frameVector_injective (I := I) h2 (by rw [frameVector_chartCoords (I := I) h2, h1])
  set A : ℝ → (E →L[ℝ] E) := fun σ => (Trivialization.coordChangeL ℝ
      (trivializationAt E (TangentSpace I) x₀)
      (trivializationAt E (TangentSpace I) x₁) (γ σ) : E →L[ℝ] E) with hAdef
  set B : ℝ → (E →L[ℝ] E) := fun σ => (Trivialization.coordChangeL ℝ
      (trivializationAt E (TangentSpace I) x₁)
      (trivializationAt E (TangentSpace I) x₀) (γ σ) : E →L[ℝ] E) with hBdef
  have hAd : DifferentiableAt ℝ A s :=
    differentiableAt_coordChangeL_comp (I := I) hs₀ hs₁ hγmd
  have hBd : DifferentiableAt ℝ B s :=
    differentiableAt_coordChangeL_comp (I := I) hs₁ hs₀ hγmd
  have hzA : z =ᶠ[𝓝 s] fun σ => A σ (y σ) := by
    filter_upwards [hyV, hzV, hsrcEv₀, hsrcEv₁] with σ h1 h2 h3 h4
    rw [← h2, ← h1]
    exact chartCoords_eq_coordChangeL (I := I) h3 h4
  have hyB : y =ᶠ[𝓝 s] fun σ => B σ (z σ) := by
    filter_upwards [hyV, hzV, hsrcEv₀, hsrcEv₁] with σ h1 h2 h3 h4
    rw [← h1, ← h2]
    exact chartCoords_eq_coordChangeL (I := I) (x₀ := x₁) (x₁ := x₀) h4 h3
  have hyd : DifferentiableAt ℝ y s := by
    have h1 : DifferentiableAt ℝ (fun σ => B σ (z σ)) s := hBd.clm_apply hzd.self_of_nhds
    exact h1.congr_of_eventuallyEq hyB
  -- the realizing smooth section
  obtain ⟨W, hWsm, hWa, hWb⟩ := exists_smooth_section_jet (I := I) hs₀ hne (y s) (deriv y s)
  set yW : ℝ → E := chartCoords (I := I) x₀ γ (fun σ => W (γ σ)) with hyWdef
  set zW : ℝ → E := chartCoords (I := I) x₁ γ (fun σ => W (γ σ)) with hzWdef
  have hyWcomp : (fun σ : ℝ => coordFun x₀ W (γ σ)) = yW := rfl
  have hyWs : yW s = y s := by
    rw [hyWdef]
    exact hWa
  have hyWmd : MDifferentiableAt I (modelWithCornersSelf ℝ E) (coordFun x₀ W) (γ s) :=
    (contMDiffAt_coordFun (x₀ := x₀) hWsm hs₀).mdifferentiableAt (by simp)
  have hyWdiff : DifferentiableAt ℝ yW s := by
    have h2 := MDifferentiableAt.comp (f := γ) (g := coordFun x₀ W) s hyWmd hγmd
    exact mdifferentiableAt_iff_differentiableAt.mp h2
  have hyWd : deriv yW s = deriv y s := by
    have h : deriv (coordFun x₀ W ∘ γ) s = deriv y s := by
      rw [← mvfderiv_comp_curve (I := I) (g := coordFun x₀ W) (γ := γ) (t := s) hyWmd hγmd]
      exact hWb
    exact h
  have hzWeq : zW =ᶠ[𝓝 s] fun σ => A σ (yW σ) := by
    filter_upwards [hsrcEv₀, hsrcEv₁] with σ h3 h4
    rw [hzWdef, hyWdef]
    exact chartCoords_eq_coordChangeL (I := I) h3 h4
  have hzWs : zW s = A s (y s) := by
    have h1 : zW s = A s (yW s) := hzWeq.self_of_nhds
    rw [h1, hyWs]
  have hzs : z s = A s (y s) := hzA.self_of_nhds
  have hzWdiff : DifferentiableAt ℝ (fun σ => A σ (yW σ)) s := hAd.clm_apply hyWdiff
  have hzWd : deriv zW s = deriv z s := by
    have e1 : deriv zW s = deriv (fun σ => A σ (yW σ)) s := hzWeq.deriv_eq
    have e2 : deriv z s = deriv (fun σ => A σ (y σ)) s := hzA.deriv_eq
    rw [e1, e2, deriv_clm_apply'' hAd hyWdiff, deriv_clm_apply'' hAd hyd, hyWs, hyWd]
  have hcov0 : frameVector (I := I) x₀ (γ s) (chartCovDeriv cov x₀ u w y s)
      = cov W (γ s) (curveVelocity (I := I) γ s) := by
    have h1 : chartCovDeriv cov x₀ u w y s = chartCovDeriv cov x₀ u w yW s := by
      rw [chartCovDeriv_apply (I := I) (cov := cov) huTgt.self_of_nhds,
        chartCovDeriv_apply (I := I) (cov := cov) (y := yW) huTgt.self_of_nhds,
        hyWs, hyWd]
    rw [h1]
    exact frameVector_chartCovDeriv_eq_cov (cov := cov) hs₀ hsrcEv₀ huTgt hWsm hγ₀ hu
      (by filter_upwards [hsrcEv₀] with σ hσ; exact frameVector_chartCoords (I := I) hσ) hγmd
  have hcov1 : frameVector (I := I) x₁ (γ s) (chartCovDeriv cov x₁ u₁ w₁ z s)
      = cov W (γ s) (curveVelocity (I := I) γ s) := by
    have h1 : chartCovDeriv cov x₁ u₁ w₁ z s = chartCovDeriv cov x₁ u₁ w₁ zW s := by
      rw [chartCovDeriv_apply (I := I) (cov := cov) (x₀ := x₁) huTgt₁.self_of_nhds,
        chartCovDeriv_apply (I := I) (cov := cov) (x₀ := x₁) (y := zW) huTgt₁.self_of_nhds,
        hzWs, hzs, hzWd]
    rw [h1]
    exact frameVector_chartCovDeriv_eq_cov (cov := cov) hs₁ hsrcEv₁ huTgt₁ hWsm hγ₁ hu₁
      (by filter_upwards [hsrcEv₁] with σ hσ; exact frameVector_chartCoords (I := I) hσ) hγmd
  exact ⟨hyd, hcov0.trans hcov1.symm⟩



open Submission.ChartConnection

/-- `chartCovDeriv` only depends on the germ of the field. -/
lemma chartCovDeriv_congr_field {x₀ : M} {u w y₁ y₂ : ℝ → E} {s : ℝ}
    (h : y₁ =ᶠ[𝓝 s] y₂) :
    chartCovDeriv cov x₀ u w y₁ s = chartCovDeriv cov x₀ u w y₂ s := by
  simp only [chartCovDeriv, h.deriv_eq, h.eq_of_nhds]

/-- **The transfer lemma, uniformly on an open set.** -/
theorem frameVector_chartCovDeriv_eq_on
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (σ : ℝ) → TangentSpace I (γ σ)} {x₀ x₁ : M}
    {u w u₁ w₁ y z : ℝ → E} {U : Set ℝ}
    (hU : IsOpen U)
    (hγmd : ∀ σ ∈ U, MDifferentiableAt 𝓘(ℝ) I γ σ)
    (hsrc₀ : ∀ σ ∈ U, γ σ ∈ (chartAt H x₀).source)
    (hsrc₁ : ∀ σ ∈ U, γ σ ∈ (chartAt H x₁).source)
    (huTgt : ∀ σ ∈ U, u σ ∈ (extChartAt I x₀).target)
    (huTgt₁ : ∀ σ ∈ U, u₁ σ ∈ (extChartAt I x₁).target)
    (hγ₀ : ∀ σ ∈ U, γ σ = (extChartAt I x₀).symm (u σ))
    (hγ₁ : ∀ σ ∈ U, γ σ = (extChartAt I x₁).symm (u₁ σ))
    (hu : ∀ σ ∈ U, HasDerivAt u (w σ) σ)
    (hu₁ : ∀ σ ∈ U, HasDerivAt u₁ (w₁ σ) σ)
    (hy : ∀ σ ∈ U, frameVector (I := I) x₀ (γ σ) (y σ) = V σ)
    (hz : ∀ σ ∈ U, frameVector (I := I) x₁ (γ σ) (z σ) = V σ)
    (hzd : ∀ σ ∈ U, DifferentiableAt ℝ z σ)
    (hne : ∀ σ ∈ U, curveVelocity (I := I) γ σ ≠ 0) :
    ∀ σ ∈ U, DifferentiableAt ℝ y σ ∧
      frameVector (I := I) x₀ (γ σ) (chartCovDeriv cov x₀ u w y σ)
        = frameVector (I := I) x₁ (γ σ) (chartCovDeriv cov x₁ u₁ w₁ z σ) := by
  intro σ hσ
  have hUσ : U ∈ 𝓝 σ := hU.mem_nhds hσ
  exact frameVector_chartCovDeriv_eq_of_coords (cov := cov) htor
    (hsrc₀ σ hσ) (hsrc₁ σ hσ) (hγmd σ hσ)
    (Filter.eventually_of_mem hUσ hsrc₀)
    (Filter.eventually_of_mem hUσ hsrc₁)
    (Filter.eventually_of_mem hUσ huTgt)
    (Filter.eventually_of_mem hUσ huTgt₁)
    (Filter.eventually_of_mem hUσ hγ₀)
    (Filter.eventually_of_mem hUσ hγ₁)
    (Filter.eventually_of_mem hUσ hu)
    (Filter.eventually_of_mem hUσ hu₁)
    (Filter.eventually_of_mem hUσ hy)
    (Filter.eventually_of_mem hUσ hz)
    (Filter.eventually_of_mem hUσ hzd)
    (hne σ hσ)


open Submission.ChartConnection

open scoped Manifold ContDiff Bundle Topology in
/-- **Jacobi fields along a fixed curve are closed under addition.**  The Jacobi equation is linear in
the field, so the sum of two Jacobi fields along the same curve is again a Jacobi field.  (The
library has `Submission.JacobiVec.chartCurv_add_fst`/`chartCurv_smul_fst` and the docstring of
`Submission.JacobiVec` announces this lemma, but it is not actually present.)

HINT for the proof: take the `IsJacobiAt` data of `J` at `t` (`Submission.RauchGlobal.exists_local_data`,
chart `x₀`, coordinates `y`), and the data of `K` at `t` (chart `x₁`, coordinates `z`).  The sum has
coordinates `chartCoords x₀ γ J + chartCoords x₀ γ K` in the chart `x₀` (use
`Submission.JacobiCoords.frameVector_chartCoords` and `frameVector_add`); both coordinate functions
are `C^∞` near `t` (`Submission.JacobiGlobal.contDiffOn_chartCoords_of_isJacobiAt` /
`contDiffOn_chartCoords_of_chartCoords`), the equation for `J`'s coordinates is the given data, and
the equation for `K`'s coordinates in the chart `x₀` is obtained from its own data with
`Submission.ChartIndep.chartJacobiEquation_of_charts` (which needs globally smooth sections
`𝓚 ≈ K` and `𝒵 ≈ ∇_{γ'}K`; get them with
`Submission.JacobiGlobal.exists_section_of_smoothAlongAt` from `smoothAlongAt_of_isJacobiAt`
(Jacobi fields are smooth along `γ`) and from `Work.Diff.C.smoothAlongAt_covAlong`).  Adding the two
equations needs `Submission.JacobiVec.chartCurv_add_fst` plus the linearity of `chartCovDeriv` (which
is `deriv` plus the bilinear `gammaOp`/`chrB`; see `Submission.Jacobi.chartCovDeriv_add`) and
`deriv_add`; then assemble the `IsJacobiAt` data for the sum. -/
theorem isJacobiAt_add
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
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {J K : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hJ : Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hK : Submission.RauchGlobal.IsJacobiAt cov γ K t) :
    Submission.RauchGlobal.IsJacobiAt cov γ (fun s : ℝ ↦ J s + K s) t := by

  classical
  obtain ⟨x₀, u, w, yJ, ρJ, hρJ, huTgtJ, huJ, hγJ, hyJ, hunitJ, hyJd, hyJz, hjacJ⟩ :=
    Submission.RauchGlobal.exists_local_data (cov := cov) hJ
  obtain ⟨x₁, u₁, w₁, yK, ρK, hρK, huTgtK, huK, hγK, hyK, hunitK, hyKd, hyKz, hjacK⟩ :=
    Submission.RauchGlobal.exists_local_data (cov := cov) hK
  set ρ : ℝ := min ρJ ρK with hρdef
  have hρ : 0 < ρ := lt_min hρJ hρK
  set U : Set ℝ := Ioo (t - ρ) (t + ρ) with hUdef
  have hUopen : IsOpen U := isOpen_Ioo
  have htU : t ∈ U := ⟨by linarith, by linarith⟩
  have hminJ : ρ ≤ ρJ := min_le_left _ _
  have hminK : ρ ≤ ρK := min_le_right _ _
  have hmemJ : ∀ σ ∈ U, σ ∈ Ioo (t - ρJ) (t + ρJ) := by
    intro σ hσ
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hmemK : ∀ σ ∈ U, σ ∈ Ioo (t - ρK) (t + ρK) := by
    intro σ hσ
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  -- wrappers for J's data
  have huTgtU : ∀ σ ∈ U, u σ ∈ (extChartAt I x₀).target := fun σ hσ => huTgtJ σ (hmemJ σ hσ)
  have huU : ∀ σ ∈ U, HasDerivAt u (w σ) σ := fun σ hσ => huJ σ (hmemJ σ hσ)
  have hγU : ∀ σ ∈ U, γ σ = (extChartAt I x₀).symm (u σ) := fun σ hσ => hγJ σ (hmemJ σ hσ)
  have hunitU : ∀ σ ∈ U, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u σ)) (w σ) (w σ) = 1 :=
    fun σ hσ => hunitJ σ (hmemJ σ hσ)
  have hyJU : ∀ σ ∈ U, frameVector (I := I) x₀ (γ σ) (yJ σ) = J σ := fun σ hσ => hyJ σ (hmemJ σ hσ)
  have hyJdU : ∀ σ ∈ U, HasDerivAt yJ (deriv yJ σ) σ := fun σ hσ => hyJd σ (hmemJ σ hσ)
  have hyJzU : ∀ σ ∈ U, HasDerivAt (chartCovDeriv cov x₀ u w yJ)
      (deriv (chartCovDeriv cov x₀ u w yJ) σ) σ := fun σ hσ => hyJz σ (hmemJ σ hσ)
  have hjacJU : ∀ σ ∈ U, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w yJ) σ
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u σ)) (yJ σ) (w σ) = 0 :=
    fun σ hσ => hjacJ σ (hmemJ σ hσ)
  have huTgtKU : ∀ σ ∈ U, u₁ σ ∈ (extChartAt I x₁).target := fun σ hσ => huTgtK σ (hmemK σ hσ)
  have huKU : ∀ σ ∈ U, HasDerivAt u₁ (w₁ σ) σ := fun σ hσ => huK σ (hmemK σ hσ)
  have hγKU : ∀ σ ∈ U, γ σ = (extChartAt I x₁).symm (u₁ σ) := fun σ hσ => hγK σ (hmemK σ hσ)
  have hyKU : ∀ σ ∈ U, frameVector (I := I) x₁ (γ σ) (yK σ) = K σ := fun σ hσ => hyK σ (hmemK σ hσ)
  have hyKzU : ∀ σ ∈ U, HasDerivAt (chartCovDeriv cov x₁ u₁ w₁ yK)
      (deriv (chartCovDeriv cov x₁ u₁ w₁ yK) σ) σ := fun σ hσ => hyKz σ (hmemK σ hσ)
  have hjacKU : ∀ σ ∈ U, chartCovDeriv cov x₁ u₁ w₁ (chartCovDeriv cov x₁ u₁ w₁ yK) σ
      + chartCurv cov x₁ ((extChartAt I x₁).symm (u₁ σ)) (yK σ) (w₁ σ) = 0 :=
    fun σ hσ => hjacK σ (hmemK σ hσ)
  -- source memberships
  have hsrc₀ : ∀ σ ∈ U, γ σ ∈ (chartAt H x₀).source := by
    intro σ hσ
    rw [hγU σ hσ]
    exact mem_source_chartCurve (I := I) (huTgtU σ hσ)
  have hsrc₁ : ∀ σ ∈ U, γ σ ∈ (chartAt H x₁).source := by
    intro σ hσ
    rw [hγKU σ hσ]
    exact mem_source_chartCurve (I := I) (huTgtKU σ hσ)
  -- differentiability of the curve on U
  have hγmdU : ∀ σ ∈ U, MDifferentiableAt 𝓘(ℝ) I γ σ := by
    intro σ hσ
    have htgt : u σ ∈ (extChartAt I x₀).target := huTgtU σ hσ
    have hu_md : MDifferentiableAt 𝓘(ℝ) (modelWithCornersSelf ℝ E) u σ :=
      mdifferentiableAt_iff_differentiableAt.mpr (huU σ hσ).differentiableAt
    have hsym : MDifferentiableAt (modelWithCornersSelf ℝ E) I
        (fun ξ : E => (extChartAt I x₀).symm ξ) (u σ) :=
      ((contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) x₀).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds htgt)).mdifferentiableAt (by simp)
    have hcomp : MDifferentiableAt 𝓘(ℝ) I
        (fun τ : ℝ => (extChartAt I x₀).symm (u τ)) σ :=
      MDifferentiableAt.comp (f := u) (g := fun ξ : E => (extChartAt I x₀).symm ξ) σ hsym hu_md
    have heq : γ =ᶠ[𝓝 σ] fun τ : ℝ => (extChartAt I x₀).symm (u τ) :=
      Filter.eventually_of_mem (hUopen.mem_nhds hσ) hγU
    exact heq.mdifferentiableAt_iff.mpr hcomp
  -- the velocity is nonzero on U
  have hneU : ∀ σ ∈ U, curveVelocity (I := I) γ σ ≠ 0 := by
    intro σ hσ
    have hw : w σ ≠ 0 := by
      intro h0
      have := hunitU σ hσ
      rw [h0] at this
      simp at this
    have h1 : frameVector (I := I) x₀ (γ σ) (w σ) ≠ 0 := by
      intro hz
      refine hw (frameVector_injective (I := I) (hsrc₀ σ hσ) ?_)
      rw [hz]
      exact (map_zero _).symm
    rw [← frameVector_chartVel_eq_curveVelocity (hsrc₀ σ hσ)
      (Filter.eventually_of_mem (hUopen.mem_nhds hσ) huTgtU)
      (Filter.eventually_of_mem (hUopen.mem_nhds hσ) hγU)
      (Filter.eventually_of_mem (hUopen.mem_nhds hσ) huU) (hγmdU σ hσ)]
    exact h1
  -- the field K in chart x₁ and its x₀-coordinates
  have hzK : ∀ σ ∈ U, frameVector (I := I) x₁ (γ σ) (chartCoords (I := I) x₁ γ K σ) = K σ :=
    fun σ hσ => frameVector_chartCoords (I := I) (hsrc₁ σ hσ)
  have hzeqU : ∀ σ ∈ U, chartCoords (I := I) x₁ γ K σ = yK σ := by
    intro σ hσ
    exact frameVector_injective (I := I) (hsrc₁ σ hσ)
      (by rw [frameVector_chartCoords (I := I) (hsrc₁ σ hσ), hyKU σ hσ])
  have hzdU : ∀ σ ∈ U, DifferentiableAt ℝ (chartCoords (I := I) x₁ γ K) σ := by
    intro σ hσ
    exact (hyKd σ (hmemK σ hσ)).differentiableAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hUopen.mem_nhds hσ) hzeqU)
  -- transfer for K
  have htransK : ∀ σ ∈ U, DifferentiableAt ℝ (chartCoords (I := I) x₀ γ K) σ ∧
      frameVector (I := I) x₀ (γ σ) (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K) σ)
        = frameVector (I := I) x₁ (γ σ)
            (chartCovDeriv cov x₁ u₁ w₁ (chartCoords (I := I) x₁ γ K) σ) :=
    frameVector_chartCovDeriv_eq_on (cov := cov) htor hUopen hγmdU hsrc₀ hsrc₁ huTgtU huTgtKU
      hγU hγKU huU huKU
      (fun σ hσ => frameVector_chartCoords (I := I) (hsrc₀ σ hσ))
      hzK hzdU hneU
  -- transfer for ∇K
  have hzd2U : ∀ σ ∈ U, DifferentiableAt ℝ (chartCovDeriv cov x₁ u₁ w₁ (chartCoords (I := I) x₁ γ K)) σ := by
    intro σ hσ
    exact (hyKzU σ hσ).differentiableAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hUopen.mem_nhds hσ) fun τ hτ => by
        exact (chartCovDeriv_congr_field (cov := cov)
          (Filter.eventually_of_mem (hUopen.mem_nhds hτ) hzeqU)))
  have htransT : ∀ σ ∈ U,
      DifferentiableAt ℝ (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ ∧
      frameVector (I := I) x₀ (γ σ)
          (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ)
        = frameVector (I := I) x₁ (γ σ)
            (chartCovDeriv cov x₁ u₁ w₁ (chartCovDeriv cov x₁ u₁ w₁ (chartCoords (I := I) x₁ γ K)) σ) :=
    frameVector_chartCovDeriv_eq_on (cov := cov) htor hUopen hγmdU hsrc₀ hsrc₁ huTgtU huTgtKU
      hγU hγKU huU huKU
      (fun σ hσ => rfl)
      (fun σ hσ => (htransK σ hσ).2.symm)
      hzd2U hneU
  -- the ordinary-differentiability of the x₀-coordinate function of K
  have hzKd : ∀ σ ∈ U, DifferentiableAt ℝ (chartCoords (I := I) x₀ γ K) σ :=
    fun σ hσ => (htransK σ hσ).1
  -- the inner chartCovDeriv linearity, at any σ ∈ U
  have hFeqOn : ∀ σ ∈ U, (fun s => chartCovDeriv cov x₀ u w
        (fun τ => yJ τ + chartCoords (I := I) x₀ γ K τ) s)
      =ᶠ[𝓝 σ] fun s => chartCovDeriv cov x₀ u w yJ s
        + chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K) s := by
    intro σ hσ
    filter_upwards [hUopen.mem_nhds hσ] with τ hτ
    exact chartCovDeriv_add (I := I) (cov := cov) (huTgtU τ hτ) (hyJdU τ hτ).differentiableAt
      (hzKd τ hτ)
  have hjacJU' : ∀ σ ∈ U, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w yJ) σ
      + chartCurv cov x₀ (γ σ) (yJ σ) (w σ) = 0 := by
    intro σ hσ
    have h := hjacJU σ hσ
    rwa [← hγU σ hσ] at h
  -- the K-part of the Jacobi equation in chart x₀ vanishes
  have hKpartOn : ∀ σ ∈ U,
      chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ
        + chartCurv cov x₀ (γ σ) (chartCoords (I := I) x₀ γ K σ) (w σ) = 0 := by
    intro σ hσ
    -- the x₁-form of the same expression vanishes
    have hzeqσ : (fun τ => chartCoords (I := I) x₁ γ K τ) =ᶠ[𝓝 σ] fun τ => yK τ :=
      Filter.eventually_of_mem (hUopen.mem_nhds hσ) hzeqU
    have hKjac : chartCovDeriv cov x₁ u₁ w₁
          (chartCovDeriv cov x₁ u₁ w₁ (chartCoords (I := I) x₁ γ K)) σ
        + chartCurv cov x₁ (γ σ) (chartCoords (I := I) x₁ γ K σ) (w₁ σ) = 0 := by
      have e1 : chartCovDeriv cov x₁ u₁ w₁
            (chartCovDeriv cov x₁ u₁ w₁ (chartCoords (I := I) x₁ γ K)) σ
          = chartCovDeriv cov x₁ u₁ w₁ (chartCovDeriv cov x₁ u₁ w₁ yK) σ :=
        chartCovDeriv_congr_field (cov := cov)
          (Filter.eventually_of_mem (hUopen.mem_nhds hσ) fun τ hτ =>
            chartCovDeriv_congr_field (cov := cov)
              (Filter.eventually_of_mem (hUopen.mem_nhds hτ) hzeqU))
      have e2 : chartCurv cov x₁ (γ σ) (chartCoords (I := I) x₁ γ K σ) (w₁ σ)
          = chartCurv cov x₁ ((extChartAt I x₁).symm (u₁ σ)) (yK σ) (w₁ σ) := by
        rw [← hγKU σ hσ, hzeqU σ hσ]
      rw [e1, e2]
      exact hjacKU σ hσ
    -- transfer the expression to chart x₁
    refine frameVector_injective (I := I) (hsrc₀ σ hσ) ?_
    rw [show frameVector (I := I) x₀ (γ σ) (0 : E) = 0 from map_zero _]
    rw [frameVector_add, (htransT σ hσ).2]
    rw [frameVector_chartCurv_eq_of_charts (cov := cov) htor (hsrc₀ σ hσ) (hsrc₁ σ hσ)
      (by rw [frameVector_chartCoords (I := I) (hsrc₀ σ hσ),
        frameVector_chartCoords (I := I) (hsrc₁ σ hσ)])
      (by rw [frameVector_chartVel_eq_curveVelocity (hsrc₀ σ hσ)
            (Filter.eventually_of_mem (hUopen.mem_nhds hσ) huTgtU)
            (Filter.eventually_of_mem (hUopen.mem_nhds hσ) hγU)
            (Filter.eventually_of_mem (hUopen.mem_nhds hσ) huU) (hγmdU σ hσ),
          frameVector_chartVel_eq_curveVelocity (hsrc₁ σ hσ)
            (Filter.eventually_of_mem (hUopen.mem_nhds hσ) huTgtKU)
            (Filter.eventually_of_mem (hUopen.mem_nhds hσ) hγKU)
            (Filter.eventually_of_mem (hUopen.mem_nhds hσ) huKU) (hγmdU σ hσ)])]
    rw [← frameVector_add, hKjac, show frameVector (I := I) x₁ (γ σ) (0 : E) = 0 from map_zero _]
  refine ⟨x₀, u, w, fun s => yJ s + chartCoords (I := I) x₀ γ K s,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Filter.eventually_of_mem (hUopen.mem_nhds htU) huTgtU
  · exact Filter.eventually_of_mem (hUopen.mem_nhds htU) huU
  · exact Filter.eventually_of_mem (hUopen.mem_nhds htU) hγU
  · refine Filter.eventually_of_mem (hUopen.mem_nhds htU) (fun σ hσ => ?_)
    rw [frameVector_add, hyJU σ hσ, frameVector_chartCoords (I := I) (hsrc₀ σ hσ)]
  · exact Filter.eventually_of_mem (hUopen.mem_nhds htU) hunitU
  · refine Filter.eventually_of_mem (hUopen.mem_nhds htU) (fun σ hσ => ?_)
    exact ((hyJdU σ hσ).differentiableAt.add (hzKd σ hσ)).hasDerivAt
  · refine Filter.eventually_of_mem (hUopen.mem_nhds htU) (fun σ hσ => ?_)
    have hFJ : DifferentiableAt ℝ (chartCovDeriv cov x₀ u w yJ) σ := (hyJzU σ hσ).differentiableAt
    have hFK : DifferentiableAt ℝ (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ :=
      (htransT σ hσ).1
    exact ((hFJ.add hFK).congr_of_eventuallyEq (hFeqOn σ hσ)).hasDerivAt
  · refine Filter.eventually_of_mem (hUopen.mem_nhds htU) (fun σ hσ => ?_)
    have hFJ : DifferentiableAt ℝ (chartCovDeriv cov x₀ u w yJ) σ := (hyJzU σ hσ).differentiableAt
    have hFK : DifferentiableAt ℝ (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ :=
      (htransT σ hσ).1
    have hdecomp : chartCovDeriv cov x₀ u w
          (chartCovDeriv cov x₀ u w (fun τ => yJ τ + chartCoords (I := I) x₀ γ K τ)) σ
        = chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w yJ) σ
          + chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ := by
      rw [chartCovDeriv_congr_field (cov := cov) (hFeqOn σ hσ),
        chartCovDeriv_add (I := I) (cov := cov) (huTgtU σ hσ) hFJ hFK]
    have hdecomp2 : chartCurv cov x₀ (γ σ) ((fun τ => yJ τ + chartCoords (I := I) x₀ γ K τ) σ) (w σ)
        = chartCurv cov x₀ (γ σ) (yJ σ) (w σ)
          + chartCurv cov x₀ (γ σ) (chartCoords (I := I) x₀ γ K σ) (w σ) :=
      chartCurv_add_fst (I := I) (cov := cov) x₀ (γ σ) (hsrc₀ σ hσ) (yJ σ)
        (chartCoords (I := I) x₀ γ K σ) (w σ)
    rw [← hγU σ hσ, hdecomp, hdecomp2]
    have hgroup : (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w yJ) σ
          + chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ)
        + (chartCurv cov x₀ (γ σ) (yJ σ) (w σ)
          + chartCurv cov x₀ (γ σ) (chartCoords (I := I) x₀ γ K σ) (w σ))
        = (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w yJ) σ
            + chartCurv cov x₀ (γ σ) (yJ σ) (w σ))
          + (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (chartCoords (I := I) x₀ γ K)) σ
            + chartCurv cov x₀ (γ σ) (chartCoords (I := I) x₀ γ K σ) (w σ)) := by abel
    rw [hgroup, hjacJU' σ hσ, hKpartOn σ hσ, add_zero]

end Work.Diff.C
