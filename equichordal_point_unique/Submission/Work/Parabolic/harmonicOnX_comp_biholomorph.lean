import Mathlib
import Submission.Work.Parabolic.Deps

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Parabolic

/-! ### Two rewrite lemmas for the identity model with corners on `ℂ` -/

private lemma extChartAt_self_coe_eq {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) : ⇑(extChartAt (modelWithCornersSelf ℂ ℂ) x) = ⇑(chartAt ℂ x) := by
  rw [extChartAt_coe]; funext z; simp

private lemma extChartAt_self_coe_symm_eq {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) : ⇑(extChartAt (modelWithCornersSelf ℂ ℂ) x).symm = ⇑(chartAt ℂ x).symm := by
  rw [extChartAt_coe_symm]; funext z; simp

/-- **Chart representations of `C^∞` maps between Riemann surfaces are analytic.**

For the model `modelWithCornersSelf ℂ ℂ` the scalar field is `ℂ`, so a manifold-smooth (`∞`, in
the sense of the plain notation `X ≃ₘ⟮mℂ, mℂ⟯ Y`) map has `ℂ`-Fréchet smooth chart
representations; and a `ℂ`-Fréchet smooth function on an open subset of `ℂ` is analytic.  Hence
the chart representation `z ↦ (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z))` of `Φ` is analytic at
`(chartAt ℂ x) x`. -/
theorem analyticAt_chart_representation_infty {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {Φ : X → Y} (hΦ : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ Φ)
    (x : X) :
    AnalyticAt ℂ (fun z => (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z)))
      ((chartAt ℂ x) x) := by
  have h := hΦ x
  rw [contMDiffAt_iff] at h
  obtain ⟨-, h2⟩ := h
  rw [show (range (modelWithCornersSelf ℂ ℂ)) = (univ : Set ℂ) from
        ModelWithCorners.range_eq_univ _] at h2
  rw [show (⇑(extChartAt (modelWithCornersSelf ℂ ℂ) (Φ x)) : Y → ℂ)
        = ⇑(chartAt ℂ (Φ x)) from extChartAt_self_coe_eq _,
      show (⇑(extChartAt (modelWithCornersSelf ℂ ℂ) x).symm : ℂ → X)
        = ⇑(chartAt ℂ x).symm from extChartAt_self_coe_symm_eq _] at h2
  rw [contDiffWithinAt_univ] at h2
  -- `h2 : ContDiffAt ℂ ∞ g z₀`; it is `C^1` there, hence ℂ-differentiable near `z₀`, hence
  -- analytic at `z₀` — a `ℂ`-Fréchet differentiable function is holomorphic.
  obtain ⟨u, hu, hcu⟩ :=
    h2.contDiffOn (m := (1 : ℕ∞ω)) (by simp) (by intro hh; exact absurd hh (by simp))
  exact (hcu.differentiableOn (by simp)).analyticAt hu

/-- **Harmonicity transports along a biholomorphism, in the smoothness level used by the
library.**  Here `((⊤ : ℕ∞) : WithTop ℕ∞)` is Mathlib's `∞` (the level of the plain notation
`X ≃ₘ⟮mℂ, mℂ⟯ Y`), which is *not* the analytic level `ω`; but the model is `mℂ = modelWithCornersSelf ℂ ℂ`,
whose scalar field is ℂ, so `ContMDiff mℂ mℂ ∞ Φ` forces the chart representations of `Φ` to be
ℂ-differentiable (order 1 ≤ ∞), hence analytic, i.e. `Φ` is a biholomorphism.  (A smooth non-holomorphic
map such as `z ↦ z + (Im z)^3` is not `mℂ`-smooth, since `ContDiff ℂ ∞` is ℂ-Fréchet smoothness.)

Suggested route: `ContMDiffAt` with `range mℂ = univ` gives `ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) g` for
the chart representation `g`; `ContDiff.differentiable_one` then `Differentiable.analyticAt` give
`AnalyticAt ℂ g`, and `Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic` finishes. -/
theorem harmonicOnX_comp_biholomorph {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X Y
      ((⊤ : ℕ∞) : WithTop ℕ∞)) {u : Y → ℝ} {s : Set Y} (hu : Submission.HarmonicOnX u s) :
    Submission.HarmonicOnX (fun x => u (Φ x)) (Φ ⁻¹' s) := by
  intro x hx
  change InnerProductSpace.HarmonicAt ((fun x => u (Φ x)) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  -- the chart representation of `Φ` is analytic at the chart image of `x`
  have hF : AnalyticAt ℂ (fun z => (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z)))
      ((chartAt ℂ x) x) :=
    analyticAt_chart_representation_infty (Φ := ⇑Φ) Φ.contMDiff x
  -- the chart image of `x` is taken to the chart image of `Φ x` by that representation
  have hval : (fun z => (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z))) ((chartAt ℂ x) x)
      = (chartAt ℂ (Φ x)) (Φ x) := by
    simp only
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  -- harmonicity of `u` at `Φ x`, read in the chart at `Φ x`, at the correct point
  have hu' : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ (Φ x)).symm)
      ((fun z => (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z))) ((chartAt ℂ x) x)) := by
    rw [hval]
    exact hu (Φ x) hx
  have hcomp := Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
    (f := fun z => (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z)))
    (u := u ∘ (chartAt ℂ (Φ x)).symm) (x := (chartAt ℂ x) x) hF hu'
  -- the two functions agree near `(chartAt ℂ x) x`: the chart at `Φ x` inverts on its source
  have hcont : ContinuousAt (fun z : ℂ => Φ ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) :=
    Φ.continuous.continuousAt.comp
      ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  have hvs : ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      Φ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (Φ x)).source := by
    have hmem : (chartAt ℂ (Φ x)).source ∈ 𝓝 (Φ ((chartAt ℂ x).symm ((chartAt ℂ x) x))) := by
      rw [show (chartAt ℂ x).symm ((chartAt ℂ x) x) = x from
        (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact (chartAt ℂ (Φ x)).open_source.mem_nhds (mem_chart_source ℂ (Φ x))
    exact hcont.preimage_mem_nhds hmem
  have heq : (fun z => u ((chartAt ℂ (Φ x)).symm ((chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z)))))
      =ᶠ[𝓝 ((chartAt ℂ x) x)] (fun z => u (Φ ((chartAt ℂ x).symm z))) := by
    filter_upwards [hvs] with z hz
    rw [(chartAt ℂ (Φ x)).left_inv hz]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mp hcomp

end Work.Parabolic
