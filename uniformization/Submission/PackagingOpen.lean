import ChallengeDeps
import Submission.Packaging
import Submission.Holomorphic
import Submission.Helpers

/-!
# Packaging a bijective holomorphic map onto an open subset of `ℂ` as a complex diffeomorphism

This is the analogue of `Submission.Packaging` for the target being an *open subset* `U` of `ℂ`
(equipped with the subtype complex-manifold structure).  It is what converts the hyperbolic
endgame ("a proper holomorphic map `X → 𝔻` with a single simple zero is bijective") into the
second disjunct of the uniformization theorem, via
`Submission.Helpers.uniformization_of_unitDisc_openSubset`.

The main results are

* `Submission.nonempty_diffeomorph_open_of_bijective` : a bijective holomorphic `Φ : X → ℂ` whose
  image is exactly the open set `U` and whose chart derivative never vanishes induces an element of
  `X ≃ₘ⟮mℂ, mℂ⟯ U`;

* `Submission.nonempty_diffeomorph_disc_of_bijective` : the case `U = 𝔻`;

* `Submission.uniformization_of_bijective_to_disc` : the second disjunct of the conclusion.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Charts on an open subset of `ℂ` -/

/-- The chart of an open subset `U` of `ℂ` at a point is the inclusion. -/
theorem opens_chartAt_eq (U : TopologicalSpace.Opens ℂ) (w : U) :
    chartAt ℂ w = (OpenPartialHomeomorph.refl ℂ).subtypeRestr (s := U) ⟨w⟩ := by
  rw [TopologicalSpace.Opens.chartAt_eq (H := ℂ) (x := w)]
  rfl

/-- The chart of an open subset of `ℂ` is the coercion. -/
theorem opens_chartAt_apply (U : TopologicalSpace.Opens ℂ) (w u : U) :
    (chartAt ℂ w) u = (u : ℂ) := by
  rw [opens_chartAt_eq U w, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The target of the chart of an open subset of `ℂ` is the subset itself. -/
theorem opens_chartAt_target (U : TopologicalSpace.Opens ℂ) (w : U) :
    (chartAt ℂ w).target = (U : Set ℂ) := by
  rw [opens_chartAt_eq U w, OpenPartialHomeomorph.subtypeRestr_def,
    OpenPartialHomeomorph.trans_target]
  simp [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

/-- The inverse of the chart of an open subset of `ℂ` has coercion the identity. -/
theorem opens_chartAt_symm_apply_cast (U : TopologicalSpace.Opens ℂ) {w : U} {u : ℂ}
    (hu : u ∈ (U : Set ℂ)) : (((chartAt ℂ w).symm u : U) : ℂ) = u := by
  rw [opens_chartAt_eq U w]
  have hu' : u ∈ ((OpenPartialHomeomorph.refl ℂ).subtypeRestr (s := U) ⟨w⟩).target := by
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target]
    simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hu
  have h := (OpenPartialHomeomorph.refl ℂ).subtypeRestr_symm_eqOn (U := U) ⟨w⟩ hu'
  exact h.symm

/-! ## `ContMDiffAt` for a map out of an open subset -/

/-- **A map from an open subset of `ℂ` into a complex manifold is `ℂ`-smooth at a point as soon as
it is continuous there and its chart representation is analytic.** -/
theorem contMDiffAt_of_analytic_chart_subtype {U : TopologicalSpace.Opens ℂ} {f : U → X} {w : U}
    (hcont : ContinuousAt f w)
    (h : ContDiffAt ℂ ∞ ((chartAt ℂ (f w)) ∘ f ∘ (chartAt ℂ w).symm) ((chartAt ℂ w) w)) :
    ContMDiffAt mℂ mℂ ∞ f w := by
  rw [contMDiffAt_iff]
  refine ⟨hcont, ?_⟩
  have hcoe : ⇑(extChartAt mℂ (f w)) = ⇑(chartAt ℂ (f w)) := by
    simp [extChartAt_coe, modelWithCornersSelf_coe]
  have hcoesymm : ⇑(extChartAt mℂ w).symm = ⇑(chartAt ℂ w).symm := by
    simp [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
  have hpt : (extChartAt mℂ w) w = (chartAt ℂ w) w := by
    simp [extChartAt_coe, modelWithCornersSelf_coe]
  have hFeq : ⇑(extChartAt mℂ (f w)) ∘ f ∘ ⇑(extChartAt mℂ w).symm
      = (chartAt ℂ (f w)) ∘ f ∘ (chartAt ℂ w).symm := by
    funext u
    simp only [Function.comp_apply]
    rw [hcoe, hcoesymm]
  rw [hFeq, hpt, ModelWithCorners.Boundaryless.range_eq_univ]
  exact h.contDiffWithinAt

/-! ## The packaging -/

/-- **A bijective holomorphic map onto an open subset of `ℂ`, with non-vanishing chart derivative,
is a complex diffeomorphism onto that subset.** -/
theorem nonempty_diffeomorph_open_of_bijective {U : TopologicalSpace.Opens ℂ} {Φ : X → ℂ}
    (hmaps : ∀ x, Φ x ∈ (U : Set ℂ))
    (hbij : Function.Bijective fun x => (⟨Φ x, hmaps x⟩ : U))
    (hΦ : HolomorphicOnX Φ univ)
    (hderiv : ∀ x, deriv (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ U) := by
  set ψ : X → U := fun x => ⟨Φ x, hmaps x⟩ with hψdef
  have hΦψ : ∀ x, Φ x = ((ψ x : U) : ℂ) := fun x => rfl
  have hbijψ : Function.Bijective ψ := hbij
  let e : X ≃ U := Equiv.ofBijective ψ hbijψ
  have he : ⇑e = ψ := Equiv.coe_ofBijective ψ hbijψ
  have heΦ : ∀ x, Φ x = ((e x : U) : ℂ) := fun x => by rw [he]
  -- the forward direction
  have hcontΦ : Continuous Φ := hΦ.continuous
  have hana : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    fun x => hΦ x (mem_univ x)
  have hfwd : ContMDiff mℂ mℂ ∞ e := by
    rw [← ContMDiff.subtypeVal_comp_iff (U := U) (f := e)]
    have hfun : (Subtype.val : U → ℂ) ∘ ⇑e = Φ := by
      funext x
      exact (heΦ x).symm
    rw [hfun]
    exact contMDiff_of_analyticAt_charts hcontΦ hana
  -- the inverse direction
  have hinv : ContMDiff mℂ mℂ ∞ e.symm := by
    intro w
    set x : X := e.symm w with hx
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
    set φ : ℂ → ℂ := Φ ∘ c.symm with hφdef
    set z : ℂ := c x with hz
    have hφ : AnalyticAt ℂ φ z := by rw [hφdef, hz, hc]; exact hana x
    have hd : deriv φ z ≠ 0 := by rw [hφdef, hz, hc]; exact hderiv x
    let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 (deriv φ z) hd)
    have hfd : HasStrictFDerivAt φ i.toContinuousLinearMap z := hφ.hasStrictDerivAt
    let e₂ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph φ
    have he₂ : (e₂ : ℂ → ℂ) = φ := rfl
    have hzs : z ∈ e₂.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfd
    have hzt : φ z ∈ e₂.target := by rw [← he₂]; exact e₂.map_source hzs
    have hzsy : (e₂.symm : ℂ → ℂ) (φ z) = z := by rw [← he₂]; exact e₂.left_inv hzs
    have hzmem : z ∈ c.target := c.map_source (mem_chart_source ℂ x)
    have hr_an : AnalyticAt ℂ (e₂.symm : ℂ → ℂ) (φ z) := by
      refine OpenPartialHomeomorph.analyticAt_symm (f := e₂) (a := φ z) (i := i) hzt ?_ ?_
      · rw [hzsy, he₂]; exact hφ
      · rw [hzsy, he₂]; exact hfd.hasFDerivAt.fderiv
    have hφz : φ z = (w : ℂ) := by
      rw [hφdef, hz, hc, Function.comp_apply, c.left_inv (mem_chart_source ℂ x)]
      rw [heΦ x, e.apply_symm_apply]
    have hright : ∀ᶠ u in 𝓝 (φ z), Φ (c.symm ((e₂.symm : ℂ → ℂ) u)) = u := by
      filter_upwards [e₂.open_target.mem_nhds hzt] with u hu
      have h1 : e₂ (e₂.symm u) = u := e₂.right_inv hu
      have h2 : Φ (c.symm ((e₂.symm : ℂ → ℂ) u)) = e₂ ((e₂.symm : ℂ → ℂ) u) := by
        rw [he₂, hφdef]
        rfl
      rw [h2, h1]
    -- `e.symm` in terms of the local inverse
    have hsymm : ∀ᶠ u in 𝓝 (w : ℂ),
        e.symm ((chartAt ℂ w).symm u) = c.symm ((e₂.symm : ℂ → ℂ) u) := by
      rw [← hφz]
      filter_upwards [hright, U.2.mem_nhds (by rw [hφz]; exact w.2)] with u hu huU
      refine e.injective ?_
      rw [e.apply_symm_apply]
      refine Subtype.ext ?_
      rw [opens_chartAt_symm_apply_cast U huU, he,
        ← hΦψ (c.symm ((e₂.symm : ℂ → ℂ) u))]
      have h1 : Φ (c.symm ((e₂.symm : ℂ → ℂ) u)) = φ ((e₂.symm : ℂ → ℂ) u) := by
        rw [hφdef]; rfl
      have h2 : φ ((e₂.symm : ℂ → ℂ) u) = u := by rw [← h1]; exact hu
      rw [h1, h2]
    -- continuity of `e.symm` at `w`
    have hsymm' : e.symm =ᶠ[𝓝 w]
        (fun w' : U => c.symm ((e₂.symm : ℂ → ℂ) ((w' : U) : ℂ))) := by
      have hmap : Tendsto (fun w' : U => (chartAt ℂ w) w') (𝓝 w) (𝓝 ((chartAt ℂ w) w)) :=
        (chartAt ℂ w).continuousAt (mem_chart_source ℂ w)
      filter_upwards [hmap.eventually hsymm] with w' hw'
      rw [show (chartAt ℂ w).symm ((chartAt ℂ w) w') = w' from
        (chartAt ℂ w).left_inv (mem_chart_source ℂ w')] at hw'
      rwa [opens_chartAt_apply U w w'] at hw'
    have hr_an' : AnalyticAt ℂ (e₂.symm : ℂ → ℂ) ((w : ℂ)) := hφz ▸ hr_an
    have hcont : ContinuousAt e.symm w := by
      have hF : ContinuousAt (fun w' : U => c.symm ((e₂.symm : ℂ → ℂ) ((w' : U) : ℂ))) w := by
        refine ContinuousAt.comp (g := ⇑c.symm)
          (f := fun w' : U => (e₂.symm : ℂ → ℂ) ((w' : U) : ℂ)) ?_ ?_
        · rw [← hφz, hzsy]
          exact c.continuousAt_symm hzmem
        · exact ContinuousAt.comp hr_an'.continuousAt continuousAt_subtype_val
      exact hF.congr hsymm'.symm
    -- the chart representation
    have hchart : ContDiffAt ℂ ∞ ((chartAt ℂ x) ∘ ⇑e.symm ∘ (chartAt ℂ w).symm)
        ((chartAt ℂ w) w) := by
      have hpt : (chartAt ℂ w) w = (w : ℂ) := opens_chartAt_apply U w w
      rw [hpt]
      have htarget : ∀ᶠ u in 𝓝 ((w : ℂ)), (e₂.symm : ℂ → ℂ) u ∈ c.target := by
        refine (hr_an'.continuousAt).eventually (c.open_target.mem_nhds ?_)
        rw [← hφz, hzsy]
        exact c.map_source (mem_chart_source ℂ x)
      have hev : ((chartAt ℂ x) ∘ ⇑e.symm ∘ (chartAt ℂ w).symm)
          =ᶠ[𝓝 ((w : ℂ))] (e₂.symm : ℂ → ℂ) := by
        filter_upwards [hsymm, htarget] with u hu hru
        simp only [Function.comp_apply]
        rw [hu]
        exact c.right_inv hru
      exact ((analyticAt_congr hev).mpr hr_an').contDiffAt
    exact contMDiffAt_of_analytic_chart_subtype hcont hchart
  exact ⟨Diffeomorph.mk e hfwd hinv⟩

/-! ## The unit disc -/

/-- **A bijective holomorphic map `X → 𝔻` with non-vanishing chart derivative is a complex
diffeomorphism onto the disc.** -/
theorem nonempty_diffeomorph_disc_of_bijective {Φ : X → ℂ}
    (hmaps : ∀ x, Φ x ∈ (Helpers.DiscOpen : Set ℂ))
    (hbij : Function.Bijective fun x => (⟨Φ x, hmaps x⟩ : Helpers.DiscOpen))
    (hΦ : HolomorphicOnX Φ univ)
    (hderiv : ∀ x, deriv (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ Helpers.DiscOpen) :=
  nonempty_diffeomorph_open_of_bijective hmaps hbij hΦ hderiv

/-- The second disjunct of the uniformization conclusion, from a bijective holomorphic map onto
the unit disc with non-vanishing chart derivative. -/
theorem uniformization_of_bijective_to_disc {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {Φ : X → ℂ}
    (hmaps : ∀ x, Φ x ∈ (Helpers.DiscOpen : Set ℂ))
    (hbij : Function.Bijective fun x => (⟨Φ x, hmaps x⟩ : Helpers.DiscOpen))
    (hΦ : HolomorphicOnX Φ univ)
    (hderiv : ∀ x, deriv (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Helpers.uniformization_of_unitDisc_openSubset
    (nonempty_diffeomorph_disc_of_bijective hmaps hbij hΦ hderiv).some

end Submission
