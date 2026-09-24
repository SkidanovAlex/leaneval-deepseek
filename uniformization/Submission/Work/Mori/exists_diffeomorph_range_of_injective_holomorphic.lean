import Submission.Work.Mori.Defs
import Submission.Work.Parabolic.isOpenMap_of_injective_holomorphic
import Submission.Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
import Submission.Packaging

/-!
# An injective holomorphic map into `ℂ` is a biholomorphism onto its range

An injective holomorphic map `φ : X → ℂ` on a Riemann surface `X` is an *open embedding*
(`Work.Parabolic.isOpenMap_of_injective_holomorphic` for the open mapping theorem), hence a
homeomorphism onto its (open) image; the inverse is holomorphic because a holomorphic function with
nowhere vanishing derivative is locally invertible with holomorphic inverse (the one-dimensional
inverse function theorem).  Consequently

> `Work.Mori.exists_diffeomorph_range_of_injective_holomorphic`:
> there is an open subset `U ⊆ ℂ` with `(U : Set ℂ) = Set.range φ` and a complex diffeomorphism
> `X ≃ₘ⟮mℂ, mℂ⟯ U`.

This is the "planarity ⟹ plane domain" step of the Mori route to the parabolic case of
uniformization: it converts the existence of an injective holomorphic map into `ℂ` (the output of
the ABS theorem, `Work.Mori.ABSTheorem` / `Work.Mori.HasHolomorphicEmbedding`) into a *normal form*
`X ≃ₘ U` with `U` an open subset of `ℂ`, to which the potential theory of plane domains (polarity,
the winding obstruction) applies.

The chart bookkeeping is the same as in `Submission.Packaging`
(`Submission.nonempty_diffeomorph_of_analytic_equiv`), with the only new ingredient being the
preferred chart of an open subset of `ℂ`, which is the inclusion
(`Work.Mori.chartAt_opens_apply`).  The result here is the local version of
`Submission.analyticAt_chartAt_inv_of_analytic`, whose statement assumes a *global* bijection onto
`ℂ`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart bookkeeping for an open subset of `ℂ`.**  The preferred chart of the open subtype
`U : Opens ℂ` at a point `u` is the restriction of the identity chart of `ℂ`, hence the inclusion:
`(chartAt ℂ u) z = (z : ℂ)` for every `z : U`. -/
theorem chartAt_opens_apply (U : TopologicalSpace.Opens ℂ) (u z : U) :
    (chartAt ℂ u) z = (z : ℂ) := by
  rw [TopologicalSpace.Opens.chartAt_eq (x := u), OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- **A complex one-manifold has more than one point.**  The preferred chart at `x` is a partial
homeomorphism with an open, nonempty source and an open target; an open nonempty subset of `ℂ`
contains more than one point, so the source does too. -/
theorem exists_ne_of_chartedSpace_complex (x : X) : ∃ y : X, y ≠ x := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hxt : c x ∈ c.target := c.map_source hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) hxt
  set δ : ℂ := ((ε / 2 : ℝ) : ℂ) with hδ
  have hδne : δ ≠ 0 := by
    intro h
    rw [hδ] at h
    have : ε / 2 = 0 := by exact_mod_cast h
    linarith
  have hmem : c x + δ ∈ c.target := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hδ]
    have hhalf : (0:ℝ) < ε / 2 := by linarith
    have hnorm : ‖(((ε / 2 : ℝ)) : ℂ)‖ = ε / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
    rw [hnorm]; linarith)
  refine ⟨c.symm (c x + δ), fun hcontra => ?_⟩
  have h1 : c (c.symm (c x + δ)) = c x := by rw [hcontra]
  rw [c.right_inv hmem] at h1
  have h2 : δ = 0 := by
    have h4 : c x + δ = c x + 0 := by rw [add_zero]; exact h1
    exact add_left_cancel h4
  exact hδne h2

/-- **An injective holomorphic map into `ℂ` is a biholomorphism onto its range.**  There is an open
subset `U ⊆ ℂ` with `(U : Set ℂ) = Set.range φ` and a complex diffeomorphism `X ≃ₘ⟮mℂ,mℂ⟯ U`. -/
theorem exists_diffeomorph_range_of_injective_holomorphic {φ : X → ℂ}
    (hφ : Submission.HolomorphicOnX φ Set.univ) (hinj : Function.Injective φ) :
    ∃ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) = Set.range φ ∧
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X U
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  have hcont : Continuous φ := hφ.continuous
  have hopen : IsOpenMap φ := Work.Parabolic.isOpenMap_of_injective_holomorphic hφ hinj
  have hemb : Topology.IsOpenEmbedding φ :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
  set U : TopologicalSpace.Opens ℂ := ⟨Set.range φ, hemb.isOpen_range⟩ with hU
  refine ⟨U, rfl, ?_⟩
  -- the bijection `X ≃ U` induced by `φ`
  have hbij : Function.Bijective (fun x : X => (⟨φ x, Set.mem_range_self x⟩ : U)) := by
    constructor
    · intro a b hab
      exact hinj (Subtype.ext_iff.mp hab)
    · intro u
      obtain ⟨x, hx⟩ := u.2
      exact ⟨x, Subtype.ext hx⟩
  set e : X ≃ U := Equiv.ofBijective (fun x : X => (⟨φ x, Set.mem_range_self x⟩ : U)) hbij with he
  have hcoe : ∀ x : X, (e x : ℂ) = φ x := fun x => rfl
  -- `U` as a subtype is `Set.range φ`, so the homeomorphism of the embedding computes `e`
  have hhom : ∀ x : X, (hemb.isEmbedding.toHomeomorph x : U) = e x := fun x => Subtype.ext rfl
  have hecont : Continuous e := by
    have h1 : (e : X → U) = hemb.isEmbedding.toHomeomorph := by
      funext x; exact (hhom x).symm
    rw [h1]
    exact (hemb.isEmbedding.toHomeomorph).continuous
  have hesymm : Continuous e.symm := by
    have h1 : (e.symm : U → X) = (hemb.isEmbedding.toHomeomorph).symm := by
      funext u
      refine (Equiv.injective e) ?_
      rw [e.apply_symm_apply]
      exact ((hhom _).symm.trans ((hemb.isEmbedding.toHomeomorph).apply_symm_apply u)).symm
    rw [h1]
    exact (hemb.isEmbedding.toHomeomorph).continuous_symm
  -- the forward analyticity
  have hfor : ∀ x : X, AnalyticAt ℂ ((chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) := by
    intro x
    have hbase : AnalyticAt ℂ (φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hφ x (mem_univ x)
    refine hbase.congr ?_
    filter_upwards with w
    simp only [Function.comp_apply]
    rw [chartAt_opens_apply U (e x) (e ((chartAt ℂ x).symm w))]
    exact hcoe ((chartAt ℂ x).symm w)
  -- the inverse analyticity
  have hinv : ∀ y : U, AnalyticAt ℂ ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y) := by
    intro y
    set x : X := e.symm y with hx
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
    set φl : ℂ → ℂ := φ ∘ c.symm with hφl
    set z : ℂ := c x with hz
    have hφan : AnalyticAt ℂ φl z := by
      rw [hφl, hz, hc]
      exact hφ x (mem_univ x)
    have hd : deriv φl z ≠ 0 := by
      have h := Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic (Φ := φ) hinj
        (fun w => hφ w (mem_univ w)) (exists_ne_of_chartedSpace_complex x)
      rw [hφl, hz, hc]
      exact h
    let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 (deriv φl z) hd)
    have hfd : HasStrictFDerivAt φl i.toContinuousLinearMap z := hφan.hasStrictDerivAt
    let e₂ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph φl
    have he₂ : (e₂ : ℂ → ℂ) = φl := rfl
    have hzs : z ∈ e₂.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfd
    have hzt : φl z ∈ e₂.target := by rw [← he₂]; exact e₂.map_source hzs
    have hzsy : e₂.symm (φl z) = z := by rw [← he₂]; exact e₂.left_inv hzs
    have hφz : φl z = (y : ℂ) := by
      rw [hφl, hz, hc, Function.comp_apply, c.left_inv (mem_chart_source ℂ x)]
      rw [← hcoe x, hx, e.apply_symm_apply]
    -- the local inverse is analytic
    have hr_an : AnalyticAt ℂ (e₂.symm : ℂ → ℂ) (φl z) := by
      refine OpenPartialHomeomorph.analyticAt_symm (f := e₂) (a := φl z) (i := i) hzt ?_ ?_
      · rw [hzsy, he₂]
        exact hφan
      · rw [hzsy, he₂]
        exact hfd.hasFDerivAt.fderiv
    -- `e` inverts the local inverse, near `y`
    have hright : ∀ᶠ u : ℂ in 𝓝 (φl z), ((e (c.symm (e₂.symm u)) : U) : ℂ) = u := by
      filter_upwards [e₂.open_target.mem_nhds hzt] with u hu
      have h1 : (e (c.symm (e₂.symm u)) : ℂ) = φl (e₂.symm u) := hcoe (c.symm (e₂.symm u))
      rw [h1, ← he₂]
      exact e₂.right_inv hu
    have hcont_ev : ∀ᶠ u : U in 𝓝 y,
        ((e (c.symm (e₂.symm ((u : ℂ)))) : U) : ℂ) = (u : ℂ) := by
      have htend : Tendsto (fun u : U => (u : ℂ)) (𝓝 y) (𝓝 (φl z)) := by
        rw [hφz]
        exact continuous_subtype_val.continuousAt
      exact htend.eventually hright
    have hev : e.symm =ᶠ[𝓝 y] (fun u : U => c.symm (e₂.symm ((u : ℂ)))) := by
      filter_upwards [hcont_ev] with u hu
      refine (Equiv.injective e) ?_
      rw [e.apply_symm_apply]
      exact Subtype.ext hu.symm
    -- the chart representation of `e.symm` near `y` is the local inverse `e₂.symm`
    have htarget : ∀ᶠ w : ℂ in 𝓝 ((chartAt ℂ y) y), e₂.symm w ∈ c.target := by
      have hval : ((chartAt ℂ y) y) = φl z := by rw [chartAt_opens_apply U y y, hφz]
      have hzmem : z ∈ c.target := by rw [hz]; exact c.map_source (mem_chart_source ℂ x)
      have htend : Tendsto (fun w : ℂ => e₂.symm w) (𝓝 ((chartAt ℂ y) y)) (𝓝 z) := by
        rw [hval]
        have h :=
          (e₂.symm.continuousAt (by rw [OpenPartialHomeomorph.symm_source]; exact hzt)).tendsto
        rw [hzsy] at h
        exact h
      exact htend.eventually (c.open_target.mem_nhds hzmem)
    have hchart : ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm)
        =ᶠ[𝓝 ((chartAt ℂ y) y)] (e₂.symm : ℂ → ℂ) := by
      have hs1 : Tendsto (fun w : ℂ => (chartAt ℂ y).symm w) (𝓝 ((chartAt ℂ y) y)) (𝓝 y) := by
        simpa only [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)] using
          ((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source (mem_chart_source ℂ y))).tendsto
      have hev2 : (e.symm ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 ((chartAt ℂ y) y)]
          ((fun u : U => c.symm (e₂.symm ((u : ℂ)))) ∘ (chartAt ℂ y).symm) :=
        hev.comp_tendsto hs1
      have hsymm : ∀ᶠ w : ℂ in 𝓝 ((chartAt ℂ y) y),
          (((chartAt ℂ y).symm w : U) : ℂ) = w := by
        filter_upwards [(chartAt ℂ y).open_target.mem_nhds
          ((chartAt ℂ y).map_source (mem_chart_source ℂ y))] with w hw
        rw [← chartAt_opens_apply U y ((chartAt ℂ y).symm w)]
        exact (chartAt ℂ y).right_inv hw
      filter_upwards [hev2, hsymm, htarget] with w hw hsw htw
      have h1 : e.symm ((chartAt ℂ y).symm w) = c.symm (e₂.symm w) := by
        have h2 := hw
        simp only [Function.comp_apply] at h2
        rw [hsw] at h2
        exact h2
      have h3 : chartAt ℂ (e.symm y) = c := by rw [← hx, hc]
      simp only [Function.comp_apply]
      rw [h3, h1, c.right_inv htw]
    refine (analyticAt_congr hchart).mpr ?_
    have hval : ((chartAt ℂ y) y) = φl z := by
      rw [chartAt_opens_apply U y y, hφz]
    rw [hval]
    exact hr_an
  exact Submission.nonempty_diffeomorph_of_analytic_equiv e hecont hesymm hfor hinv

end Work.Mori
