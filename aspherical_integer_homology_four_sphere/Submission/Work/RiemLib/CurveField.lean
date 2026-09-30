import Submission.Work.RiemLib.GeodesicChart
import Submission.Work.RiemLib.Commons.Analysis.Calculus.exists_contDiffOn_eqOn_of_deriv_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Extending the velocity field of a curve to a global smooth section

The intrinsic definition `IsGeodesicAt cov γ t` of `Submission/Geodesic.lean` quantifies over all
*globally smooth* sections `Z` of the tangent bundle agreeing with the velocity field of `γ` in a
neighbourhood of `t`.  For the converse direction (intrinsic geodesic ⟹ chart equation) we must be
able to produce such a section.  This file proves that it exists as soon as the velocity field of
the curve does not vanish at `t`:

`exists_contMDiff_section_eventuallyEq_curveVelocity`.

The construction is local: in the chart at `γ t₀` the coordinate curve `u` has a non-vanishing
derivative, so by the inverse function theorem (`Commons.Analysis.Calculus.exists_contDiffAt_eqOn_of_deriv_ne_zero`,
i.e. the local flow box for a curve) the coordinate velocity `v = u'` extends to a smooth function
`F` on a neighbourhood of `u t₀`; the section `q ↦ σ_{F (chart q)}` is smooth near `γ t₀`
(scale by a bump function supported in the chart to globalise it).
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Commons.Geometry.Manifold.Tangent

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.CurveField

noncomputable section

/-- The coordinate velocity of a curve in the chart at `y`. -/
noncomputable def chartVel (y : M) (γ : ℝ → M) : ℝ → E :=
  deriv fun t => (extChartAt I y) (γ t)

/-- The chart coordinates of the velocity of `γ`: `deriv (chart ∘ γ) = (chart velocity)`. -/
lemma deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity
    {x : M} {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hx : γ t ∈ (chartAt H x).source) :
    deriv (fun s => (extChartAt I x) (γ s)) t
      = ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (γ t))
          (curveVelocity (I := I) γ t) := by
  rw [continuousLinearMapAt_curveVelocity (I := I) x hγ hx, mfderiv_eq_fderiv]
  rfl

/-- **Extension of the velocity field of a curve to a global smooth section.**  If `γ` is `C^∞` on
an open set `V ∋ t₀` and its velocity at `t₀` is nonzero, then there is a globally smooth section
of the tangent bundle agreeing with the velocity of `γ` in a neighbourhood of `t₀`. -/
theorem exists_contMDiff_section_eventuallyEq_curveVelocity
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hne : curveVelocity (I := I) γ t₀ ≠ 0) :
    ∃ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) ∧
      ∀ᶠ t in 𝓝 t₀, Z (γ t) = curveVelocity (I := I) γ t := by
  classical
  set x₁ : M := γ t₀ with hx₁
  have hsrc₁ : x₁ ∈ (chartAt H x₁).source := mem_chart_source H x₁
  -- an open set on which the coordinate curve is smooth
  have hV₁ : IsOpen (V ∩ γ ⁻¹' (chartAt H x₁).source) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.inter_mem (hV.mem_nhds ht.1)
      ((hγ.continuousOn.continuousAt (hV.mem_nhds ht.1)).preimage_mem_nhds
        ((chartAt H x₁).open_source.mem_nhds ht.2))
  have ht₀V₁ : t₀ ∈ V ∩ γ ⁻¹' (chartAt H x₁).source := by
    refine ⟨ht₀, ?_⟩
    rw [Set.mem_preimage, ← hx₁]
    exact hsrc₁
  set u : ℝ → E := fun t => (extChartAt I x₁) (γ t) with hu_def
  have hu : ContDiffOn ℝ ∞ u (V ∩ γ ⁻¹' (chartAt H x₁).source) := by
    have h2 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) ∞ (fun t : ℝ => (extChartAt I x₁) (γ t))
        (V ∩ γ ⁻¹' (chartAt H x₁).source) :=
      (contMDiffOn_extChartAt (I := I) (x := x₁)).comp
        (hγ.mono Set.inter_subset_left) (fun t ht => ht.2)
    exact h2.contDiffOn
  have hv : ContDiffOn ℝ ∞ (deriv u) (V ∩ γ ⁻¹' (chartAt H x₁).source) :=
    hu.deriv_of_isOpen hV₁ (le_of_eq (by simp))
  -- the derivative at `t₀` is nonzero
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀ :=
    (hγ.contMDiffAt (hV.mem_nhds ht₀)).mdifferentiableAt (by simp)
  have hder : deriv u t₀
      = ((trivializationAt E (TangentSpace I) x₁).continuousLinearMapAt ℝ (γ t₀))
          (curveVelocity (I := I) γ t₀) :=
    deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (x := x₁) hγmd
      (by rw [← hx₁]; exact hsrc₁)
  have hdne : deriv u t₀ ≠ 0 := by
    intro h0
    apply hne
    have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by
      rw [← hx₁]; exact hsrc₁
    have h1 : ((trivializationAt E (TangentSpace I) x₁).continuousLinearMapAt ℝ (γ t₀))
        (curveVelocity (I := I) γ t₀) = 0 := by rw [← hder]; exact h0
    have h2 := congrArg ((trivializationAt E (TangentSpace I) x₁).symmL ℝ (γ t₀)) h1
    rw [map_zero, Trivialization.symmL_continuousLinearMapAt _ hbase] at h2
    exact h2
  -- the smooth local extension of the coordinate velocity
  obtain ⟨F, W, hWopen, hWmem, hFcd, hFapp⟩ :=
    Commons.Analysis.Calculus.exists_contDiffOn_eqOn_of_deriv_ne_zero hV₁ ht₀V₁ hu hv hdne
  -- the open neighbourhood of `x₁` on which the local section is smooth
  have hUopen : IsOpen ((chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W)) :=
    (chartAt H x₁).isOpen_inter_preimage (hWopen.preimage I.continuous)
  have hx₁U : x₁ ∈ (chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W) := by
    refine ⟨hsrc₁, ?_⟩
    rw [Set.mem_preimage, Set.mem_preimage]
    have : I ((chartAt H x₁) x₁) = u t₀ := by
      rw [hu_def, hx₁]; rfl
    rw [this]
    exact hWmem
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₁).mem_iff.mp
    (hUopen.mem_nhds hx₁U)
  -- the local section, and its globalization
  refine ⟨fun q : M => ψ q •
      (trivializationAt E (TangentSpace I) x₁).symmL ℝ q (F ((extChartAt I x₁) q)), ?_, ?_⟩
  · refine ContMDiffOn.smul_section_of_tsupport
      (u := (chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W))
      (ψ := (ψ : M → ℝ))
      (s := fun q : M =>
        (trivializationAt E (TangentSpace I) x₁).symmL ℝ q (F ((extChartAt I x₁) q)))
      ?_ hUopen hψts ?_
    · exact ψ.contMDiff.contMDiffOn
    · have hFe : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun q : M => F ((extChartAt I x₁) q))
          ((chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W)) :=
        hFcd.contMDiffOn.comp
          ((contMDiffOn_extChartAt (I := I) (x := x₁)).mono Set.inter_subset_left)
          (fun q hq => hq.2)
      have hpair : ContMDiffOn I (I.prod 𝓘(ℝ,E)) ∞
          (fun q : M => (q, F ((extChartAt I x₁) q)))
          ((chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W)) :=
        ContMDiffOn.prodMk (contMDiffOn_id (I := I)
          (s := (chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W))) hFe
      refine (Commons.Geometry.Manifold.Tangent.contMDiffOn_trivializationAt_symmL_apply
        (I := I) x₁).comp hpair ?_
      intro q hq
      exact ⟨hq.1, trivial⟩
  · -- the value along the curve
    have hψev : ∀ᶠ t in 𝓝 t₀, (ψ : M → ℝ) (γ t) = 1 :=
      (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto.eventually ψ.eventuallyEq_one
    have hsrcev : ∀ᶠ t in 𝓝 t₀, γ t ∈ (chartAt H x₁).source :=
      (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto
        ((chartAt H x₁).open_source.mem_nhds (by rw [← hx₁]; exact hsrc₁))
    have hVev : ∀ᶠ t in 𝓝 t₀, t ∈ V := hV.mem_nhds ht₀
    filter_upwards [hFapp, hψev, hsrcev, hVev] with t hFt hψ1 hsrc htV
    rw [hψ1, one_smul]
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
      (hγ.contMDiffAt (hV.mem_nhds htV)).mdifferentiableAt (by simp)
    rw [hFt, deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (x := x₁) hmd hsrc]
    have hbase : γ t ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := hsrc
    exact Trivialization.symmL_continuousLinearMapAt _ hbase (curveVelocity (I := I) γ t)



/-- **Extension of an arbitrary smooth field along a curve to a global smooth section.**
If `γ` is `C^∞` on an open set `V ∋ t₀`, its velocity at `t₀` is nonzero, and `α : ℝ → E` is `C^∞`
on `V ∩ γ ⁻¹' (chartAt H (γ t₀)).source`, then there is a globally smooth section `Z` of the tangent
bundle agreeing, near `t₀`, with the field `t ↦ frameVector (γ t₀) (γ t) (α t)` whose coordinates in
the chart at `γ t₀` are `α`.

This is the tool that makes the covariant derivative along a curve intrinsic: any `C^∞` field along
`γ` (with nonzero velocity) is, near each time, the restriction of a globally smooth section. -/
theorem exists_contMDiff_section_eventuallyEq_of_contDiffOn
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {α : ℝ → E} (hα : ContDiffOn ℝ ∞ α (V ∩ γ ⁻¹' (chartAt H (γ t₀)).source)) :
    ∃ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) ∧
      ∀ᶠ t in 𝓝 t₀, Z (γ t) = frameVector (I := I) (γ t₀) (γ t) (α t) := by
  classical
  set x₁ : M := γ t₀ with hx₁
  have hsrc₁ : x₁ ∈ (chartAt H x₁).source := mem_chart_source H x₁
  have hV₁ : IsOpen (V ∩ γ ⁻¹' (chartAt H x₁).source) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.inter_mem (hV.mem_nhds ht.1)
      ((hγ.continuousOn.continuousAt (hV.mem_nhds ht.1)).preimage_mem_nhds
        ((chartAt H x₁).open_source.mem_nhds ht.2))
  have ht₀V₁ : t₀ ∈ V ∩ γ ⁻¹' (chartAt H x₁).source := by
    refine ⟨ht₀, ?_⟩
    rw [Set.mem_preimage, ← hx₁]
    exact hsrc₁
  set u : ℝ → E := fun t => (extChartAt I x₁) (γ t) with hu_def
  have hu : ContDiffOn ℝ ∞ u (V ∩ γ ⁻¹' (chartAt H x₁).source) := by
    have h2 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) ∞ (fun t : ℝ => (extChartAt I x₁) (γ t))
        (V ∩ γ ⁻¹' (chartAt H x₁).source) :=
      (contMDiffOn_extChartAt (I := I) (x := x₁)).comp
        (hγ.mono Set.inter_subset_left) (fun t ht => ht.2)
    exact h2.contDiffOn
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀ :=
    (hγ.contMDiffAt (hV.mem_nhds ht₀)).mdifferentiableAt (by simp)
  have hder : deriv u t₀
      = ((trivializationAt E (TangentSpace I) x₁).continuousLinearMapAt ℝ (γ t₀))
          (curveVelocity (I := I) γ t₀) :=
    deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (x := x₁) hγmd
      (by rw [← hx₁]; exact hsrc₁)
  have hdne : deriv u t₀ ≠ 0 := by
    intro h0
    apply hne
    have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by
      rw [← hx₁]; exact hsrc₁
    have h1 : ((trivializationAt E (TangentSpace I) x₁).continuousLinearMapAt ℝ (γ t₀))
        (curveVelocity (I := I) γ t₀) = 0 := by rw [← hder]; exact h0
    have h2 := congrArg ((trivializationAt E (TangentSpace I) x₁).symmL ℝ (γ t₀)) h1
    rw [map_zero, Trivialization.symmL_continuousLinearMapAt _ hbase] at h2
    exact h2
  obtain ⟨F, W, hWopen, hWmem, hFcd, hFapp⟩ :=
    Commons.Analysis.Calculus.exists_contDiffOn_eqOn_of_deriv_ne_zero hV₁ ht₀V₁ hu hα hdne
  have hUopen : IsOpen ((chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W)) :=
    (chartAt H x₁).isOpen_inter_preimage (hWopen.preimage I.continuous)
  have hx₁U : x₁ ∈ (chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W) := by
    refine ⟨hsrc₁, ?_⟩
    rw [Set.mem_preimage, Set.mem_preimage]
    have : I ((chartAt H x₁) x₁) = u t₀ := by
      rw [hu_def, hx₁]; rfl
    rw [this]
    exact hWmem
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₁).mem_iff.mp
    (hUopen.mem_nhds hx₁U)
  refine ⟨fun q : M => ψ q •
      (trivializationAt E (TangentSpace I) x₁).symmL ℝ q (F ((extChartAt I x₁) q)), ?_, ?_⟩
  · refine ContMDiffOn.smul_section_of_tsupport
      (u := (chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W))
      (ψ := (ψ : M → ℝ))
      (s := fun q : M =>
        (trivializationAt E (TangentSpace I) x₁).symmL ℝ q (F ((extChartAt I x₁) q)))
      ?_ hUopen hψts ?_
    · exact ψ.contMDiff.contMDiffOn
    · have hFe : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun q : M => F ((extChartAt I x₁) q))
          ((chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W)) :=
        hFcd.contMDiffOn.comp
          ((contMDiffOn_extChartAt (I := I) (x := x₁)).mono Set.inter_subset_left)
          (fun q hq => hq.2)
      have hpair : ContMDiffOn I (I.prod 𝓘(ℝ,E)) ∞
          (fun q : M => (q, F ((extChartAt I x₁) q)))
          ((chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W)) :=
        ContMDiffOn.prodMk (contMDiffOn_id (I := I)
          (s := (chartAt H x₁).source ∩ (chartAt H x₁) ⁻¹' (I ⁻¹' W))) hFe
      refine (Commons.Geometry.Manifold.Tangent.contMDiffOn_trivializationAt_symmL_apply
        (I := I) x₁).comp hpair ?_
      intro q hq
      exact ⟨hq.1, trivial⟩
  · have hψev : ∀ᶠ t in 𝓝 t₀, (ψ : M → ℝ) (γ t) = 1 :=
      (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto.eventually ψ.eventuallyEq_one
    have hsrcev : ∀ᶠ t in 𝓝 t₀, γ t ∈ (chartAt H x₁).source :=
      (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto
        ((chartAt H x₁).open_source.mem_nhds (by rw [← hx₁]; exact hsrc₁))
    filter_upwards [hFapp, hψev, hsrcev] with t hFt hψ1 hsrc
    rw [hψ1, one_smul]
    show (trivializationAt E (TangentSpace I) x₁).symmL ℝ (γ t) (F ((extChartAt I x₁) (γ t)))
      = frameVector (I := I) x₁ (γ t) (α t)
    rw [hFt]
    rfl

/-- **Extension of a smooth field given in a *fixed* chart to a global smooth section.**
If `γ` is `C^∞` on an open set `V ∋ t₀` and stays in the chart at `x₀`, its velocity at `t₀` is
nonzero, and `y : ℝ → E` is `C^∞` on `V`, then the field `t ↦ frameVector x₀ (γ t) (y t)` (whose
coordinates in the chart at `x₀` are `y`) agrees near `t₀` with a globally smooth section.

This is the variant of `exists_contMDiff_section_eventuallyEq_of_contDiffOn` in which the chart
centre does not move with `t`; it is what makes it possible to *compute* the intrinsic covariant
derivative `∇_{γ'}Y` of a field given by coordinates in a single chart. -/
theorem exists_contMDiff_section_eventuallyEq_of_contDiffOn_chart
    (x₀ : M) {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hsrcV : ∀ t ∈ V, γ t ∈ (chartAt H x₀).source)
    (hne : curveVelocity (I := I) γ t₀ ≠ 0)
    {y : ℝ → E} (hy : ContDiffOn ℝ ∞ y (V ∩ γ ⁻¹' (chartAt H x₀).source)) :
    ∃ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) ∧
      ∀ᶠ t in 𝓝 t₀, Z (γ t) = frameVector (I := I) x₀ (γ t) (y t) := by
  classical
  have hsrc₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hV₁ : IsOpen (V ∩ γ ⁻¹' (chartAt H x₀).source) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.inter_mem (hV.mem_nhds ht.1)
      ((hγ.continuousOn.continuousAt (hV.mem_nhds ht.1)).preimage_mem_nhds
        ((chartAt H x₀).open_source.mem_nhds ht.2))
  have ht₀V₁ : t₀ ∈ V ∩ γ ⁻¹' (chartAt H x₀).source := by
    refine ⟨ht₀, ?_⟩
    rw [Set.mem_preimage]
    exact hsrcV t₀ ht₀
  set u : ℝ → E := fun t => (extChartAt I x₀) (γ t) with hu_def
  have hu : ContDiffOn ℝ ∞ u (V ∩ γ ⁻¹' (chartAt H x₀).source) := by
    have h2 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) ∞ (fun t : ℝ => (extChartAt I x₀) (γ t))
        (V ∩ γ ⁻¹' (chartAt H x₀).source) :=
      (contMDiffOn_extChartAt (I := I) (x := x₀)).comp
        (hγ.mono Set.inter_subset_left) (fun t ht => ht.2)
    exact h2.contDiffOn
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀ :=
    (hγ.contMDiffAt (hV.mem_nhds ht₀)).mdifferentiableAt (by simp)
  have hder : deriv u t₀
      = ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀))
          (curveVelocity (I := I) γ t₀) :=
    deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (x := x₀) hγmd
      (hsrcV t₀ ht₀)
  have hdne : deriv u t₀ ≠ 0 := by
    intro h0
    apply hne
    have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hsrcV t₀ ht₀
    have h1 : ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t₀))
        (curveVelocity (I := I) γ t₀) = 0 := by rw [← hder]; exact h0
    have h2 := congrArg ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t₀)) h1
    rw [map_zero, Trivialization.symmL_continuousLinearMapAt _ hbase] at h2
    exact h2
  obtain ⟨F, W, hWopen, hWmem, hFcd, hFapp⟩ :=
    Commons.Analysis.Calculus.exists_contDiffOn_eqOn_of_deriv_ne_zero hV₁ ht₀V₁ hu hy hdne
  have hUopen : IsOpen ((chartAt H x₀).source ∩ (chartAt H x₀) ⁻¹' (I ⁻¹' W)) :=
    (chartAt H x₀).isOpen_inter_preimage (hWopen.preimage I.continuous)
  have ht₀U : γ t₀ ∈ (chartAt H x₀).source ∩ (chartAt H x₀) ⁻¹' (I ⁻¹' W) := by
    refine ⟨hsrcV t₀ ht₀, ?_⟩
    rw [Set.mem_preimage, Set.mem_preimage]
    have h1 : I ((chartAt H x₀) (γ t₀)) = u t₀ := by
      rw [hu_def]; rfl
    rw [h1]
    exact hWmem
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) (γ t₀)).mem_iff.mp
    (hUopen.mem_nhds ht₀U)
  refine ⟨fun q : M => ψ q •
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (F ((extChartAt I x₀) q)), ?_, ?_⟩
  · refine ContMDiffOn.smul_section_of_tsupport
      (u := (chartAt H x₀).source ∩ (chartAt H x₀) ⁻¹' (I ⁻¹' W))
      (ψ := (ψ : M → ℝ))
      (s := fun q : M =>
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (F ((extChartAt I x₀) q)))
      ?_ hUopen hψts ?_
    · exact ψ.contMDiff.contMDiffOn
    · have hFe : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun q : M => F ((extChartAt I x₀) q))
          ((chartAt H x₀).source ∩ (chartAt H x₀) ⁻¹' (I ⁻¹' W)) :=
        hFcd.contMDiffOn.comp
          ((contMDiffOn_extChartAt (I := I) (x := x₀)).mono Set.inter_subset_left)
          (fun q hq => hq.2)
      have hpair : ContMDiffOn I (I.prod 𝓘(ℝ,E)) ∞
          (fun q : M => (q, F ((extChartAt I x₀) q)))
          ((chartAt H x₀).source ∩ (chartAt H x₀) ⁻¹' (I ⁻¹' W)) :=
        ContMDiffOn.prodMk (contMDiffOn_id (I := I)
          (s := (chartAt H x₀).source ∩ (chartAt H x₀) ⁻¹' (I ⁻¹' W))) hFe
      refine (Commons.Geometry.Manifold.Tangent.contMDiffOn_trivializationAt_symmL_apply
        (I := I) x₀).comp hpair ?_
      intro q hq
      exact ⟨hq.1, trivial⟩
  · have hψev : ∀ᶠ t in 𝓝 t₀, (ψ : M → ℝ) (γ t) = 1 :=
      (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto.eventually ψ.eventuallyEq_one
    have hsrcev : ∀ᶠ t in 𝓝 t₀, γ t ∈ (chartAt H x₀).source :=
      (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto
        ((chartAt H x₀).open_source.mem_nhds (hsrcV t₀ ht₀))
    filter_upwards [hFapp, hψev, hsrcev] with t hFt hψ1 hsrc
    rw [hψ1, one_smul]
    show (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) (F ((extChartAt I x₀) (γ t)))
      = frameVector (I := I) x₀ (γ t) (y t)
    rw [hFt]
    rfl

/-! ## Status

The construction of the smooth section agreeing with the velocity of a curve requires the
**local flow box for a curve with non-vanishing derivative**,
`Commons.Analysis.Calculus.exists_contDiffOn_eqOn_of_deriv_ne_zero` (requested; it is the `C^∞`
on-a-neighbourhood version of `exists_contDiffAt_eqOn_of_deriv_ne_zero`).  With it the argument is:

* let `x₁ = γ t₀` and work in the chart at `x₁`; set `u = chart ∘ γ` and `v = deriv u`;
* by the flow box, `v` agrees near `t₀` with a smooth function `F` defined on a neighbourhood `W`
  of `u t₀`;
* the section `s q = (trivializationAt E (TangentSpace I) x₁).symmL ℝ q (F (chart q))` is smooth on
  the open neighbourhood `(extChartAt I x₁) ⁻¹' W` of `x₁`;
* multiplying by a `SmoothBumpFunction` with support in that neighbourhood
  (`ContMDiffOn.smul_section_of_tsupport`) gives a *globally* smooth section `Z` which agrees with
  the velocity of `γ` near `t₀`, because
  `curveVelocity γ t = (trivializationAt E (TangentSpace I) x₁).symmL ℝ (γ t) (deriv u t)`
  (`deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity`).
-/

end

end Submission.CurveField
