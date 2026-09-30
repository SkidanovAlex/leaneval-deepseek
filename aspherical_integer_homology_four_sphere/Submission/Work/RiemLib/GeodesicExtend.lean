import Submission.Work.RiemLib.CurveField
import Submission.Work.RiemLib.GeodesicChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Chart-independence of the geodesic equation

`Submission/GeodesicChart.lean` proves that an intrinsic geodesic satisfies the chart geodesic
equation in the chart at `x₀`, provided the velocity field of the curve can be extended to a
globally smooth section (`Submission/CurveField.lean` provides that extension).

Here we draw the consequences:

* `curveVelocity_congr_of_eventuallyEq`, `isGeodesicAt_congr_of_eventuallyEq`: the velocity and the
  geodesic equation depend only on the germ of the curve;
* `chartGeodesic_eq_of_isGeodesicAt`: **the chart geodesic equation holds for an intrinsic geodesic
  in *every* chart**, which is the missing half of the equivalence "chart equation ⟺ intrinsic
  equation" (`Geodesic.cov_eq_zero_of_chartGeodesic` is the other half).  This is the
  **chart-independence of the geodesic equation**, the key structural result that lets one continue
  a geodesic beyond the chart in which it was constructed.
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.CurveField
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

namespace Submission.GeodesicExtend

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- The velocity of a curve depends only on the germ of the curve. -/
lemma curveVelocity_congr_of_eventuallyEq {γ γ' : ℝ → M} {t : ℝ} (h : γ =ᶠ[𝓝 t] γ') :
    curveVelocity (I := I) γ t = curveVelocity (I := I) γ' t := by
  have ht : γ t = γ' t := h.eq_of_nhds
  rw [curveVelocity_apply, curveVelocity_apply, ht]
  rw [h.mfderiv_eq (I := 𝓘(ℝ)) (I' := I)]
  -- v4.34: the rewrite leaves a `tangentSpaceCast`, definitionally the identity.
  all_goals first | rfl | (ext v; rfl)

/-- The geodesic equation depends only on the germ of the curve. -/
lemma isGeodesicAt_congr_of_eventuallyEq {γ γ' : ℝ → M} {t : ℝ} (h : γ =ᶠ[𝓝 t] γ') :
    IsGeodesicAt (I := I) cov γ t ↔ IsGeodesicAt (I := I) cov γ' t := by
  obtain ⟨U, hUsub, hUopen, hUt⟩ := _root_.mem_nhds_iff.mp h
  have hvelU : ∀ s ∈ U, curveVelocity (I := I) γ s = curveVelocity (I := I) γ' s :=
    fun s hs => curveVelocity_congr_of_eventuallyEq (I := I)
      (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hs) (fun r hr => hUsub hr))
  constructor
  · intro hg Z hZ hZeq
    have h1 : cov Z (γ' t) (curveVelocity (I := I) γ' t)
        = cov Z (γ t) (curveVelocity (I := I) γ t) := by
      have ht : γ t = γ' t := h.eq_of_nhds
      have hv : curveVelocity (I := I) γ t = curveVelocity (I := I) γ' t :=
        curveVelocity_congr_of_eventuallyEq (I := I) h
      rw [hv, ht]
    rw [h1]
    refine hg Z hZ ?_
    filter_upwards [hZeq, hUopen.mem_nhds hUt] with s hs hUs
    rw [hUsub hUs, hvelU s hUs]
    exact hs
  · intro hg Z hZ hZeq
    have h1 : cov Z (γ t) (curveVelocity (I := I) γ t)
        = cov Z (γ' t) (curveVelocity (I := I) γ' t) := by
      have ht : γ t = γ' t := h.eq_of_nhds
      have hv : curveVelocity (I := I) γ t = curveVelocity (I := I) γ' t :=
        curveVelocity_congr_of_eventuallyEq (I := I) h
      rw [hv, ht]
    rw [h1]
    refine hg Z hZ ?_
    filter_upwards [hZeq, hUopen.mem_nhds hUt] with s hs hUs
    rw [hUsub hUs, hvelU s hUs] at hs
    exact hs

/-- **Chart-independence of the geodesic equation.**  If `γ` is an intrinsic geodesic at `t₀` with
nonzero velocity, and `γ` is `C^∞` on a neighbourhood of `t₀`, then in the chart at *any* point `x₀`
whose chart contains `γ t₀`, the coordinate curve `s ↦ (extChartAt I x₀) (γ s)` of `γ` satisfies the
chart geodesic equation at `t₀`:
`(chart ∘ γ)'' = -Γ((chart ∘ γ)')(γ')`.

Together with `Geodesic.cov_eq_zero_of_chartGeodesic` (the converse implication) this says that the
geodesic equation is independent of the chart used to write it. -/
theorem hasDerivAt_deriv_chartCurve_of_isGeodesicAt
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hsrc : γ t₀ ∈ (chartAt H x₀).source)
    (hgeo : IsGeodesicAt (I := I) cov γ t₀)
    (hne : curveVelocity (I := I) γ t₀ ≠ 0) :
    HasDerivAt (fun t => deriv (fun s => (extChartAt I x₀) (γ s)) t)
      (chartGeodesicVectorField cov x₀ ((extChartAt I x₀) (γ t₀),
        deriv (fun s => (extChartAt I x₀) (γ s)) t₀)) t₀ := by
  classical
  -- the globally smooth section extending the velocity
  obtain ⟨Z, hZ, hZev⟩ := exists_contMDiff_section_eventuallyEq_curveVelocity hV ht₀ hγ hne
  -- the open set on which the chart curve is smooth
  have hWopen : IsOpen (V ∩ γ ⁻¹' (chartAt H x₀).source) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.inter_mem (hV.mem_nhds ht.1)
      ((hγ.continuousOn.continuousAt (hV.mem_nhds ht.1)).preimage_mem_nhds
        ((chartAt H x₀).open_source.mem_nhds ht.2))
  have ht₀W : t₀ ∈ V ∩ γ ⁻¹' (chartAt H x₀).source := ⟨ht₀, hsrc⟩
  set u : ℝ → E := fun s => (extChartAt I x₀) (γ s) with hu_def
  have hu : ContDiffOn ℝ ∞ u (V ∩ γ ⁻¹' (chartAt H x₀).source) := by
    have h2 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) ∞ (fun t : ℝ => (extChartAt I x₀) (γ t))
        (V ∩ γ ⁻¹' (chartAt H x₀).source) :=
      (contMDiffOn_extChartAt (I := I) (x := x₀)).comp
        (hγ.mono Set.inter_subset_left) (fun t ht => ht.2)
    exact h2.contDiffOn
  have hv : ContDiffOn ℝ ∞ (deriv u) (V ∩ γ ⁻¹' (chartAt H x₀).source) :=
    hu.deriv_of_isOpen hWopen (le_of_eq (by simp))
  -- an interval around `t₀` on which all the good properties hold
  have hsrcEv : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H x₀).source :=
    (hγ.continuousOn.continuousAt (hV.mem_nhds ht₀)).tendsto
      ((chartAt H x₀).open_source.mem_nhds hsrc)
  have hev : ∀ᶠ s in 𝓝 t₀, Z (γ s) = curveVelocity (I := I) γ s ∧
      γ s ∈ (chartAt H x₀).source ∧ s ∈ V := by
    filter_upwards [hZev, hsrcEv, hV.mem_nhds ht₀] with s h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨δ, hδ, hδsub⟩ := (nhds_basis_Ioo_pos t₀).mem_iff.mp hev
  have hsta : t₀ - δ < t₀ := by linarith
  have ht₀b : t₀ < t₀ + δ := by linarith
  have ht₀I : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨hsta, ht₀b⟩
  -- the eventual agreement of `γ` and the chart curve
  have hagree : γ =ᶠ[𝓝 t₀] (fun s => (extChartAt I x₀).symm (u s)) := by
    filter_upwards [hsrcEv] with s hs
    rw [hu_def]
    exact (PartialEquiv.left_inv (extChartAt I x₀) (by rw [extChartAt_source]; exact hs)).symm
  -- the hypotheses of the converse
  have hsW_of : ∀ {s : ℝ}, s ∈ Ioo (t₀ - δ) (t₀ + δ) →
      s ∈ V ∩ γ ⁻¹' (chartAt H x₀).source :=
    fun {s} hs => ⟨(hδsub hs).2.2, (hδsub hs).2.1⟩
  have hderu : ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt u (deriv u s) s := by
    intro s hs
    have hsW : s ∈ V ∩ γ ⁻¹' (chartAt H x₀).source := hsW_of hs
    have hd : HasDerivWithinAt u (derivWithin u (V ∩ γ ⁻¹' (chartAt H x₀).source) s)
        (V ∩ γ ⁻¹' (chartAt H x₀).source) s :=
      (hu.differentiableOn (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0) s hsW).hasFDerivWithinAt
        |>.hasDerivWithinAt
    rw [derivWithin_of_isOpen hWopen hsW] at hd
    exact hd.hasDerivAt (hWopen.mem_nhds hsW)
  have hderv : ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt (deriv u) (deriv (deriv u) s) s := by
    intro s hs
    have hsW : s ∈ V ∩ γ ⁻¹' (chartAt H x₀).source := hsW_of hs
    have hd : HasDerivWithinAt (deriv u) (derivWithin (deriv u)
        (V ∩ γ ⁻¹' (chartAt H x₀).source) s)
        (V ∩ γ ⁻¹' (chartAt H x₀).source) s :=
      (hv.differentiableOn (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0) s hsW).hasFDerivWithinAt
        |>.hasDerivWithinAt
    rw [derivWithin_of_isOpen hWopen hsW] at hd
    exact hd.hasDerivAt (hWopen.mem_nhds hsW)
  have hstay : ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), u s ∈ (extChartAt I x₀).target := by
    intro s hs
    have hsW : s ∈ V ∩ γ ⁻¹' (chartAt H x₀).source := hsW_of hs
    have hsrc' : γ s ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hsW.2
    exact (extChartAt I x₀).map_source hsrc'
  have hleft_of : ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
      (extChartAt I x₀).symm (u s) = γ s := by
    intro s hs
    have hsrc' : γ s ∈ (extChartAt I x₀).source := by
      have h := (hδsub hs).2.1
      rwa [extChartAt_source]
    rw [hu_def]
    exact PartialEquiv.left_inv (extChartAt I x₀) hsrc'
  have hZeq : ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
      Z ((extChartAt I x₀).symm (u s))
        = curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) s := by
    intro s hs
    have hag : γ =ᶠ[𝓝 s] (fun r => (extChartAt I x₀).symm (u r)) :=
      Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hs)
        (fun r hr => (hleft_of r hr).symm)
    rw [hleft_of s hs, (hδsub hs).1]
    rw [← curveVelocity_congr_of_eventuallyEq (I := I) hag]
  have hgeo' : IsGeodesicAt (I := I) cov (fun s => (extChartAt I x₀).symm (u s)) t₀ :=
    (isGeodesicAt_congr_of_eventuallyEq (I := I) hagree).mp hgeo
  have hkey := Submission.Geodesic.chartGeodesicVectorField_eq_of_isGeodesicAt cov x₀
    (a := t₀ - δ) (b := t₀ + δ) ht₀I hderu hderv hstay Z hZ hZeq hgeo'
  -- conclude
  have hfinal : HasDerivAt (deriv u)
      (chartGeodesicVectorField cov x₀ (u t₀, deriv u t₀)) t₀ := by
    rw [← hkey]
    exact hderv t₀ ht₀I
  exact hfinal


end

end Submission.GeodesicExtend
