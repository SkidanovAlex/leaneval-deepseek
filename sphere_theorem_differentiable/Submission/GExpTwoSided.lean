import Submission.GExpGlob
import Submission.GExpRay2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Two-sided geodesy of the rays of `GExp`

`Submission.GlobalExp.GExp hmet x v` is defined as the endpoint of a chosen unit-speed geodesic
segment from `x` in the direction of `v`, and `isGeodesicAt_GExp_smul` shows that for **positive**
parameters `t > 0` the curve `s ↦ GExp x (s • v)` is a geodesic at `t`.  The same curve is, of
course, a geodesic for **negative** parameters as well (the ray extended backwards is still a
geodesic by uniqueness); this file records that fact.

## Contents

* `exists_pos_GExp_smul_eq_expMap`: `GExp x` and `expMap x` agree, on the ray of `v ≠ 0`, on a
  *two-sided* neighbourhood of `0` (the ball agreement of `exists_pos_GExp_eq_expMap` restricted to
  the ray);
* `mdifferentiableAt_GExp_smul`: the ray is smooth at every positive parameter;
* `isGeodesicAt_GExp_smul_of_neg`, `isGeodesicAt_GExp_smul_of_ne`: **two-sided geodesy**.

## Gotchas (see also `Submission/Roadmap.lean` §74)

* The tangent space `TangentSpace I x` is *definitionally* the model space `E`, but it carries its
  **own** `NormedAddCommGroup`/`NormedSpace` instances (from the Riemannian bundle), and those are
  *not* definitionally equal to the ambient ones.  As a consequence instance search for
  `ChartedSpace E (TangentSpace I x)` (needed by `HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)`, e.g. for the map
  `s ↦ s • v`) **fails**.  Lemmas about curves *into* the tangent space must therefore be stated in
  the native `TangentSpace`-valued form, and the velocity at `0` of the ray (which needs the chain
  rule with that map) needs a different, chart-based proof (see §74).

* The **fibre norm** `‖w‖` of `w : TangentSpace I x` is `√(chartGram x x w w)`, and
  `chartGram_self_apply` exhibits it as the *Riemannian* inner product of the (chart-coordinate)
  vector `w` *with itself*: it is **not** the model norm.  The two are comparable with the constants
  of `ChartBounds.exists_chartGram_bounds` and nothing more.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.ChartBounds
open Submission.GeodesicExtend

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpTwoSided

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## Two-sided agreement of `GExp` with `expMap` along a ray -/

/-- **Two-sided agreement along a ray.**  For `v ≠ 0` there is `ρ > 0` with
`GExp x (s • v) = expMap x (s • v)` for every `|s| < ρ`. -/
theorem exists_pos_GExp_smul_eq_expMap (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℝ, |s| < ρ →
      GExp (cov := cov) hmet x (s • v) = expMap cov x (s • v) := by
  obtain ⟨ρ₁, hρ₁, hag⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet x
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨ρ₁ / ‖v‖, by positivity, fun s hs => ?_⟩
  refine hag (s • v) ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact (lt_div_iff₀ hvpos).mp hs

/-! ## Smoothness and geodesy of the rays -/

/-- **The ray of `GExp` is smooth at every positive parameter.**  Near a positive time the ray is a
reparametrised `geodCurve`, hence smooth. -/
theorem mdifferentiableAt_GExp_smul (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) t := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hgd := geodDelta_pos (cov := cov) hmet
  set T : ℝ := max ‖v‖ ((t + 1) * ‖v‖) with hTdef
  have hTnn : 0 ≤ T := le_trans (norm_nonneg v) (le_max_left _ _)
  have hTle : (t + 1) * ‖v‖ ≤ T := by rw [hTdef]; exact le_max_right _ _
  set ξ : TangentSpace I x := unitOf v hv with hξdef
  have hξnorm : ‖ξ‖ = 1 := unitOf_norm v hv
  obtain ⟨-, -, hgcsm, -, -⟩ := geodCurve_spec (cov := cov) hmet T hTnn x ξ hξnorm
  have hnb : Ioo (t / 2) (t + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hev : (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) =ᶠ[𝓝 t]
      (fun s : ℝ => (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * s)) := by
    filter_upwards [hnb] with s hs
    have hs0 : 0 ≤ s := le_of_lt (by linarith [hs.1])
    have hsle : s * ‖v‖ ≤ T := by
      have h1 : s ≤ t + 1 := le_of_lt hs.2
      calc s * ‖v‖ ≤ (t + 1) * ‖v‖ := by nlinarith [hvpos]
        _ ≤ T := hTle
    rw [GExp_smul (cov := cov) hmet x hv hs0, mul_comm ‖v‖ s]
    exact geodCurve_agree (cov := cov) hmet (T₁ := max ‖v‖ (s * ‖v‖)) (T₂ := T)
      (le_trans (norm_nonneg v) (le_max_left _ _)) hTnn (max_le (le_max_left _ _) hsle) x ξ hξnorm
      ⟨by linarith [hgd, mul_nonneg hs0 (norm_nonneg v)],
       by linarith [hgd, le_max_right ‖v‖ (s * ‖v‖)]⟩
  have hmt : ‖v‖ * t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) :=
    ⟨by linarith [hgd, mul_pos hvpos ht],
     by nlinarith [hvpos, hTle, hgd, le_of_lt (lt_add_one t)]⟩
  have hsm : MDifferentiableAt 𝓘(ℝ) I (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * t) :=
    (hgcsm.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo hmt)).mdifferentiableAt (by simp)
  have hcomp : MDifferentiableAt 𝓘(ℝ) I
      (fun s : ℝ => (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * s)) t :=
    hsm.comp t (mdifferentiableAt_const.mul mdifferentiableAt_id)
  exact hcomp.congr_of_eventuallyEq hev

/-- **The rays of the global exponential map are geodesics at negative parameters too.**  For
`t < 0` the reversed ray in the direction `-v`, read backwards, is the ray in the direction `v`. -/
theorem isGeodesicAt_GExp_smul_of_neg (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) {t : ℝ} (ht : t < 0) :
    IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) t := by
  have hnv : -v ≠ 0 := neg_ne_zero.mpr hv
  have hpos : 0 < -t := by linarith
  have hgeo : IsGeodesicAt cov (fun u : ℝ => GExp (cov := cov) hmet x (u • (-v)))
      ((-1 : ℝ) * t) := by
    rw [neg_one_mul]
    exact isGeodesicAt_GExp_smul (cov := cov) hmet x hnv hpos
  have hmd : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ) I
      (fun u : ℝ => GExp (cov := cov) hmet x (u • (-v))) ((-1 : ℝ) * s) := by
    have hgood : ∀ᶠ u in 𝓝 ((-1 : ℝ) * t),
        MDifferentiableAt 𝓘(ℝ) I (fun u : ℝ => GExp (cov := cov) hmet x (u • (-v))) u := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (-1 : ℝ) * t ∈
        Ioo ((-1 : ℝ) * t / 2) ((-1 : ℝ) * t + 1) from ⟨by linarith, by linarith⟩)] with u hu
      exact mdifferentiableAt_GExp_smul (cov := cov) hmet x hnv (by linarith [hu.1])
    have hcont : Tendsto (fun s : ℝ => (-1 : ℝ) * s) (𝓝 t) (𝓝 ((-1 : ℝ) * t)) :=
      (continuous_const.mul continuous_id).continuousAt
    exact hcont.eventually hgood
  have hres := isGeodesicAt_comp_mul (cov := cov)
    (γ := fun u : ℝ => GExp (cov := cov) hmet x (u • (-v))) (c := -1) (t := t)
    (by norm_num) hmd hgeo
  refine (isGeodesicAt_congr_of_eventuallyEq (I := I) (Filter.Eventually.of_forall ?_)).mp hres
  intro s
  have harg : ((-1 : ℝ) * s) • (-v) = s • v := by
    rw [neg_one_mul, neg_smul, smul_neg, neg_neg]
  rw [harg]

/-- **Two-sided geodesy of the rays of the global exponential map.** -/
theorem isGeodesicAt_GExp_smul_of_ne (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) t := by
  rcases lt_trichotomy t 0 with h | h | h
  · exact isGeodesicAt_GExp_smul_of_neg (cov := cov) hmet x hv h
  · exact absurd h ht
  · exact isGeodesicAt_GExp_smul (cov := cov) hmet x hv h

end

end Submission.GExpTwoSided
