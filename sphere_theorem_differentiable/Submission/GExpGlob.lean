import Submission.GExpFlow
import Submission.HopfRinow2

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The global exponential map: ray continuation and the chart-flow step

`Submission.GlobalExp.GExp` is the *global* exponential map of the manifold: the endpoint at
Riemannian distance `‖v‖` of the geodesic through `p` in the direction of `v`.  It is defined
through an arbitrary choice of geodesic segment (`Classical.choose` of `geodCurve`), so its
*functorial* properties (continuity in the initial vector, ray continuation, ...) have to be
established from the uniqueness of geodesics, not from the definition.

`Submission.GExpFlow` provides the *local* model of `GExp` in a chart: a chart geodesic spray flow
`D.α` with joint smooth dependence on the initial phase, which agrees with `GExp` whenever the phase
`((extChartAt I z₀) q, flowScale D • u)` lies in the flow domain (`GExp_eq_chartFlow`).  Because that
model is stated in *coordinates*, its reach is a chart-dependent (but positive) amount of Riemannian
length.

This file starts the assembly of the *global* theory:

* `GExp_add_smul`: **ray continuation** — the semigroup property of the geodesic flow along a ray;
* `GExp_eq_chartFlow_ball`, `GExp_chartFlow_velocity`: the *one-step* description given by a chart
  flow box, for the endpoint and for the velocity of the ray at the endpoint (the state of the
  geodesic flow);
* `GExp_step_smul`, `GExp_step_velocity`: the same in the *Riemannian-length* form used by the
  induction along a long ray (the velocity of the geodesic at the endpoint of a step of prescribed
  Riemannian length).

The plan for the continuation (see `Submission/Roadmap.lean` §73) is to iterate
`GExp_add_smul` with these one-step descriptions along the states of a reference ray, using the
compactness of the ray to get finitely many boxes and a uniform positive step; this yields
continuity of `v ↦ GExp p v`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.GeodesicSpeed
open Submission.Length
open Submission.GExpFlow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpGlob

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## Ray continuation -/

/-- **Ray continuation (the semigroup property of the geodesic flow).**  Continuing the ray of a unit
vector `ξ` for Riemannian time `s` and then for Riemannian time `t` gives the point of the ray at
time `s + t`: the state of a geodesic at time `s + t` is determined by its state at time `s` (given
by the position `GExp p (s • ξ)` and the velocity of the ray there). -/
theorem GExp_add_smul (hmet : IsMetricCompatible cov) {p : M} {ξ : TangentSpace I p}
    (hξ : ‖ξ‖ = 1) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    GExp (cov := cov) hmet p ((s + t) • ξ)
      = GExp (cov := cov) hmet (GExp (cov := cov) hmet p (s • ξ))
          (t • curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (r • ξ)) s) := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · rw [← ht0, add_zero, zero_smul, GExp_zero]
  · have hT : 0 ≤ s + t := by linarith
    set Gp : ℝ → M := geodCurve (cov := cov) hmet (s + t) hT p ξ hξ with hGpdef
    have hray : ∀ r ∈ Icc (0:ℝ) (s + t), GExp (cov := cov) hmet p (r • ξ) = Gp r :=
      fun r hr => GExp_eq_geodCurve (cov := cov) hmet hξ hT hr.1 hr.2
    have hev : (fun r : ℝ => GExp (cov := cov) hmet p (r • ξ)) =ᶠ[𝓝 s] Gp := by
      filter_upwards [Ioo_mem_nhds hs (by linarith : s < s + t)] with r hr
      exact hray r ⟨hr.1.le, hr.2.le⟩
    have hvel : curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (r • ξ)) s
        = curveVelocity (I := I) Gp s := by
      rw [curveVelocity_apply, curveVelocity_apply, hev.mfderiv_eq (I := 𝓘(ℝ)) (I' := I)]
      rfl
    rw [hvel, hray s ⟨hs.le, by linarith⟩, hray (s + t) ⟨by linarith, le_rfl⟩]
    exact (GExp_geodCurve_add (cov := cov) hmet p hξ hT (t := s) (s := t) hs.le (by linarith) ht
      le_rfl).symm


/-! ## Local agreement with a geodesic through the base point -/

/-- **Local agreement of the global exponential map with a geodesic through the base point.**  If
`γ` is a geodesic on a neighbourhood of `0` with `γ 0 = p` and non-zero velocity `V` at `0`, then
`γ τ = GExp p (τ • V)` for `τ` in some right-neighbourhood of `0`.

(Equivalently: the ray of `GExp` is *the* geodesic with the prescribed initial data; the proof goes
through the unit-speed normalisation, where the library already has this statement for unit
velocities, and the uniqueness of geodesics with given initial data.) -/
theorem exists_pos_eq_GExp_of_isGeodesicAt (hmet : IsMetricCompatible cov)
    {p : M} {V : TangentSpace I p} (hV : V ≠ 0) {ε : ℝ} (hε : 0 < ε) {γ : ℝ → M}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo (-ε) ε))
    (hgeo : ∀ t ∈ Set.Ioo (-ε) ε, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Set.Ioo (-ε) ε, curveVelocity (I := I) γ t ≠ 0)
    (h0 : γ 0 = p) (hvel : curveVelocity (I := I) γ 0 = V) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ∀ τ : ℝ, 0 < τ → τ < ε' →
      γ τ = GExp (cov := cov) hmet p (τ • V) := by
  classical
  have hgd := geodDelta_pos (cov := cov) hmet
  have hcpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  set c : ℝ := ‖V‖ with hcdef
  have hcne : c ≠ 0 := ne_of_gt hcpos
  set ξ : TangentSpace I p := unitOf V hV with hξdef
  have hξ : ‖ξ‖ = 1 := unitOf_norm V hV
  have hcξ : c • ξ = V := by
    rw [hcdef, hξdef]
    show ‖V‖ • unitOf V hV = V
    rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hV), one_smul]
  -- a small radius, chosen so that `c * t` stays in the geodetic interval for `|t| < ε''`
  set ε'' : ℝ := min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) / 2
    with hε''def
  have hε''pos : 0 < ε'' := by
    rw [hε''def]
    have h1 : 0 < min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) :=
      lt_min (lt_min hε (by positivity)) (by positivity)
    linarith
  have hε''ltε : ε'' < ε := by
    rw [hε''def]
    have h2 : min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c))
        ≤ min ε (geodDelta (cov := cov) hmet / (2 * c)) := min_le_left _ _
    have h3 : min ε (geodDelta (cov := cov) hmet / (2 * c)) ≤ ε := min_le_left _ _
    linarith
  have hε''gd : ε'' * c < geodDelta (cov := cov) hmet := by
    rw [hε''def]
    have h2 : min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c))
        ≤ geodDelta (cov := cov) hmet / (2 * c) :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have h4 : min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) / 2 * c
        ≤ geodDelta (cov := cov) hmet / 4 := by
      have h5 : min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) * c
          ≤ geodDelta (cov := cov) hmet / 2 := by
        calc min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) * c
            ≤ (geodDelta (cov := cov) hmet / (2 * c)) * c :=
              mul_le_mul_of_nonneg_right h2 hcpos.le
          _ = geodDelta (cov := cov) hmet / 2 := by
              field_simp
      nlinarith [h5, hcpos]
    linarith [h4, hgd]
  have hε''c : ε'' * c < 1 := by
    rw [hε''def]
    have h2 : min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) ≤ 1 / (2 * c) :=
      min_le_right _ _
    have h4 : min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) / 2 * c ≤ 1 / 4 := by
      have h5 : min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) * c ≤ 1 / 2 := by
        calc min (min ε (geodDelta (cov := cov) hmet / (2 * c))) (1 / (2 * c)) * c
            ≤ (1 / (2 * c)) * c := mul_le_mul_of_nonneg_right h2 hcpos.le
          _ = 1 / 2 := by
              field_simp
      nlinarith [h5]
    linarith [h4]
  -- the unit-speed geodesic with the same initial direction
  set H : ℝ → M := geodCurve (cov := cov) hmet 1 (by norm_num : (0:ℝ) ≤ 1) p ξ hξ with hHdef
  obtain ⟨hH0, hHv, hHsm, hHgeo, hHsp⟩ := geodCurve_spec (cov := cov) hmet 1 (by norm_num) p ξ hξ
  have hmemH : ∀ t ∈ Set.Ioo (-ε'') ε'',
      c * t ∈ Set.Ioo (-(geodDelta (cov := cov) hmet)) (1 + geodDelta (cov := cov) hmet) := by
    intro t ht
    refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
    · have h1 : -ε'' * c < c * t := by nlinarith [ht.1, hcpos]
      nlinarith [hgd, h1, hε''gd]
    · have h2 : c * t < 1 := by nlinarith [ht.2, hcpos, hε''c]
      linarith
  have hHmd : ∀ t ∈ Set.Ioo (-ε'') ε'', MDifferentiableAt 𝓘(ℝ) I H (c * t) :=
    fun t ht => (hHsm.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo (hmemH t ht))).mdifferentiableAt
      (by simp)
  have hσsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => H (c * t)) (Set.Ioo (-ε'') ε'') := by
    have h1 : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => c * t) (Set.Ioo (-ε'') ε'') :=
      (contMDiff_const.mul contMDiff_id).contMDiffOn
    exact hHsm.comp h1 (fun t ht => hmemH t ht)
  have hσgeo : ∀ t ∈ Set.Ioo (-ε'') ε'', IsGeodesicAt cov (fun t : ℝ => H (c * t)) t := by
    intro t ht
    refine isGeodesicAt_comp_mul (cov := cov) (γ := H) (c := c) (t := t) hcne ?_
      (hHgeo (c * t) (hmemH t ht))
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun s hs => hHmd s hs)
  have hσne : ∀ t ∈ Set.Ioo (-ε'') ε'',
      curveVelocity (I := I) (fun t : ℝ => H (c * t)) t ≠ 0 := by
    intro t ht hzero
    have hvelc : curveVelocity (I := I) (fun s : ℝ => H (c * s)) t
        = c • curveVelocity (I := I) H (c * t) := by
      have h := curveVelocity_comp_mul_add (I := I) (γ := H) (c := c) (d := 0) (t := t)
        (by simpa using hHmd t ht)
      have hfun : (fun s : ℝ => H (c * s + 0)) = (fun s : ℝ => H (c * s)) := by
        funext s; rw [add_zero]
      rw [hfun, add_zero] at h
      exact h
    rw [hvelc] at hzero
    have h2 : curveVelocity (I := I) H (c * t) = 0 := (smul_eq_zero.mp hzero).resolve_left hcne
    have h3 := hHsp (c * t) (hmemH t ht)
    rw [h2, norm_zero] at h3
    norm_num at h3
  -- (i) `γ` and the rescaled `H` agree near `0`
  have hEqOn : EqOn γ (fun t : ℝ => H (c * t)) (Set.Ioo (-ε'') ε'') := by
    have hvel0 : curveVelocity (I := I) (fun s : ℝ => H (c * s)) 0 = V := by
      have h := curveVelocity_comp_mul_add (I := I) (γ := H) (c := c) (d := 0) (t := 0)
        (by simpa using hHmd 0 (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩))
      have hfun : (fun s : ℝ => H (c * s + 0)) = (fun s : ℝ => H (c * s)) := by
        funext s; rw [add_zero]
      rw [hfun, mul_zero, add_zero, hHv] at h
      rw [h, hcξ]
    refine eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov)
      (hsm.mono (fun t ht => ⟨by linarith [ht.1, hε''ltε], by linarith [ht.2, hε''ltε]⟩)) hσsm
      (fun t ht => hgeo t ⟨by linarith [ht.1, hε''ltε], by linarith [ht.2, hε''ltε]⟩) hσgeo
      (fun t ht => hne t ⟨by linarith [ht.1, hε''ltε], by linarith [ht.2, hε''ltε]⟩) hσne
      (t₀ := 0) (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
      (by simp only [h0, mul_zero, hHdef, hH0]) ?_
    rw [hvel]
    exact hvel0.symm
  -- (ii) the ray of `GExp` is the same geodesic
  refine ⟨ε'', hε''pos, hε''ltε.le, fun τ hτ hτ' => ?_⟩
  have hτne : τ • V ≠ 0 := smul_ne_zero (ne_of_gt hτ) hV
  have hnormτ : ‖τ • V‖ = τ * c := by
    rw [norm_smul, Real.norm_of_nonneg hτ.le, hcdef]
  have hunit : unitOf (τ • V) hτne = ξ := by
    have hτne0 : τ ≠ 0 := ne_of_gt hτ
    rw [hξdef, unitOf, unitOf, hnormτ]
    show (τ * c)⁻¹ • (τ • V) = c⁻¹ • V
    rw [smul_smul]
    congr 1
    field_simp
  have h1 : GExp (cov := cov) hmet p (τ • V)
      = (geodCurve (cov := cov) hmet ‖τ • V‖ (norm_nonneg _) p (unitOf (τ • V) hτne)
          (unitOf_norm (τ • V) hτne)) ‖τ • V‖ :=
    GExp_apply (cov := cov) hmet hτne
  have h2 : (geodCurve (cov := cov) hmet ‖τ • V‖ (norm_nonneg _) p (unitOf (τ • V) hτne)
        (unitOf_norm (τ • V) hτne)) ‖τ • V‖ = H (τ * c) := by
    have hτc : τ * c < 1 := by nlinarith [hτ', hcpos, hε''c]
    have hmemp : ‖τ • V‖ ∈ Set.Ioo (-(geodDelta (cov := cov) hmet))
        (‖τ • V‖ + geodDelta (cov := cov) hmet) :=
      Set.mem_Ioo.mpr ⟨by rw [hnormτ]; nlinarith [hgd, mul_nonneg hτ.le hcpos.le],
        by linarith [hgd]⟩
    have hstep : (geodCurve (cov := cov) hmet ‖τ • V‖ (norm_nonneg _) p (unitOf (τ • V) hτne)
        (unitOf_norm (τ • V) hτne)) ‖τ • V‖
        = (geodCurve (cov := cov) hmet 1 (by norm_num : (0:ℝ) ≤ 1) p ξ hξ) ‖τ • V‖ :=
      geodCurve_agree_of_eq (cov := cov) hmet (x := p) hunit
        (unitOf_norm (τ • V) hτne) hξ (T₁ := ‖τ • V‖) (T₂ := 1) (norm_nonneg _) (by norm_num)
        (le_of_lt (by rw [hnormτ]; exact hτc)) hmemp
    rw [hstep, hHdef, hnormτ]
  rw [h1, h2, hEqOn (Set.mem_Ioo.mpr ⟨by linarith, hτ'⟩)]
  show H (c * τ) = H (τ * c)
  rw [mul_comm]

end

end Submission.GExpGlob
