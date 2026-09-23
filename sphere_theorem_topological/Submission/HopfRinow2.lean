import Submission.HopfRinow
import Submission.CornerCut
import Submission.Commons.Geometry.Manifold.riemannianEDist_min_on_sphere_enormSMul

/-!
# Hopf–Rinow: ray continuation and the existence of minimising geodesics

## Contents

* `pathELength_of_unit_speed`: the Riemannian length of a curve of unit speed on `[a,b]` is
  `b - a`;
* `GExp_eq_geodCurve`: the ray `s ↦ GExp x (s • u)` of the *global* exponential map agrees with a
  single chosen geodesic segment `geodCurve` on `[0,T]`;
* `isGeodesicAt_comp_affine`, `isGeodesicAt_comp_sub_neg_at`, `curveVelocity_comp_sub_neg_at`:
  affine reparametrisation of the geodesic equation (with arbitrary centre), and the velocity of a
  time-reflected curve;
* `GExp_neg_smul_curveVelocity_geodCurve`: **backward ray continuation** — the geodesic ray through
  a point of `geodCurve` in the direction of the velocity is the backward extension of `geodCurve`;
* `GExp_geodCurve_add`: **forward ray continuation**;
* `riemannianEDist_GExp_ray_le`: the distance between two points of a ray is at most the difference
  of the parameters;
* **`exists_geodesic_riemannianEDist_eq`**: **Hopf–Rinow** — on a compact connected Riemannian
  manifold every two points are joined by a minimising geodesic: there is `v ∈ T_pM` with
  `GExp p v = q` and `d(p,q) = ‖v‖`.

## Proof sketch of Hopf–Rinow

The proof is the classical recursion.  Fix a uniform radius `ρ > 0` such that the metric ball of
radius `ρ` around any point is covered by the exponential map with the right norms
(`exists_eq_expMap_of_riemannianEDist_lt`, `exists_pos_GExp_eq_expMap`); the *uniformity* is not
needed: the argument below uses the local theory only at a single point.

If `d(p,q) < ofReal ρ` we are done.  Otherwise put `L := (d(p,q)).toReal ≥ ρ/2`.  Choose `y₁` on
the sphere of radius `ρ/2` around `p` minimising `d(·,q)`
(`Commons.Geometry.Manifold.riemannianEDist_min_on_sphere_enormSMul`); then
`d(p,y₁) = ρ/2` and `d(y₁,q) = L - ρ/2`.  Writing `y₁ = GExp p ((ρ/2) • u)` with `u` a unit
vector, consider

  `S := {t ∈ [0,L] : d(p, α t) = t  ∧  d(α t, q) = L - t}`,  `α t := GExp p (t • u)`.

`S` contains `0` and `ρ/2`, and is closed (continuity of the distance).  It is also *right open*: for
`t ∈ S`, `0 < t < L` one takes a point `y'` minimising `d(·,q)` on a small sphere of radius `r`
around `α t`, notes that `y' = GExp (α t) (r • η)` for a unit `η` with `r < ρ`, and uses the corner
cut (`Submission.CornerCut.corner_cut`): if `η` differed from the direction `α'(t) = Gp'(t)` of the
ray, then the broken path `p → α(t-τ) → GExp (α t) (τ η) → y' → q` would be strictly shorter than
`L`, contradicting `d(p,q) = L`.  Here `α(t-τ)` is the backward continuation of the ray and
`d(GExp (α t)(τ η), y') ≤ r - τ` comes from the length of a ray arc.
Hence `sSup S = L`, so `L ∈ S` and `d(α L, q) = 0`, i.e. `α L = q`; `v := L • u` is the required
tangent vector.

This file completes the Hopf–Rinow theorem:

* `pathELength_of_unit_speed`: the Riemannian length of a curve of unit speed on `[a,b]` is `b - a`;
* `GExp_eq_geodCurve`: the ray `s ↦ GExp x (s • u)` of the *global* exponential map agrees with a
  single chosen geodesic segment `geodCurve` on `[0,T]`;
* `GExp_neg_smul_curveVelocity_geodCurve`: **backward ray continuation** — the geodesic ray through a
  point of `geodCurve` in the direction of the velocity is the backward extension of `geodCurve`;
* `riemannianEDist_GExp_ray_le`: the distance between two points of a ray is at most the difference
  of the parameters;
* **`exists_geodesic_riemannianEDist_eq`**: every two points of a compact connected Riemannian
  manifold are joined by a minimising geodesic.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.GeodesicSpeed
open Submission.Length
open Submission.Minimal
open Submission.Gauss
open Submission.GlobalExp
open Submission.GeodesicGlobal2
open Submission.Distance
open Submission.CornerCut

namespace Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-! ## The length of a unit-speed curve -/

/-- **The length of a curve of unit speed.**  If `‖γ'‖ = 1` on `[a,b]`, the Riemannian length of
`γ` on `[a,b]` is `b - a`. -/
theorem pathELength_of_unit_speed {γ : ℝ → M} {a b : ℝ}
    (h : ∀ t ∈ Icc a b, ‖curveVelocity (I := I) γ t‖ = 1) :
    Manifold.pathELength I γ a b = ENNReal.ofReal (b - a) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hcongr : (∫⁻ t in Icc a b, ‖(mfderiv% γ t) 1‖ₑ)
      = ∫⁻ _ in Icc a b, (1 : ℝ≥0∞) := by
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    change ‖curveVelocity (I := I) γ t‖ₑ = 1
    rw [enorm_eq_ofReal_norm, h t ht, ENNReal.ofReal_one]
  rw [hcongr, MeasureTheory.setLIntegral_const, Real.volume_Icc, one_mul]


section Ray

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]

/-! ## The ray of the global exponential map is a single chosen geodesic -/

/-- **The ray of `GExp` is a single chosen geodesic.**  For a unit vector `u` and `0 ≤ r ≤ T`, the
ray of the global exponential map agrees with the chosen geodesic segment of length `T`. -/
theorem GExp_eq_geodCurve (hmet : IsMetricCompatible cov)
    {x : M} {u : TangentSpace I x} (hu : ‖u‖ = 1) {T : ℝ} (hT : 0 ≤ T)
    {r : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ T) :
    GExp (cov := cov) hmet x (r • u) = (geodCurve (cov := cov) hmet T hT x u hu) r := by
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · subst h0
    rw [zero_smul, GExp_zero]
    exact ((geodCurve_spec (cov := cov) hmet T hT x u hu).1).symm
  · have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu; norm_num at hu
    have hξ₁ : ‖unitOf u hu0‖ = 1 := unitOf_norm u hu0
    have heq : unitOf u hu0 = u := by rw [unitOf, hu, inv_one, one_smul]
    have hmaxnn : 0 ≤ max ‖u‖ (r * ‖u‖) := le_trans (norm_nonneg u) (le_max_left _ _)
    have harith : r * ‖u‖ = r := by rw [hu, mul_one]
    have hge : r ≤ max ‖u‖ (r * ‖u‖) := by
      rw [harith]; exact le_max_right ‖u‖ r
    have hstep := GExp_smul (cov := cov) hmet x hu0 (le_of_lt hpos)
    have hval : (geodCurve (cov := cov) hmet (max ‖u‖ (r * ‖u‖))
          (le_trans (norm_nonneg u) (le_max_left _ _)) x (unitOf u hu0) hξ₁) (r * ‖u‖)
        = (geodCurve (cov := cov) hmet (max ‖u‖ (r * ‖u‖))
          (le_trans (norm_nonneg u) (le_max_left _ _)) x (unitOf u hu0) hξ₁) r :=
      congrArg (fun s : ℝ => (geodCurve (cov := cov) hmet (max ‖u‖ (r * ‖u‖))
          (le_trans (norm_nonneg u) (le_max_left _ _)) x (unitOf u hu0) hξ₁) s) harith
    rw [hstep, hval]
    rcases le_total (max ‖u‖ (r * ‖u‖)) T with hle | hle
    · exact geodCurve_agree_of_eq (cov := cov) hmet heq hξ₁ hu hmaxnn hT hle
        (Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet],
          by linarith [geodDelta_pos (cov := cov) hmet, hge]⟩)
    · have hmem : r ∈ Ioo (-(geodDelta (cov := cov) hmet))
          (T + geodDelta (cov := cov) hmet) :=
        Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet],
          by linarith [geodDelta_pos (cov := cov) hmet, hrT]⟩
      exact (geodCurve_agree_of_eq (cov := cov) hmet heq.symm hu hξ₁ hT hmaxnn hle hmem).symm


/-! ## Time reflection of geodesics -/

/-- The composition with a translation on the left. -/
lemma mdifferentiableAt_comp_add {σ : ℝ → M} {y b : ℝ}
    (h : MDifferentiableAt 𝓘(ℝ) I σ (y + b)) :
    MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ => σ (s + b)) y := by
  have h2 : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => s + b) y :=
    (mdifferentiableAt_id (I := 𝓘(ℝ))).add mdifferentiableAt_const
  simpa [Function.comp_def] using h.comp y h2

/-- Time reflection of a smooth curve. -/
lemma contMDiffOn_comp_sub_neg {γ : ℝ → M} {c d t : ℝ} {u : Set ℝ}
    (h : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo c d)) (hu : ∀ r ∈ u, t - r ∈ Ioo c d) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun r : ℝ => γ (t - r)) u :=
  h.comp (contDiff_const.sub contDiff_id).contMDiff.contMDiffOn hu

/-- **Affine reparametrisation preserves the geodesic equation.**  If `σ` is a `C^∞` geodesic on
`Ioo c d`, `a ≠ 0` and `a * r + b ∈ Ioo c d`, then `s ↦ σ (a * s + b)` is a geodesic at `r`. -/
lemma isGeodesicAt_comp_affine {σ : ℝ → M} {c d a b : ℝ} (ha : a ≠ 0)
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ σ (Ioo c d))
    (hgeo : ∀ y ∈ Ioo c d, IsGeodesicAt cov σ y) {r : ℝ} (hr : a * r + b ∈ Ioo c d) :
    IsGeodesicAt cov (fun s : ℝ => σ (a * s + b)) r := by
  have hmd0 : ∀ᶠ y in 𝓝 (a * r + b), MDifferentiableAt 𝓘(ℝ) I σ y := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with y hy
    exact (hsm.contMDiffAt (isOpen_Ioo.mem_nhds hy)).mdifferentiableAt (by simp)
  have hτgeo : IsGeodesicAt cov (fun y : ℝ => σ (y + b)) (a * r) := by
    have h := isGeodesicAt_comp_sub (cov := cov) (σ := σ) (t := a * r + b) (T := -b) hmd0
      (hgeo (a * r + b) hr)
    simpa [sub_neg_eq_add] using h
  have hnb : {s : ℝ | a * s + b ∈ Ioo c d} ∈ 𝓝 r := by
    have hcont : Continuous (fun s : ℝ => a * s + b) :=
      (continuous_const.mul continuous_id).add continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hr)
  have hmdτ : ∀ᶠ s in 𝓝 r, MDifferentiableAt 𝓘(ℝ) I (fun y : ℝ => σ (y + b)) (a * s) := by
    filter_upwards [hnb] with s hs
    exact mdifferentiableAt_comp_add (I := I) (h := (hsm.contMDiffAt
      (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt (by simp))
  exact isGeodesicAt_comp_mul (cov := cov) (γ := fun y : ℝ => σ (y + b)) (c := a) (t := r)
    ha hmdτ hτgeo

/-- **Time reflection at an arbitrary centre.**  If `γ` is a `C^∞` geodesic on `Ioo c d`, then
`r ↦ γ (t - r)` is a geodesic at every `r` with `t - r ∈ Ioo c d`. -/
lemma isGeodesicAt_comp_sub_neg_at {γ : ℝ → M} {c d t : ℝ}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo c d))
    (hgeo : ∀ y ∈ Ioo c d, IsGeodesicAt cov γ y) {r : ℝ} (hr : t - r ∈ Ioo c d) :
    IsGeodesicAt cov (fun s : ℝ => γ (t - s)) r := by
  have h := isGeodesicAt_comp_affine (cov := cov) (σ := γ) (a := -1) (b := t) (by norm_num)
    hsm hgeo (r := r) (by rwa [show (-1 : ℝ) * r + t = t - r from by ring])
  rwa [show (fun s : ℝ => γ ((-1 : ℝ) * s + t)) = (fun s : ℝ => γ (t - s)) from by
    funext u; rw [neg_one_mul, sub_eq_add_neg, add_comm]] at h

/-- The velocity of a time-reflected curve. -/
lemma curveVelocity_comp_sub_neg_at {γ : ℝ → M} {t r : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (t - r)) :
    curveVelocity (I := I) (fun s : ℝ => γ (t - s)) r = -curveVelocity (I := I) γ (t - r) := by
  have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := -1) (d := t)
    (t := r) (by rwa [show (-1 : ℝ) * r + t = t - r from by ring])
  rw [show (fun s : ℝ => γ ((-1 : ℝ) * s + t)) = (fun s : ℝ => γ (t - s)) from by
    funext u; rw [neg_one_mul, sub_eq_add_neg, add_comm]] at h
  rw [show (-1 : ℝ) * r + t = t - r from by ring] at h
  simpa using h

/-- **Backward Ray continuation.**  Let `Gp` be the chosen unit-speed geodesic segment of length
`T` starting at `x` with initial unit velocity `ξ`.  Then for `0 ≤ s ≤ t ≤ T`, the ray of the
global exponential map starting at `Gp t` in the direction `-Gp'(t)` runs back along `Gp`. -/
theorem GExp_neg_smul_curveVelocity_geodCurve
    (hmet : IsMetricCompatible cov) (x : M) {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1)
    {T : ℝ} (hT : 0 ≤ T) {t s : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hs0 : 0 ≤ s) (hst : s ≤ t) :
    GExp (cov := cov) hmet ((geodCurve (cov := cov) hmet T hT x ξ hξ) t)
        ((-s) • curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t)
      = (geodCurve (cov := cov) hmet T hT x ξ hξ) (t - s) := by
  classical
  have hδ := geodDelta_pos (cov := cov) hmet
  set Gp : ℝ → M := geodCurve (cov := cov) hmet T hT x ξ hξ with hGpdef
  have hspec := geodCurve_spec (cov := cov) hmet T hT x ξ hξ
  have hGpsm : ContMDiffOn 𝓘(ℝ) I ∞ Gp
      (Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet)) := by
    rw [hGpdef]; exact hspec.2.2.1
  have hGpgeo : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet), IsGeodesicAt cov Gp r := by
    intro r hr; rw [hGpdef]; exact hspec.2.2.2.1 r hr
  have hGpsp : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet), ‖curveVelocity (I := I) Gp r‖ = 1 := by
    intro r hr; rw [hGpdef]; exact hspec.2.2.2.2 r hr
  have htIoo : t ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hGpmd : MDifferentiableAt 𝓘(ℝ) I Gp t :=
    (hGpsm.contMDiffAt (isOpen_Ioo.mem_nhds htIoo)).mdifferentiableAt (by simp)
  set w : TangentSpace I (Gp t) := curveVelocity (I := I) Gp t with hwdef
  have hw1 : ‖w‖ = 1 := hGpsp t htIoo
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · subst hs_eq
    rw [neg_zero, zero_smul, GExp_zero, sub_zero]
  · have hsvne : (-s) • w ≠ 0 := by
      refine smul_ne_zero (by linarith) ?_
      intro h0; rw [h0, norm_zero] at hw1; norm_num at hw1
    have hvnorm : ‖(-s) • w‖ = s := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs_pos, hw1, mul_one]
    have hunit : unitOf ((-s) • w) hsvne = -w := by
      rw [unitOf, hvnorm, smul_smul, show s⁻¹ * -s = -1 from by field_simp]
      simp
    -- the geodesic starting at `Gp t` in the direction `-w`
    set Gz : ℝ → M := geodCurve (cov := cov) hmet s hs0 (Gp t) (unitOf ((-s) • w) hsvne)
      (unitOf_norm ((-s) • w) hsvne) with hGzdef
    have hGzspec := geodCurve_spec (cov := cov) hmet s hs0 (Gp t) (unitOf ((-s) • w) hsvne)
      (unitOf_norm ((-s) • w) hsvne)
    have hGzsm : ContMDiffOn 𝓘(ℝ) I ∞ Gz
        (Ioo (-(geodDelta (cov := cov) hmet)) (s + geodDelta (cov := cov) hmet)) := by
      rw [hGzdef]; exact hGzspec.2.2.1
    have hGzgeo : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (s + geodDelta (cov := cov) hmet), IsGeodesicAt cov Gz r := by
      intro r hr; rw [hGzdef]; exact hGzspec.2.2.2.1 r hr
    have hGzsp : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (s + geodDelta (cov := cov) hmet), ‖curveVelocity (I := I) Gz r‖ = 1 := by
      intro r hr; rw [hGzdef]; exact hGzspec.2.2.2.2 r hr
    have hGz0 : Gz 0 = Gp t := by rw [hGzdef]; exact hGzspec.1
    have hGzv : curveVelocity (I := I) Gz 0 = -w := by
      rw [hGzdef]
      exact hGzspec.2.1.trans hunit
    -- the reflected curve `K r = Gp (t - r)`
    have hKv : curveVelocity (I := I) (fun r : ℝ => Gp (t - r)) 0 = -w := by
      have h := curveVelocity_comp_sub_neg_at (I := I) (γ := Gp) (t := t) (r := 0) (by
        rw [sub_zero]; exact hGpmd)
      rw [show t - 0 = t from by ring] at h
      rw [hwdef]; exact h
    -- the comparison interval
    set a : ℝ := max (-(geodDelta (cov := cov) hmet)) (t - (T + geodDelta (cov := cov) hmet))
      with hadef
    set b : ℝ := min (s + geodDelta (cov := cov) hmet) (t + geodDelta (cov := cov) hmet)
      with hbdef
    have ha0 : a < 0 := by
      rw [hadef]; exact max_lt (by linarith) (by linarith)
    have h0b : 0 < b := by
      rw [hbdef]; exact lt_min (by linarith) (by linarith)
    have has : a < s := by
      rw [hadef]; refine max_lt (by linarith) ?_; linarith
    have hsb : s < b := by
      rw [hbdef]; exact lt_min (by linarith) (by linarith)
    have hab1 : Ioo a b ⊆ Ioo (-(geodDelta (cov := cov) hmet))
        (s + geodDelta (cov := cov) hmet) := by
      intro r hr
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
    have hab2 : ∀ r ∈ Ioo a b, t - r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (T + geodDelta (cov := cov) hmet) := by
      intro r hr
      have h1 : t - (T + geodDelta (cov := cov) hmet) < r :=
        lt_of_le_of_lt (le_max_right _ _) hr.1
      have h2 : r < t + geodDelta (cov := cov) hmet := lt_of_lt_of_le hr.2 (min_le_right _ _)
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hKsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun r : ℝ => Gp (t - r)) (Ioo a b) :=
      contMDiffOn_comp_sub_neg (I := I) hGpsm hab2
    have hKgeo : ∀ r ∈ Ioo a b, IsGeodesicAt cov (fun r : ℝ => Gp (t - r)) r := by
      intro r hr
      exact isGeodesicAt_comp_sub_neg_at (cov := cov) hGpsm hGpgeo (hab2 r hr)
    have hKne : ∀ r ∈ Ioo a b, curveVelocity (I := I) (fun r : ℝ => Gp (t - r)) r ≠ 0 := by
      intro r hr h0
      have hmd : MDifferentiableAt 𝓘(ℝ) I Gp (t - r) :=
        (hGpsm.contMDiffAt (isOpen_Ioo.mem_nhds (hab2 r hr))).mdifferentiableAt (by simp)
      have hv := curveVelocity_comp_sub_neg_at (I := I) (γ := Gp) (t := t) (r := r) hmd
      have hsp := hGpsp (t - r) (hab2 r hr)
      rw [hv] at h0
      rw [neg_eq_zero] at h0
      rw [h0] at hsp
      norm_num at hsp
    have hGzne : ∀ r ∈ Ioo a b, curveVelocity (I := I) Gz r ≠ 0 := by
      intro r hr h0
      have hsp := hGzsp r (hab1 hr)
      rw [h0, norm_zero] at hsp
      norm_num at hsp
    have hEqOn : EqOn Gz (fun r : ℝ => Gp (t - r)) (Ioo a b) :=
      eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := a) (b := b)
        (hGzsm.mono hab1) hKsm
        (fun r hr => hGzgeo r (hab1 hr)) hKgeo
        (fun r hr => hGzne r hr) hKne
        (t₀ := 0) (Set.mem_Ioo.mpr ⟨ha0, h0b⟩)
        (by rw [hGz0]; exact congrArg Gp (show t = t - 0 from by ring)) (by rw [hGzv, hKv])
    -- conclusion
    have hGs : GExp (cov := cov) hmet (Gp t) ((-s) • w) = Gz s := by
      have h := GExp_eq_geodCurve (cov := cov) hmet (x := Gp t) (u := unitOf ((-s) • w) hsvne)
        (unitOf_norm ((-s) • w) hsvne) (T := s) hs0 hs0 le_rfl
      rwa [show s • unitOf ((-s) • w) hsvne = (-s) • w from by rw [hunit, smul_neg, neg_smul]] at h
    rw [hGs, hEqOn (Set.mem_Ioo.mpr ⟨has, hsb⟩)]

/-- **Forward ray continuation.**  Let `Gp` be the chosen unit-speed geodesic segment of length `T`
starting at `x` with initial unit velocity `ξ`.  Then for `0 ≤ t ≤ T` and `0 ≤ s` with
`t + s ≤ T`, the ray of the global exponential map starting at `Gp t` in the direction `Gp'(t)`
runs forward along `Gp`. -/
theorem GExp_geodCurve_add
    (hmet : IsMetricCompatible cov) (x : M) {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1)
    {T : ℝ} (hT : 0 ≤ T) {t s : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hs0 : 0 ≤ s) (hts : t + s ≤ T) :
    GExp (cov := cov) hmet ((geodCurve (cov := cov) hmet T hT x ξ hξ) t)
        (s • curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t)
      = (geodCurve (cov := cov) hmet T hT x ξ hξ) (t + s) := by
  classical
  have hδ := geodDelta_pos (cov := cov) hmet
  set Gp : ℝ → M := geodCurve (cov := cov) hmet T hT x ξ hξ with hGpdef
  have hspec := geodCurve_spec (cov := cov) hmet T hT x ξ hξ
  have hGpsm : ContMDiffOn 𝓘(ℝ) I ∞ Gp
      (Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet)) := by
    rw [hGpdef]; exact hspec.2.2.1
  have hGpgeo : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet), IsGeodesicAt cov Gp r := by
    intro r hr; rw [hGpdef]; exact hspec.2.2.2.1 r hr
  have hGpsp : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet), ‖curveVelocity (I := I) Gp r‖ = 1 := by
    intro r hr; rw [hGpdef]; exact hspec.2.2.2.2 r hr
  have htIoo : t ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  set w : TangentSpace I (Gp t) := curveVelocity (I := I) Gp t with hwdef
  have hw1 : ‖w‖ = 1 := hGpsp t htIoo
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · subst hs_eq
    rw [zero_smul, GExp_zero, add_zero]
  · have hsvne : s • w ≠ 0 := by
      refine smul_ne_zero (ne_of_gt hs_pos) ?_
      intro h0; rw [h0, norm_zero] at hw1; norm_num at hw1
    have hvnorm : ‖s • w‖ = s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hw1, mul_one]
    have hunit : unitOf (s • w) hsvne = w := by
      rw [unitOf, hvnorm, smul_smul, show s⁻¹ * s = 1 from by field_simp]
      simp
    set Gz : ℝ → M := geodCurve (cov := cov) hmet s hs0 (Gp t) (unitOf (s • w) hsvne)
      (unitOf_norm (s • w) hsvne) with hGzdef
    have hGzspec := geodCurve_spec (cov := cov) hmet s hs0 (Gp t) (unitOf (s • w) hsvne)
      (unitOf_norm (s • w) hsvne)
    have hGzsm : ContMDiffOn 𝓘(ℝ) I ∞ Gz
        (Ioo (-(geodDelta (cov := cov) hmet)) (s + geodDelta (cov := cov) hmet)) := by
      rw [hGzdef]; exact hGzspec.2.2.1
    have hGzgeo : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (s + geodDelta (cov := cov) hmet), IsGeodesicAt cov Gz r := by
      intro r hr; rw [hGzdef]; exact hGzspec.2.2.2.1 r hr
    have hGzsp : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (s + geodDelta (cov := cov) hmet), ‖curveVelocity (I := I) Gz r‖ = 1 := by
      intro r hr; rw [hGzdef]; exact hGzspec.2.2.2.2 r hr
    have hGz0 : Gz 0 = Gp t := by rw [hGzdef]; exact hGzspec.1
    have hGzv : curveVelocity (I := I) Gz 0 = w := by
      rw [hGzdef]
      exact hGzspec.2.1.trans hunit
    have hGpmd : MDifferentiableAt 𝓘(ℝ) I Gp t :=
      (hGpsm.contMDiffAt (isOpen_Ioo.mem_nhds htIoo)).mdifferentiableAt (by simp)
    have hKv : curveVelocity (I := I) (fun r : ℝ => Gp (t + r)) 0 = w := by
      have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := Gp) (c := 1) (d := t)
        (t := 0) (by rw [one_mul, zero_add]; exact hGpmd)
      rw [one_smul, show (fun s : ℝ => Gp (1 * s + t)) = (fun r : ℝ => Gp (t + r)) from by
        funext u; rw [one_mul, add_comm], show (1 : ℝ) * 0 + t = t from by ring] at h
      rw [hwdef]; exact h
    set a : ℝ := max (-(geodDelta (cov := cov) hmet))
      (-(geodDelta (cov := cov) hmet) - t) with hadef
    set b : ℝ := min (s + geodDelta (cov := cov) hmet)
      (T + geodDelta (cov := cov) hmet - t) with hbdef
    have ha0 : a < 0 := by
      rw [hadef]; exact max_lt (by linarith) (by linarith)
    have h0b : 0 < b := by
      rw [hbdef]; exact lt_min (by linarith) (by linarith)
    have has : a < s := by
      rw [hadef]; refine max_lt (by linarith) ?_; linarith
    have hsb : s < b := by
      rw [hbdef]; exact lt_min (by linarith) (by linarith)
    have hab1 : Ioo a b ⊆ Ioo (-(geodDelta (cov := cov) hmet))
        (s + geodDelta (cov := cov) hmet) := by
      intro r hr
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
    have hab2 : ∀ r ∈ Ioo a b, t + r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (T + geodDelta (cov := cov) hmet) := by
      intro r hr
      have h1 : -(geodDelta (cov := cov) hmet) - t < r :=
        lt_of_le_of_lt (le_max_right _ _) hr.1
      have h2 : r < T + geodDelta (cov := cov) hmet - t :=
        lt_of_lt_of_le hr.2 (min_le_right _ _)
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hKsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun r : ℝ => Gp (t + r)) (Ioo a b) := by
      refine hGpsm.comp ?_ hab2
      exact (contDiff_const.add contDiff_id).contMDiff.contMDiffOn
    have hKgeo : ∀ r ∈ Ioo a b, IsGeodesicAt cov (fun r : ℝ => Gp (t + r)) r := by
      intro r hr
      have h := isGeodesicAt_comp_affine (cov := cov) (σ := Gp) (a := 1) (b := t) (by norm_num)
        hGpsm hGpgeo (r := r) (by rw [show (1:ℝ) * r + t = t + r from by ring]; exact hab2 r hr)
      rwa [show (fun s : ℝ => Gp (1 * s + t)) = (fun r : ℝ => Gp (t + r)) from by
        funext u; rw [show (1:ℝ) * u + t = t + u from by ring]] at h
    have hKne : ∀ r ∈ Ioo a b, curveVelocity (I := I) (fun r : ℝ => Gp (t + r)) r ≠ 0 := by
      intro r hr
      have hmd : MDifferentiableAt 𝓘(ℝ) I Gp (t + r) :=
        (hGpsm.contMDiffAt (isOpen_Ioo.mem_nhds (hab2 r hr))).mdifferentiableAt (by simp)
      have hv : curveVelocity (I := I) (fun r : ℝ => Gp (t + r)) r
          = curveVelocity (I := I) Gp (t + r) := by
        have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := Gp) (c := 1) (d := t)
          (t := r) (by rw [one_mul, add_comm]; exact hmd)
        rw [one_smul, show (fun s : ℝ => Gp (1 * s + t)) = (fun r : ℝ => Gp (t + r)) from by
          funext u; rw [one_mul, add_comm], show (1 : ℝ) * r + t = t + r from by ring] at h
        exact h
      rw [hv]
      intro h0
      have hsp := hGpsp (t + r) (hab2 r hr)
      rw [h0, norm_zero] at hsp; norm_num at hsp
    have hGzne : ∀ r ∈ Ioo a b, curveVelocity (I := I) Gz r ≠ 0 := by
      intro r hr h0
      have hsp := hGzsp r (hab1 hr)
      rw [h0, norm_zero] at hsp; norm_num at hsp
    have hEqOn : EqOn Gz (fun r : ℝ => Gp (t + r)) (Ioo a b) :=
      eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := a) (b := b)
        (hGzsm.mono hab1) hKsm
        (fun r hr => hGzgeo r (hab1 hr)) hKgeo
        (fun r hr => hGzne r hr) hKne
        (t₀ := 0) (Set.mem_Ioo.mpr ⟨ha0, h0b⟩)
        (by rw [hGz0]; exact congrArg Gp (show t = t + 0 from by ring)) (by rw [hGzv, hKv])
    have hGs : GExp (cov := cov) hmet (Gp t) (s • w) = Gz s := by
      have h := GExp_eq_geodCurve (cov := cov) hmet (x := Gp t) (u := unitOf (s • w) hsvne)
        (unitOf_norm (s • w) hsvne) (T := s) hs0 hs0 le_rfl
      have h2 : GExp (cov := cov) hmet (Gp t) (s • w)
          = GExp (cov := cov) hmet (Gp t) (s • unitOf (s • w) hsvne) := by rw [hunit]
      rw [h2, h]
    rw [hGs, hEqOn (Set.mem_Ioo.mpr ⟨has, hsb⟩)]

/-! ## The distance along a ray, and Hopf–Rinow -/

/-- **The distance between two points of a ray of the global exponential map.** -/
theorem riemannianEDist_GExp_ray_le (hmet : IsMetricCompatible cov) (z : M)
    {η : TangentSpace I z} (hη : ‖η‖ = 1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • η))
        (GExp (cov := cov) hmet z (b • η)) ≤ ENNReal.ofReal (b - a) := by
  have hbnn : 0 ≤ b := le_trans ha0 hab
  obtain ⟨-, -, hsm, -, hsp⟩ := geodCurve_spec (cov := cov) hmet b hbnn z η hη
  have hA := GExp_eq_geodCurve (cov := cov) hmet (x := z) (u := η) hη (T := b) hbnn ha0 hab
  have hB := GExp_eq_geodCurve (cov := cov) hmet (x := z) (u := η) hη (T := b) hbnn hbnn le_rfl
  rw [hA, hB]
  have hsub : Icc a b ⊆ Ioo (-(geodDelta (cov := cov) hmet)) (b + geodDelta (cov := cov) hmet) :=
    fun r hr => ⟨by linarith [geodDelta_pos (cov := cov) hmet, hr.1],
      by linarith [geodDelta_pos (cov := cov) hmet, hr.2]⟩
  have hγ : CMDiff[Icc a b] 1 (geodCurve (cov := cov) hmet b hbnn z η hη) :=
    (hsm.mono hsub).of_le (WithTop.coe_le_coe.mpr le_top)
  calc Manifold.riemannianEDist I (geodCurve (cov := cov) hmet b hbnn z η hη a)
        (geodCurve (cov := cov) hmet b hbnn z η hη b)
      ≤ Manifold.pathELength I (geodCurve (cov := cov) hmet b hbnn z η hη) a b :=
        Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab
    _ = ENNReal.ofReal (b - a) :=
        pathELength_of_unit_speed (I := I) (fun r hr => hsp r (hsub hr))

/-- **Hopf–Rinow.**  On a compact connected Riemannian manifold every two points are joined by a
minimising geodesic: for all `p q` there is `v ∈ T_pM` with `GExp p v = q` and
`d(p,q) = ‖v‖`. -/
theorem exists_geodesic_riemannianEDist_eq [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (p q : M) :
    ∃ v : TangentSpace I p, GExp (cov := cov) hmet p v = q ∧
      Manifold.riemannianEDist I p q = ENNReal.ofReal ‖v‖ := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨ρ₁, hρ₁, hexp⟩ :=
    exists_eq_expMap_of_riemannianEDist_lt (I := I) (cov := cov) hmet htor p
  obtain ⟨ρ₂, hρ₂, hexp_eq⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet p
  set ρ : ℝ := min ρ₁ ρ₂ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  by_cases hsmall : Manifold.riemannianEDist I p q < ENNReal.ofReal ρ
  · obtain ⟨v, hv, hd⟩ := hexp q
      (lt_of_lt_of_le hsmall (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    have hvρ₂ : ‖v‖ < ρ₂ := by
      have h1 : ENNReal.ofReal ‖v‖ < ENNReal.ofReal ρ₂ := by
        rw [← hd]
        exact lt_of_lt_of_le hsmall (ENNReal.ofReal_le_ofReal (min_le_right _ _))
      exact (ENNReal.ofReal_lt_ofReal_iff hρ₂).mp h1
    exact ⟨v, by rw [← hv, hexp_eq v hvρ₂], hd⟩
  · push Not at hsmall
    have hdtop : Manifold.riemannianEDist I p q < ⊤ :=
      riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p q
    set L : ℝ := (Manifold.riemannianEDist I p q).toReal with hLdef
    have hdL : Manifold.riemannianEDist I p q = ENNReal.ofReal L :=
      (ENNReal.ofReal_toReal hdtop.ne).symm
    have hLge : ρ ≤ L := by
      rw [hLdef, ← ENNReal.toReal_ofReal hρ.le]
      exact ENNReal.toReal_mono hdtop.ne hsmall
    have hLpos : 0 < L := lt_of_lt_of_le hρ hLge
    have hLnn : 0 ≤ L := hLpos.le
    have hεpos : 0 < ρ / 2 := by linarith
    have hεL : ρ / 2 < L := by linarith
    -- the point `y₁` minimising `d(·,q)` on the sphere of radius `ρ/2`
    obtain ⟨y₁, hy₁, hy₁tri, hy₁min⟩ :=
      Commons.Geometry.Manifold.riemannianEDist_min_on_sphere_enormSMul (I := I) p q hεpos
        (exists_riemannianEDist_eq_ofReal (I := I) p q hεpos
          (by rw [hdL]; exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hεL))
        (continuous_riemannianEDist_left (I := I) p) (continuous_riemannianEDist_right (I := I) q)
        (by rw [hdL]; exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hεL)
    have hy₁q : Manifold.riemannianEDist I y₁ q = ENNReal.ofReal (L - ρ/2) := by
      have h : Manifold.riemannianEDist I y₁ q + ENNReal.ofReal (ρ/2) = ENNReal.ofReal L := by
        rw [hy₁tri, hdL]
      have h2 : ENNReal.ofReal (L - ρ/2) + ENNReal.ofReal (ρ/2) = ENNReal.ofReal L := by
        rw [← ENNReal.ofReal_add (by linarith) hεpos.le, show L - ρ/2 + ρ/2 = L from by ring]
      exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp (h.trans h2.symm)
    have hltρ₁ : ρ / 2 < ρ₁ := by
      have h : ρ ≤ ρ₁ := by rw [hρdef]; exact min_le_left _ _
      linarith
    obtain ⟨v₁, hv₁eq, hv₁d⟩ := hexp y₁ (by
      rw [hy₁]; exact (ENNReal.ofReal_lt_ofReal_iff hρ₁).mpr hltρ₁)
    have hv₁norm : ‖v₁‖ = ρ/2 := by
      have h : ENNReal.ofReal ‖v₁‖ = ENNReal.ofReal (ρ/2) := by rw [← hv₁d, hy₁]
      exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) hεpos.le).mp h
    have hv₁ne : v₁ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hv₁norm; linarith
    set u : TangentSpace I p := unitOf v₁ hv₁ne with hudef
    have hunorm : ‖u‖ = 1 := unitOf_norm v₁ hv₁ne
    have hu_v₁ : (ρ/2) • u = v₁ := by
      rw [hudef, unitOf, smul_smul, hv₁norm, mul_inv_cancel₀ (ne_of_gt hεpos), one_smul]
    have hv₁ρ₂ : ‖v₁‖ < ρ₂ := by
      have hρle : ρ ≤ ρ₂ := by rw [hρdef]; exact min_le_right _ _
      have hlt : ‖v₁‖ < ρ := by rw [hv₁norm]; linarith
      linarith
    have hGExp_v₁ : GExp (cov := cov) hmet p v₁ = y₁ := by
      rw [hexp_eq v₁ hv₁ρ₂, hv₁eq]
    -- the ray
    set α : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet p (t • u) with hαdef
    have hαε : α (ρ/2) = y₁ := by
      simp only [hαdef]
      rw [hu_v₁, hGExp_v₁]
    -- the underlying chosen geodesic of length `L`
    set Gp : ℝ → M := geodCurve (cov := cov) hmet L hLnn p u hunorm with hGpdef
    have hGpspec := geodCurve_spec (cov := cov) hmet L hLnn p u hunorm
    have hGpsm : ContMDiffOn 𝓘(ℝ) I ∞ Gp
        (Ioo (-(geodDelta (cov := cov) hmet)) (L + geodDelta (cov := cov) hmet)) := by
      rw [hGpdef]; exact hGpspec.2.2.1
    have hGpsp : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (L + geodDelta (cov := cov) hmet), ‖curveVelocity (I := I) Gp r‖ = 1 := by
      intro r hr; rw [hGpdef]; exact hGpspec.2.2.2.2 r hr
    have hαGp : ∀ t ∈ Icc (0:ℝ) L, α t = Gp t := by
      intro t ht
      simp only [hαdef, hGpdef]
      exact GExp_eq_geodCurve (cov := cov) hmet (x := p) (u := u) hunorm (T := L) hLnn ht.1 ht.2
    have hαcont : ContinuousOn α (Icc (0:ℝ) L) :=
      (hGpsm.continuousOn.mono (fun r hr => ⟨by linarith [geodDelta_pos (cov := cov) hmet, hr.1],
        by linarith [geodDelta_pos (cov := cov) hmet, hr.2]⟩)).congr (fun t ht => hαGp t ht)
    -- the set of times up to which the ray is radial
    set S : Set ℝ := {t : ℝ | t ∈ Icc (0:ℝ) L ∧
      Manifold.riemannianEDist I p (α t) = ENNReal.ofReal t ∧
      Manifold.riemannianEDist I (α t) q = ENNReal.ofReal (L - t)} with hSdef
    have hSsub : S ⊆ Icc (0:ℝ) L := fun t ht => ht.1
    have hSclosed : IsClosed S := by
      rw [← closure_subset_iff_isClosed]
      intro t ht
      obtain ⟨un, huS, hut⟩ := mem_closure_iff_seq_limit.mp ht
      have huK : ∀ n, un n ∈ Icc (0:ℝ) L := fun n => (huS n).1
      have htK : t ∈ Icc (0:ℝ) L :=
        ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hut (Eventually.of_forall (fun n => (huK n).1)),
         le_of_tendsto_of_tendsto hut tendsto_const_nhds (Eventually.of_forall (fun n => (huK n).2))⟩
      have hut' : Tendsto un atTop (𝓝[Icc (0:ℝ) L] t) :=
        tendsto_nhdsWithin_iff.mpr ⟨hut, Eventually.of_forall huK⟩
      have hαtend : Tendsto (fun n => α (un n)) atTop (𝓝 (α t)) :=
        Filter.Tendsto.comp (ContinuousWithinAt.tendsto (hαcont.continuousWithinAt htK)) hut'
      have h1 : Tendsto (fun n => Manifold.riemannianEDist I p (α (un n))) atTop
          (𝓝 (Manifold.riemannianEDist I p (α t))) :=
        Filter.Tendsto.comp ((continuous_riemannianEDist_left (I := I) p).tendsto (α t)) hαtend
      have h2 : Tendsto (fun n => Manifold.riemannianEDist I p (α (un n))) atTop
          (𝓝 (ENNReal.ofReal t)) := by
        rw [show (fun n => Manifold.riemannianEDist I p (α (un n)))
            = (fun n => ENNReal.ofReal (un n)) from funext (fun n => (huS n).2.1)]
        exact Filter.Tendsto.comp (g := ENNReal.ofReal) (f := un)
          (hg := ENNReal.continuous_ofReal.tendsto t) (hf := hut)
      have h3 : Tendsto (fun n => Manifold.riemannianEDist I (α (un n)) q) atTop
          (𝓝 (Manifold.riemannianEDist I (α t) q)) :=
        Filter.Tendsto.comp ((continuous_riemannianEDist_right (I := I) q).tendsto (α t)) hαtend
      have h4 : Tendsto (fun n => Manifold.riemannianEDist I (α (un n)) q) atTop
          (𝓝 (ENNReal.ofReal (L - t))) := by
        rw [show (fun n => Manifold.riemannianEDist I (α (un n)) q)
            = (fun n => ENNReal.ofReal (L - un n)) from funext (fun n => (huS n).2.2)]
        exact Filter.Tendsto.comp (g := ENNReal.ofReal) (f := fun n => L - un n)
          (hg := ENNReal.continuous_ofReal.tendsto (L - t)) (hf := tendsto_const_nhds.sub hut)
      exact ⟨htK, tendsto_nhds_unique h1 h2, tendsto_nhds_unique h3 h4⟩
    have h0S : (0:ℝ) ∈ S := by
      refine ⟨⟨le_refl 0, hLnn⟩, ?_, ?_⟩
      · simp only [hαdef]; rw [zero_smul, GExp_zero, Manifold.riemannianEDist_self, ENNReal.ofReal_zero]
      · simp only [hαdef]; rw [zero_smul, GExp_zero, sub_zero, hdL]
    have hεS : ρ/2 ∈ S := by
      refine ⟨⟨hεpos.le, hεL.le⟩, ?_, ?_⟩
      · rw [hαε]; exact hy₁
      · rw [hαε]; exact hy₁q
    have hbdd : BddAbove S := ⟨L, fun x hx => hx.1.2⟩
    have hsupS : sSup S ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hbdd
    have hsup0 : 0 < sSup S := lt_of_lt_of_le hεpos (le_csSup hbdd hεS)
    -- the corner-cut step
    have hstep : ∀ t ∈ S, 0 < t → t < L → ∃ r : ℝ, 0 < r ∧ t + r ∈ S := by
      intro t ht ht0 htlt
      have htK : t ∈ Icc (0:ℝ) L := ht.1
      have htrad : Manifold.riemannianEDist I p (Gp t) = ENNReal.ofReal t := by
        rw [← hαGp t htK]; exact ht.2.1
      have htq : Manifold.riemannianEDist I (Gp t) q = ENNReal.ofReal (L - t) := by
        rw [← hαGp t htK]; exact ht.2.2
      -- the local theory at `Gp t`
      obtain ⟨ρz, hρz, hexpz⟩ :=
        exists_eq_expMap_of_riemannianEDist_lt (I := I) (cov := cov) hmet htor (Gp t)
      obtain ⟨ρz', hρz', hexpz_eq⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet (Gp t)
      set r : ℝ := min (min ρz ρz') (L - t) / 2 with hrdef
      have hrpos : 0 < r := by
        rw [hrdef]
        exact div_pos (lt_min (lt_min hρz hρz') (by linarith)) (by norm_num)
      have hrρz : r < ρz := by
        rw [hrdef]
        have h1 : min (min ρz ρz') (L - t) ≤ min ρz ρz' := min_le_left _ _
        have h2 : min ρz ρz' ≤ ρz := min_le_left _ _
        linarith
      have hrρz' : r < ρz' := by
        rw [hrdef]
        have h1 : min (min ρz ρz') (L - t) ≤ min ρz ρz' := min_le_left _ _
        have h2 : min ρz ρz' ≤ ρz' := min_le_right _ _
        linarith
      have hrLt : r < L - t := by
        rw [hrdef]
        have h1 : min (min ρz ρz') (L - t) ≤ L - t := min_le_right _ _
        linarith
      -- the sub-segment minimality
      have hsub_min : ∀ s ∈ Icc (0:ℝ) t, Manifold.riemannianEDist I p (α s) = ENNReal.ofReal s := by
        intro s hs
        have h1 : Manifold.riemannianEDist I p (α s) ≤ ENNReal.ofReal s := by
          have hγ : CMDiff[Icc (0:ℝ) s] 1 Gp :=
            (hGpsm.mono (fun q hq => ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1],
              by linarith [geodDelta_pos (cov := cov) hmet, hq.2, hs.2, htK.2]⟩)).of_le
              (WithTop.coe_le_coe.mpr le_top)
          have hpath : Manifold.pathELength I Gp 0 s = ENNReal.ofReal s := by
            rw [pathELength_of_unit_speed (I := I) (γ := Gp) (a := 0) (b := s) (fun q hq => hGpsp q
              ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1],
               by linarith [geodDelta_pos (cov := cov) hmet, hq.2, hs.2, htK.2]⟩), sub_zero]
          calc Manifold.riemannianEDist I p (α s) = Manifold.riemannianEDist I p (Gp s) := by
                rw [hαGp s ⟨hs.1, le_trans hs.2 htK.2⟩]
            _ ≤ Manifold.pathELength I Gp 0 s :=
                Manifold.riemannianEDist_le_pathELength hγ
                  (by rw [hGpdef]; exact hGpspec.1) rfl hs.1
            _ = ENNReal.ofReal s := hpath
        have h3 : Manifold.riemannianEDist I (α s) (α t) ≤ ENNReal.ofReal (t - s) := by
          have hγ : CMDiff[Icc s t] 1 Gp :=
            (hGpsm.mono (fun q hq => ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1, hs.1],
              by linarith [geodDelta_pos (cov := cov) hmet, hq.2, htK.2]⟩)).of_le
              (WithTop.coe_le_coe.mpr le_top)
          have hpath : Manifold.pathELength I Gp s t = ENNReal.ofReal (t - s) :=
            pathELength_of_unit_speed (I := I) (γ := Gp) (a := s) (b := t) (fun q hq => hGpsp q
              ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1, hs.1],
               by linarith [geodDelta_pos (cov := cov) hmet, hq.2, htK.2]⟩)
          calc Manifold.riemannianEDist I (α s) (α t) = Manifold.riemannianEDist I (Gp s) (Gp t) := by
                rw [hαGp s ⟨hs.1, le_trans hs.2 htK.2⟩, hαGp t htK]
            _ ≤ Manifold.pathELength I Gp s t :=
                Manifold.riemannianEDist_le_pathELength hγ rfl rfl hs.2
            _ = ENNReal.ofReal (t - s) := hpath
        have h5 : ENNReal.ofReal s + ENNReal.ofReal (t - s)
            ≤ Manifold.riemannianEDist I p (α s) + ENNReal.ofReal (t - s) := by
          calc ENNReal.ofReal s + ENNReal.ofReal (t - s) = ENNReal.ofReal (s + (t - s)) :=
                (ENNReal.ofReal_add hs.1 (sub_nonneg.mpr hs.2)).symm
            _ = ENNReal.ofReal t := by rw [show s + (t - s) = t from by ring]
            _ = Manifold.riemannianEDist I p (α t) := by rw [hαGp t htK]; exact htrad.symm
            _ ≤ Manifold.riemannianEDist I p (α s) + Manifold.riemannianEDist I (α s) (α t) :=
                Manifold.riemannianEDist_triangle (I := I)
            _ ≤ Manifold.riemannianEDist I p (α s) + ENNReal.ofReal (t - s) := add_le_add le_rfl h3
        exact le_antisymm h1 ((ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h5)
      -- the minimiser on the sphere of radius `r` around `Gp t`
      obtain ⟨y', hy', hy'tri, hy'min⟩ :=
        Commons.Geometry.Manifold.riemannianEDist_min_on_sphere_enormSMul (I := I) (Gp t) q hrpos
          (exists_riemannianEDist_eq_ofReal (I := I) (Gp t) q hrpos
            (by rw [htq]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hrLt))
          (continuous_riemannianEDist_left (I := I) (Gp t))
          (continuous_riemannianEDist_right (I := I) q)
          (by rw [htq]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hrLt)
      have hy'q : Manifold.riemannianEDist I y' q = ENNReal.ofReal (L - t - r) := by
        have h : Manifold.riemannianEDist I y' q + ENNReal.ofReal r = ENNReal.ofReal (L - t) := by
          rw [hy'tri, htq]
        have h2 : ENNReal.ofReal (L - t - r) + ENNReal.ofReal r = ENNReal.ofReal (L - t) := by
          rw [← ENNReal.ofReal_add (by linarith) (le_of_lt hrpos),
            show L - t - r + r = L - t from by ring]
        exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp (h.trans h2.symm)
      obtain ⟨w', hw'eq, hw'd⟩ := hexpz y' (by
        rw [hy']; exact (ENNReal.ofReal_lt_ofReal_iff hρz).mpr hrρz)
      have hw'norm : ‖w'‖ = r := by
        have h : ENNReal.ofReal ‖w'‖ = ENNReal.ofReal r := by rw [← hw'd, hy']
        exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) hrpos.le).mp h
      have hw'ne : w' ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hw'norm; linarith
      set η : TangentSpace I (Gp t) := unitOf w' hw'ne with hηdef
      have hηnorm : ‖η‖ = 1 := unitOf_norm w' hw'ne
      have hrη : r • η = w' := by
        rw [hηdef, unitOf, smul_smul, hw'norm, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]
      have hy'GExp : y' = GExp (cov := cov) hmet (Gp t) (r • η) := by
        rw [hrη, hexpz_eq w' (by rw [hw'norm]; exact hrρz'), hw'eq]
      -- the unit velocity of the ray at `t`
      have htIoo : t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (L + geodDelta (cov := cov) hmet) :=
        Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet, ht0.le],
          by linarith [htK.2, geodDelta_pos (cov := cov) hmet]⟩
      set ξ : TangentSpace I (Gp t) := curveVelocity (I := I) Gp t with hξdef
      have hξnorm : ‖ξ‖ = 1 := hGpsp t htIoo
      -- the corner cut
      have hξη : ξ = η := by
        by_contra hne
        obtain ⟨δc, hδc, hcut⟩ := corner_cut (cov := cov) hmet (Gp t) hξnorm hηnorm hne
        set τ : ℝ := min (min δc t) r / 2 with hτdef
        have hτpos : 0 < τ := by
          rw [hτdef]
          exact div_pos (lt_min (lt_min hδc ht0) hrpos) (by norm_num)
        have hτδ : τ < δc := by
          rw [hτdef]
          have h1 : min (min δc t) r ≤ min δc t := min_le_left _ _
          have h2 : min δc t ≤ δc := min_le_left _ _
          linarith
        have hτt : τ < t := by
          rw [hτdef]
          have h1 : min (min δc t) r ≤ min δc t := min_le_left _ _
          have h2 : min δc t ≤ t := min_le_right _ _
          linarith
        have hτr : τ < r := by
          rw [hτdef]
          have h1 : min (min δc t) r ≤ r := min_le_right _ _
          linarith
        set A : M := GExp (cov := cov) hmet (Gp t) ((-τ) • ξ) with hAdef
        set B : M := GExp (cov := cov) hmet (Gp t) (τ • η) with hBdef
        have hAcut : Manifold.riemannianEDist I A B < ENNReal.ofReal (2 * τ) := hcut τ hτpos hτδ
        have hAeq' : GExp (cov := cov) hmet (Gp t)
            ((-τ) • curveVelocity (I := I) Gp t) = Gp (t - τ) :=
          GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet p hunorm (T := L) hLnn
            ht0.le htK.2 (le_of_lt hτpos) hτt.le
        have hAeq : A = α (t - τ) := by
          rw [hAdef, hξdef]
          exact hAeq'.trans (hαGp (t - τ) ⟨by linarith, by linarith [htK.2]⟩).symm
        have hAx : Manifold.riemannianEDist I p A ≤ ENNReal.ofReal (t - τ) := by
          rw [hAeq]; exact (hsub_min (t - τ) ⟨by linarith, by linarith⟩).le
        have hBy : Manifold.riemannianEDist I B (GExp (cov := cov) hmet (Gp t) (r • η))
            ≤ ENNReal.ofReal (r - τ) :=
          riemannianEDist_GExp_ray_le (cov := cov) hmet (Gp t) hηnorm hτpos.le hτr.le
        have hB2 : Manifold.riemannianEDist I B q
            ≤ Manifold.riemannianEDist I B (GExp (cov := cov) hmet (Gp t) (r • η))
              + Manifold.riemannianEDist I (GExp (cov := cov) hmet (Gp t) (r • η)) q :=
          Manifold.riemannianEDist_triangle (I := I)
        have h3 : Manifold.riemannianEDist I (GExp (cov := cov) hmet (Gp t) (r • η)) q
            = ENNReal.ofReal (L - t - r) := by
          rw [← hy'GExp]; exact hy'q
        have hByq : Manifold.riemannianEDist I B q
            ≤ ENNReal.ofReal (r - τ) + ENNReal.ofReal (L - t - r) :=
          hB2.trans (add_le_add hBy (le_of_eq h3))
        have htri1 : Manifold.riemannianEDist I p q
            ≤ (Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B)
              + Manifold.riemannianEDist I B q := by
          calc Manifold.riemannianEDist I p q
              ≤ Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A q :=
                Manifold.riemannianEDist_triangle (I := I)
            _ ≤ Manifold.riemannianEDist I p A
                  + (Manifold.riemannianEDist I A B + Manifold.riemannianEDist I B q) :=
                add_le_add le_rfl (Manifold.riemannianEDist_triangle (I := I))
            _ = (Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B)
                  + Manifold.riemannianEDist I B q := by rw [add_assoc]
        have hlt2 : (Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B)
              + Manifold.riemannianEDist I B q
            < (ENNReal.ofReal (t - τ) + ENNReal.ofReal (2 * τ))
              + (ENNReal.ofReal (r - τ) + ENNReal.ofReal (L - t - r)) := by
          have hXY : Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B
              < ENNReal.ofReal (t - τ) + ENNReal.ofReal (2 * τ) :=
            ENNReal.add_lt_add_of_le_of_lt
              (ne_of_lt (lt_of_le_of_lt hAx ENNReal.ofReal_lt_top)) hAx hAcut
          have hZne : Manifold.riemannianEDist I B q ≠ ⊤ :=
            ne_of_lt (lt_of_le_of_lt hByq
              (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))
          exact ENNReal.add_lt_add_of_lt_of_le hZne hXY hByq
        have hsum : (ENNReal.ofReal (t - τ) + ENNReal.ofReal (2 * τ))
              + (ENNReal.ofReal (r - τ) + ENNReal.ofReal (L - t - r)) = ENNReal.ofReal L := by
          rw [← ENNReal.ofReal_add (show 0 ≤ t - τ by linarith) (show 0 ≤ 2 * τ by linarith),
            ← ENNReal.ofReal_add (show 0 ≤ r - τ by linarith) (show 0 ≤ L - t - r by linarith),
            ← ENNReal.ofReal_add (show 0 ≤ t - τ + 2 * τ by linarith)
              (show 0 ≤ r - τ + (L - t - r) by linarith),
            show t - τ + 2 * τ + (r - τ + (L - t - r)) = L from by ring]
        exact absurd (lt_of_le_of_lt htri1 (hlt2.trans_eq hsum)) (not_lt.mpr (le_of_eq hdL.symm))
      -- conclude
      have hyt : Manifold.riemannianEDist I p y' = ENNReal.ofReal (t + r) := by
        have h1 : Manifold.riemannianEDist I p y' ≤ ENNReal.ofReal (t + r) := by
          calc Manifold.riemannianEDist I p y'
              ≤ Manifold.riemannianEDist I p (Gp t) + Manifold.riemannianEDist I (Gp t) y' :=
                Manifold.riemannianEDist_triangle (I := I)
            _ = ENNReal.ofReal t + ENNReal.ofReal r := by rw [htrad, hy']
            _ = ENNReal.ofReal (t + r) := (ENNReal.ofReal_add ht0.le hrpos.le).symm
        have h2 : ENNReal.ofReal (t + r) ≤ Manifold.riemannianEDist I p y' := by
          have h3 : ENNReal.ofReal (t + r) + ENNReal.ofReal (L - t - r) ≤ ENNReal.ofReal L := by
            rw [← ENNReal.ofReal_add (show 0 ≤ t + r by linarith)
              (show 0 ≤ L - t - r by linarith), show t + r + (L - t - r) = L from by ring]
          have h4 : ENNReal.ofReal L
              ≤ Manifold.riemannianEDist I p y' + Manifold.riemannianEDist I y' q := by
            rw [← hdL]
            exact Manifold.riemannianEDist_triangle (I := I) (x := p) (y := y') (z := q)
          rw [hy'q] at h4
          exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp (le_trans h3 h4)
        exact le_antisymm h1 h2
      have hytq : Manifold.riemannianEDist I y' q = ENNReal.ofReal (L - (t + r)) := by
        rw [hy'q, show L - t - r = L - (t + r) from by ring]
      have hα : α (t + r) = y' := by
        have h1 : α (t + r) = Gp (t + r) :=
          hαGp (t + r) ⟨by linarith, by linarith [hrLt]⟩
        have h2 : GExp (cov := cov) hmet (Gp t) (r • curveVelocity (I := I) Gp t) = Gp (t + r) :=
          GExp_geodCurve_add (cov := cov) hmet p hunorm (T := L) hLnn ht0.le htK.2 hrpos.le
            (by linarith [hrLt])
        rw [h1, ← h2, ← hξdef, hξη]
        exact hy'GExp.symm
      have hmem : t + r ∈ S := by
        change t + r ∈ Icc (0:ℝ) L
          ∧ Manifold.riemannianEDist I p (α (t + r)) = ENNReal.ofReal (t + r)
          ∧ Manifold.riemannianEDist I (α (t + r)) q = ENNReal.ofReal (L - (t + r))
        exact ⟨⟨by linarith, by linarith [hrLt]⟩, by rw [hα]; exact hyt, by rw [hα]; exact hytq⟩
      exact ⟨r, hrpos, hmem⟩
    -- assemble
    have hsupL : sSup S = L := by
      by_contra hne
      have hlt : sSup S < L := lt_of_le_of_ne hsupS.1.2 hne
      obtain ⟨r, hrpos, hrS⟩ := hstep (sSup S) hsupS hsup0 hlt
      have hle : sSup S + r ≤ sSup S := le_csSup hbdd hrS
      linarith
    have hLS : L ∈ S := hsupL ▸ hsupS
    have hαLq : α L = q := by
      have h0 : Manifold.riemannianEDist I (α L) q = 0 := by
        rw [hLS.2.2, show L - L = 0 from by ring, ENNReal.ofReal_zero]
      exact (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h0
    refine ⟨L • u, ?_, ?_⟩
    · have h := hαLq
      simp only [hαdef] at h
      exact h
    · rw [hdL, show ‖L • u‖ = L from by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hLnn, hunorm, mul_one]]

end Ray

end

end Submission.HopfRinow
