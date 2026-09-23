import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.longHomotopy.pairing_affine_of_jacobi
import Submission.Work.OddBound.longHomotopy.covAlong_variation_zero
import Submission.Work.OddBound.longHomotopy.gauss_pairing_rescale

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-!
# The Gauss pairing along the fibres of the exponential map

`GExp p` is the global exponential map at `p`.  Writing, for `v, η ∈ T_pM`,

* `γ_v (t) = GExp p (t • v)` for the geodesic ray of `v`,
* `J_v (t) = ∂_r|_{r=0} GExp p (t • (v + r • η))` for the variation field of the family of rays,

the **Gauss pairing** says `⟪J_v(t), γ_v'(t)⟫ = t ⟪η, v⟫` for every real `t`.

The proof has three ingredients:

* `pairing_affine_of_jacobi` — along a geodesic `γ` with nowhere-vanishing velocity and a Jacobi
  field `J`, the pairing `t ↦ ⟪J t, γ'(t)⟫` is affine with slope `⟪∇_{γ'}J(0), γ'(0)⟫`;
* `covAlong_variation_zero` — the variation field of the family `r ↦ GExp p (s • (u + r • η))` has
  covariant derivative `η` at `0`;
* `gauss_pairing_rescale` — the statement rescales from a unit vector to an arbitrary one.

The vector `v = 0` is handled separately, where the second factor of the pairing vanishes.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-! ## Two auxiliary facts -/

/-- **`IsJacobiAt` depends only on the germ of the base curve**: if `γ =ᶠ γ'` near `t` then a Jacobi
field along `γ` is a Jacobi field along `γ'`. -/
lemma isJacobiAt_congr_curve {γ γ' : ℝ → M} {J : (s : ℝ) → TangentSpace I (γ s)} {t : ℝ}
    (h : γ =ᶠ[𝓝 t] γ') (hJ : Submission.RauchGlobal.IsJacobiAt cov γ J t) :
    Submission.RauchGlobal.IsJacobiAt cov γ' J t := by
  obtain ⟨x₀, u, w, y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hJ
  refine ⟨x₀, u, w, y, h1, h2, ?_, ?_, h5, h6, h7, h8⟩
  · filter_upwards [h, h3] with s hs h3s
    rw [← hs, h3s]
  · filter_upwards [h, h4] with s hs h4s
    rw [← hs]
    exact h4s

/-- **The variation field vanishes at `0`**: the curve `r ↦ GExp p (0 • (u + r • η))` is constant
`p`. -/
lemma variation_zero_at_zero (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {p : M} {u η : TangentSpace I p} :
    curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p ((0:ℝ) • (u + r • η))) 0 = 0 := by
  have hconst : (fun r : ℝ => GExp (cov := cov) hmet p ((0:ℝ) • (u + r • η))) = fun _ => p := by
    funext r
    rw [zero_smul, Submission.GlobalExp.GExp_zero]
  rw [hconst]
  exact curveVelocity_const (I := I) p 0

/-! ## The unit case -/

theorem gauss_pairing_fibre_unit (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {p : M} {u η : TangentSpace I p} (hu : u ≠ 0) (hu1 : ‖u‖ = 1) :
    ∀ t : ℝ,
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (t • (u + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) t)
      = t * Inner.inner ℝ η u := by
  have hfun : (fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
      = (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) := by
    funext s; rw [zero_smul, add_zero]
  have hγU : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) :=
    contMDiffOn_univ.mp (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hu)
  have hγA : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η))) := by
    rw [hfun]; exact hγU
  have hgeoU : ∀ s, Submission.Geodesic.IsGeodesicAt cov
      (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) s :=
    fun s => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hu s
  have hgeoA : ∀ s, Submission.Geodesic.IsGeodesicAt cov
      (fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η))) s := by
    intro s
    rw [hfun]
    exact hgeoU s
  have hneU : ∀ s, curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) s ≠ 0 :=
    fun s => Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hu s
  have hneA : ∀ s, curveVelocity (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η))) s ≠ 0 := by
    intro s h0
    have hcv := Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
      (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
      (γ' := fun s : ℝ => GExp (cov := cov) hmet p (s • u))
      (Filter.Eventually.of_forall (fun r => congrFun hfun r)) (t := s)
    rw [hcv] at h0
    exact hneU s h0
  have hJU : ∀ s, Submission.RauchGlobal.IsJacobiAt cov
      (fun s : ℝ => GExp (cov := cov) hmet p (s • u))
      (fun s : ℝ => curveVelocity (I := I)
        (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) 0) s :=
    fun s => Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hu hu1 s
  have hJA : ∀ s, Submission.RauchGlobal.IsJacobiAt cov
      (fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
      (fun s : ℝ => curveVelocity (I := I)
        (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) 0) s :=
    fun s => isJacobiAt_congr_curve (cov := cov)
      (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • u))
      (γ' := fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
      (J := fun s : ℝ => curveVelocity (I := I)
        (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) 0)
      (Filter.Eventually.of_forall (fun r => (congrFun hfun r).symm)) (hJU s)
  intro t
  have haff := pairing_affine_of_jacobi (cov := cov) hmet htor
    (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
    (J := fun s : ℝ => curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) 0) hJA hγA hneA hgeoA t
  have hJ0 : curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet p ((0:ℝ) • (u + r • η))) 0 = 0 :=
    variation_zero_at_zero (cov := cov) hmet
  have hS0 : curveVelocity (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η))) 0 = u := by
    have hvne : u + (0:ℝ) • η ≠ 0 := by
      rw [zero_smul, add_zero]; exact hu
    have h := Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hvne
    simpa [zero_smul, add_zero] using h
  have hcv0 : Submission.JacobiGlobal.covAlong cov
      (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
      (fun s : ℝ => curveVelocity (I := I)
        (fun r : ℝ => GExp (cov := cov) hmet p (s • (u + r • η))) 0) 0 = η :=
    covAlong_variation_zero (cov := cov) hmet htor hu
  have hcvA : curveVelocity (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η))) t
      = curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) t :=
    Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
      (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • (u + (0:ℝ) • η)))
      (γ' := fun s : ℝ => GExp (cov := cov) hmet p (s • u))
      (Filter.Eventually.of_forall (fun r => congrFun hfun r)) (t := t)
  rw [← hcvA, haff]
  have hpt : GExp (cov := cov) hmet p ((0:ℝ) • (u + (0:ℝ) • η)) = p := by
    rw [zero_smul, Submission.GlobalExp.GExp_zero]
  rw [hJ0, hS0, hcv0, inner_zero_left, zero_add]
  rw [hpt]

/-! ## The general case -/

theorem gauss_pairing_fibre
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {v η : TangentSpace I p} :
    ∀ t : ℝ,
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (t • (v + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) t)
      = t * Inner.inner ℝ η v := by
  rintro t
  by_cases hv : v = 0
  · subst hv
    have hcurve : (fun s : ℝ => GExp (cov := cov) hmet p (s • (0 : TangentSpace I p)))
        =ᶠ[𝓝 t] (fun s : ℝ => GExp (cov := cov) hmet p (s • ((0 : TangentSpace I p) + (0:ℝ) • η))) :=
      Filter.EventuallyEq.of_eq (by funext s; rw [zero_smul, add_zero])
    rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hcurve]
    have hB : curveVelocity (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ((0 : TangentSpace I p) + (0:ℝ) • η))) t
        = (0 : TangentSpace I (GExp (cov := cov) hmet p (t • ((0 : TangentSpace I p) + (0:ℝ) • η)))) := by
      have h1 : (fun s : ℝ => GExp (cov := cov) hmet p (s • ((0 : TangentSpace I p) + (0:ℝ) • η)))
          = fun _ => p := by
        funext s
        rw [zero_smul, add_zero, smul_zero, Submission.GlobalExp.GExp_zero]
      rw [h1]
      exact curveVelocity_const (I := I) p t
    rw [hB, inner_zero_right, inner_zero_right, mul_zero]
  · set u : TangentSpace I p := (‖v‖)⁻¹ • v with hu_def
    have hvn : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv
    have hu1 : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ (ne_of_gt hvn)]
    have hu : u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hu1
      norm_num at hu1
    have hcu : v = ‖v‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hvn), one_smul]
    exact gauss_pairing_rescale (cov := cov) hmet htor hv hu1 hcu
      (gauss_pairing_fibre_unit (cov := cov) hmet htor hu hu1) t

end Work.OddBound.longHomotopy
