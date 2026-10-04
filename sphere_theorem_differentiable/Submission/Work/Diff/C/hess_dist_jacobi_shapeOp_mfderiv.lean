import Mathlib
import Submission.Work.Diff.C.HessLowerKit
import Submission.RayJacobi
import Submission.RayJacobiTensor
import Submission.ConjCut
import Submission.CurveCov
import Submission.CurveField
import Submission.Work.OddBound.longHomotopy.gauss_pairing_fibre
import Submission.Work.OddBound.longHomotopy.covAlong_variation_zero
import Submission.Work.OddBound.longHomotopy.pairing_affine_of_jacobi
import Submission.Work.Diff.C.ShapeAux.Kit
import Submission.Work.Diff.C.ShapeAux.norm_add_smul_deriv_deriv
import Submission.Work.Diff.C.ShapeAux.deriv_deriv_comp_curve
import Submission.Work.Diff.C.ShapeAux.gauss_pairing_second_deriv

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000


/-- **`covAlong` is invariant under rewriting the base curve and the field** (a `covAlong` depends on
its curve and on the values of the field only, so two curves that are equal as functions with the
same field values give the same covariant derivative). -/
private theorem covAlong_congr_curve'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {γ₁ γ₂ : ℝ → M} (h : γ₁ = γ₂)
    {V₁ : (t : ℝ) → TangentSpace I (γ₁ t)} {V₂ : (t : ℝ) → TangentSpace I (γ₂ t)}
    (hV : ∀ t : ℝ, (show E from V₁ t) = (show E from V₂ t)) (d : ℝ) :
    Submission.JacobiGlobal.covAlong cov V₁ d
      = (show TangentSpace I (γ₁ d) from Submission.JacobiGlobal.covAlong cov V₂ d) := by
  subst h
  rw [show V₁ = V₂ from funext hV]


/-- **Inner products of two tangent vectors at two equal base points.**  A `TangentSpace I x` is
definitionally the model space `E` for all `x`, so vectors can be moved between the tangent spaces
at equal points; the scalar product, however, is the fibre metric at the point, and this lemma
records that rewriting the point along an equality does not change it. -/
private theorem inner_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {x y : M} (h : x = y) (a b : TangentSpace I x) :
    Inner.inner ℝ a b
      = Inner.inner ℝ (show TangentSpace I y from a) (show TangentSpace I y from b) := by
  subst h
  rfl

/-- The scalar product of a fibre is the metric section of the Riemannian bundle, evaluated at the
base point of the fibre.  Everything below is phrased with the *plain function* `(g).inner X a b`
(point first, model-space vectors after), because rewriting the point of such an application is an
ordinary congruence, whereas rewriting the point of an `Inner.inner` application means rewriting a
type-class instance. -/
private theorem inner_eq_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] {X : M} (a b : TangentSpace I X) :
    Inner.inner ℝ a b
      = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner X a b := rfl

/-- The metric section only depends on its point through the point: equal points give the same
form. -/
private theorem metric_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] {X Y : M} (h : X = Y) (a b : E) :
    ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner X a b = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner Y a b :=
  congrArg (fun Z => ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner Z a b) h

/-- Symmetry of the metric form. -/
private theorem metric_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] {X : M} (a b : TangentSpace I X) :
    ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner X a b = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner X b a :=
  (inner_eq_metric (X := X) a b).symm.trans
    ((real_inner_comm a b).symm.trans (inner_eq_metric (X := X) b a))

theorem hess_dist_jacobi_shapeOp_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (p : M) {d : ℝ} (hd : 0 < d) {u : TangentSpace I p} (hu : ‖u‖ = 1)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) d,
      Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
        = ENNReal.ofReal t)
    (hminW : ∀ w : TangentSpace I p, ∀ᶠ s in 𝓝 (0 : ℝ),
      Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + s • w))
        = ENNReal.ofReal ‖(d • u) + s • w‖)
    (hF : CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
    (hunit : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) = 1)
    (V : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
    (w : TangentSpace I p)
    (hw : (mfderiv% (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet p
        (show TangentSpace I p from u))) (show E from (d • u)) (show E from w) = V) :
    ∃ Z : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)),
      (∀ t, Submission.RauchGlobal.IsJacobiAt cov
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) Z t) ∧
      Z 0 = 0 ∧ Z d = V ∧
      Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V
        + (Inner.inner ℝ
            (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) V) ^ 2 / d
        = Inner.inner ℝ
            (Submission.JacobiGlobal.covAlong cov Z d) V
:= by
  classical
  -- ## 0. Preliminaries
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    norm_num at hu
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hnormdu : ‖(d • u : TangentSpace I p)‖ = d := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, hu, mul_one]
  have hdune : (d • u : TangentSpace I p) ≠ 0 := by
    have h : 0 < ‖(d • u : TangentSpace I p)‖ := by rw [hnormdu]; exact hd
    exact norm_pos_iff.mp h
  -- ## 1. the tangent vector `w` at `p` with `(dGExp_p)_{d•u} w = V` is now a hypothesis
  -- ## 2. the Jacobi field `Z`: the variation field of the family of rays
  set η : TangentSpace I p := d⁻¹ • w with hηdef
  have hdη : d • η = w := by rw [hηdef, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  have hηnorm : ‖η‖ = d⁻¹ * ‖w‖ := by
    rw [hηdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  set Z : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) :=
      fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0
    with hZdef
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hZdef]
    exact Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hu0 hu t
  · rw [hZdef]
    exact Work.OddBound.longHomotopy.variation_zero_at_zero (cov := cov) hmet
  · rw [hZdef]
    change Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0 = V
    rw [Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet d u η]
    rw [show (d • η : TangentSpace I p) = w from hdη]
    exact hw
  · by_cases hV : V = 0
    · subst hV
      simp [rhess]
    · -- ## 3. the shape-operator identity
      -- ### 3.0 the curve of the variation and its velocity
      -- the same, stated with the explicit curve (used in the final assembly)
      have hcvelL : Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))) 0 = V := by
        rw [Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet d u η]
        rw [show (d • η : TangentSpace I p) = w from hdη]
        exact hw
      have hccurve' : ∀ s : ℝ, Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))
          = Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + s • w) := by
        intro s
        congr 1
        rw [smul_add, smul_smul, hηdef, smul_smul]
        have hs : d * s * d⁻¹ = s := by
          rw [mul_assoc, mul_comm s d⁻¹, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
        rw [hs]
      set c : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))
        with hcdef
      have hccurve : c = fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
          ((d • u) + s • w) := by
        funext s
        rw [hcdef]
        exact hccurve' s
      have hc0 : c 0 = Submission.GlobalExp.GExp (cov := cov) hmet p (d • u) := by
        rw [hcdef]; simp
      have hcsm : ContMDiff 𝓘(ℝ) I ∞ c := by
        intro s
        rw [hcdef]
        have hlin : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
            (fun s' : ℝ => (show E from (d • (u + s' • η)))) s := by
          rw [contMDiffAt_iff_contDiffAt]
          fun_prop
        exact (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p
          (d • (u + s • η))).comp s hlin
      have hcvel : Submission.Geodesic.curveVelocity (I := I) c 0 = V := by
        rw [hcdef]
        change Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0 = V
        rw [Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet d u η]
        rw [show (d • η : TangentSpace I p) = w from hdη]
        exact hw
      -- the distance identity along the variation
      have hdist : (fun s : ℝ => rdist (I := I) (M := M) p (c s))
          =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => ‖(d • u) + s • w‖) := by
        filter_upwards [Filter.EventuallyEq.of_eq hccurve, hminW w] with s hs hs2
        rw [hs, rdist, hs2, ENNReal.toReal_ofReal (norm_nonneg _)]
      have hdistL : (fun s : ℝ => rdist (I := I) (M := M) p
            ((fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))) s))
          =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => ‖(d • u) + s • w‖) := by
        filter_upwards [hminW w] with s hs
        show rdist (I := I) (M := M) p
            (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))) = ‖(d • u) + s • w‖
        rw [hccurve' s, rdist, hs, ENNReal.toReal_ofReal (norm_nonneg _)]
      -- the explicit derivatives of the norm
      have hC := ShapeAux.norm_add_smul_deriv_deriv
        (a := ((d • u) : TangentSpace I p)) (b := w) hdune
      have hC1 : deriv (fun s : ℝ => ‖(d • u) + s • w‖) 0 = Inner.inner ℝ u w := by
        have h := hC.1
        rw [real_inner_smul_left, hnormdu] at h
        rw [h]
        field_simp
        try ring
      have hC2 : HasDerivAt (deriv (fun s : ℝ => ‖(d • u) + s • w‖))
          ((‖w‖ ^ 2 - (Inner.inner ℝ u w) ^ 2) / d) 0 := by
        refine hC.2.congr_deriv ?_
        rw [hnormdu, real_inner_smul_left]
        field_simp
        try ring
      -- the first-order chain rule for the distance
      have hchain : ∀ (c' : ℝ → M),
          c' 0 = Submission.GlobalExp.GExp (cov := cov) hmet p (d • u) → MDiffAt c' 0 →
          deriv (fun s : ℝ => rdist (I := I) (M := M) p (c' s)) 0
            = Inner.inner ℝ (rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
                (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
              (Submission.Geodesic.curveVelocity (I := I) c' 0) := by
        intro c' hc'0 hmd
        have hfmd : MDiffAt (fun z : M => rdist (I := I) (M := M) p z) (c' 0) := by
          rw [hc'0]
          exact hF.mdifferentiableAt (by decide)
        have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
          (g := fun z : M => rdist (I := I) (M := M) p z) (γ := c') (t := 0) hfmd hmd
        rw [hc'0] at h
        change deriv ((fun z : M => rdist (I := I) (M := M) p z) ∘ c') 0
          = Inner.inner ℝ (rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
            (Submission.Geodesic.curveVelocity (I := I) c' 0)
        rw [← h]
        change (mfderiv% (fun z : M => rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
            (Submission.Geodesic.curveVelocity (I := I) c' 0)
          = Inner.inner ℝ (rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
            (Submission.Geodesic.curveVelocity (I := I) c' 0)
        exact (inner_rgrad (I := I) (M := M)
          (fun z : M => rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))
          (Submission.Geodesic.curveVelocity (I := I) c' 0)).symm
      -- ## 3a. route (I): the second-order chain rule
      have hrouteI : Work.Diff.C.rhess cov (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V
          + Inner.inner ℝ
              (Work.Diff.C.rgrad (I := I) (M := M)
                (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
                (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
              (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0)
          = (‖w‖ ^ 2 - (Inner.inner ℝ u w) ^ 2) / d := by
        have hA := ShapeAux.deriv_deriv_comp_curve (cov := cov) hmet htor hF
          (c := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η)))
          (by simp) (by
            intro s
            have hlin : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
                (fun s' : ℝ => (show E from (d • (u + s' • η)))) s := by
              rw [contMDiffAt_iff_contDiffAt]
              fun_prop
            exact (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p
              (d • (u + s • η))).comp s hlin)
          (by rw [hcvelL]; exact hV)
        have hA' : HasDerivAt (deriv (fun s : ℝ => Work.Diff.C.rdist (I := I) (M := M) p
              ((fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))) s)))
            (Work.Diff.C.rhess cov (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
                (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V
              + Inner.inner ℝ
                  (Work.Diff.C.rgrad (I := I) (M := M)
                    (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
                    (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
                  (Submission.JacobiGlobal.covAlong cov
                    (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                      (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                        (d • (u + s' • η))) s) 0)) 0 := by
          rw [hcvelL] at hA
          exact hA
        exact (hA'.congr_of_eventuallyEq (Filter.EventuallyEq.deriv hdistL).symm).unique hC2
      have hE : Inner.inner ℝ (rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) V = Inner.inner ℝ u w := by
        have h1 := hchain c hc0 ((hcsm.contMDiffAt).mdifferentiableAt (by simp))
        rw [← hcvel, ← h1, Filter.EventuallyEq.deriv_eq hdist, hC1]
      -- ## 3b. the endpoint velocity of `Z` is `V`
      have hZv : Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0
          = V := by
        rw [Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet d u η]
        rw [show (d • η : TangentSpace I p) = w from hdη]
        exact hw
      -- ## 3c. the gradient of the distance is the unit tangent of the ray
      set g0 : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) :=
        Submission.Geodesic.curveVelocity (I := I)
          (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) d with hg0def
      have hg0unit : ‖g0‖ = 1 := by
        rw [hg0def, Submission.GlobalExp.norm_curveVelocity_GExp_smul (cov := cov) hmet p hu0 hd, hu]
      have hgradunit : ‖rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))‖ = 1 := by
        have h : ‖rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))‖ ^ 2 = 1 := by
          rw [← real_inner_self_eq_norm_sq, hunit]
        nlinarith [norm_nonneg (rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))]
      have hinner_g0 : Inner.inner ℝ (rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) g0 = 1 := by
        have hdist2 : (fun s : ℝ => rdist (I := I) (M := M) p
              (Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + s • u)))
            =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => ‖(d • u) + s • u‖) := by
          filter_upwards [hminW u] with s hs
          rw [rdist, hs, ENNReal.toReal_ofReal (norm_nonneg _)]
        have hCu := ShapeAux.norm_add_smul_deriv_deriv
          (a := ((d • u) : TangentSpace I p)) (b := u) hdune
        have hCu1 : deriv (fun s : ℝ => ‖(d • u) + s • u‖) 0 = 1 := by
          have h := hCu.1
          rw [real_inner_smul_left, hnormdu, real_inner_self_eq_norm_sq, hu] at h
          rw [h]
          field_simp
          try ring
        have hsm2 : ContMDiff 𝓘(ℝ) I ∞
            (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + s • u)) := by
          intro s
          have hlin : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
              (fun s' : ℝ => (show E from ((d • u) + s' • u))) s := by
            rw [contMDiffAt_iff_contDiffAt]
            fun_prop
          exact (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p
            ((d • u) + s • u)).comp s hlin
        have hcv2 : Submission.Geodesic.curveVelocity (I := I)
            (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + s • u)) 0
            = g0 := by
          rw [hg0def]
          have h1 := Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation
            (cov := cov) hmet (1 : ℝ) ((d • u) : TangentSpace I p) u
          have h2 := Work.OddBound.longHomotopy.curveVelocity_GExp_ray_tangent
            (cov := cov) hmet d u
          have h1' : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                ((1 : ℝ) • ((d • u) + r • u)))
              = (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + r • u)) := by
            funext r; rw [one_smul]
          rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
            (Filter.EventuallyEq.of_eq h1')] at h1
          rw [h1, h2]
          change (mfderiv% (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p
                (show TangentSpace I p from w))) (show E from ((1 : ℝ) • (d • u))) ((1 : ℝ) • u)
              = (mfderiv% (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p
                (show TangentSpace I p from w))) (show E from (d • u)) u
          rw [show ((1 : ℝ) • (d • u) : TangentSpace I p) = (d • u) from one_smul ℝ (d • u),
            show ((1 : ℝ) • u : TangentSpace I p) = u from one_smul ℝ u]
        have hch := hchain _ (by simp) ((hsm2.contMDiffAt).mdifferentiableAt (by simp))
        rw [← hcv2, ← hch, Filter.EventuallyEq.deriv_eq hdist2, hCu1]
      have hgradEq : rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) = g0 := by
        have hsq : ‖rgrad (I := I) (fun z : M => rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) - g0‖ ^ 2 = 0 := by
          rw [norm_sub_sq_real, hgradunit, hg0unit, hinner_g0]
          norm_num
        exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq))
      -- ## 3d. the transported identities of the differentiated Gauss pairing
      have hcue : Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))
          = Submission.GlobalExp.GExp (cov := cov) hmet p (d • u) := by simp
      have hγ : Submission.Geodesic.curveVelocity (I := I)
          (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d
          = Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) := by
        rw [show (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
            = (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) from by
          funext t; simp]
        exact hgradEq.symm
      have hZsec : Submission.JacobiGlobal.covAlong cov
            (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
            (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d
          = Submission.JacobiGlobal.covAlong cov Z d := by
        rw [hZdef]
        exact covAlong_congr_curve' (cov := cov)
          (γ₁ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
          (γ₂ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
          (V₁ := fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0)
          (V₂ := fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0)
          (by funext t; simp) (by intro t; rfl) d
      -- the two transport equations in the goal's normalisation
      have hfirst : Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0)
          = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Submission.Geodesic.curveVelocity (I := I)
              (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d) := by
        have hP4 : (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) = (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) := by simp
        have hγ' : (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) = (Submission.Geodesic.curveVelocity (I := I)
              (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d) := hγ.symm
        have e1 : Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) := rfl
        have e2 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) :=
          metric_transport (E := E) (H := H) (I := I) (M := M) hP4 (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0)
        have e3 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) :=
          (metric_symm (X := (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η)))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))).symm
        have e4 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u))) = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Submission.Geodesic.curveVelocity (I := I)
              (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d) := congrArg (fun v : E => ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) v) hγ'
        have e5 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Submission.Geodesic.curveVelocity (I := I)
              (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d) = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Submission.Geodesic.curveVelocity (I := I)
              (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d) :=
          (rfl : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Submission.Geodesic.curveVelocity (I := I)
              (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d) = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
                (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                  (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                    (d • (u + s' • η))) s) 0) (Submission.Geodesic.curveVelocity (I := I)
              (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η))) d)).symm
        exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

      have hsec : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) V
          = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) (Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0) := by
        have hPB : ((fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) d) = (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) := by simp
        have hZsec' : (Submission.JacobiGlobal.covAlong cov Z d) = (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) := hZsec.symm
        have hZv' : V = (Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0) := hZv.symm
        have f1 : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) V = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner ((fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) d) (Submission.JacobiGlobal.covAlong cov Z d) V := rfl
        have f2 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner ((fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) d) (Submission.JacobiGlobal.covAlong cov Z d) V = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov Z d) V :=
          metric_transport (E := E) (H := H) (I := I) (M := M) hPB (Submission.JacobiGlobal.covAlong cov Z d) V
        have f3 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov Z d) V = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) V := congrArg (fun v : E => ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) v V) hZsec'
        have f4 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) V = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) (Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0) := congrArg (fun v : E => ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) v) hZv'
        have f5 : ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) (Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0) = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) (Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0) :=
          (rfl : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) (Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0) = ((inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g).inner (Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + (0 : ℝ) • η))) (Submission.JacobiGlobal.covAlong cov
              (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + (0 : ℝ) • η)))
              (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
                (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • (u + r • η))) 0) d) (Submission.Geodesic.curveVelocity (I := I)
              (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + r • η))) 0)).symm
        exact f1.trans (f2.trans (f3.trans (f4.trans f5)))

      -- ## 3e. the child's identity and the final combination
      have hvecη : Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (d • (u + s • η))) 0 ≠ 0 := by
        rw [hcvelL]
        exact hV
      have hB := ShapeAux.gauss_pairing_second_deriv (cov := cov) hmet htor hd hu hvecη
      have hη2 : d * Inner.inner ℝ η η = ‖w‖ ^ 2 / d := by
        rw [real_inner_self_eq_norm_sq, hηnorm]
        field_simp
        try ring
      have h3 : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) V
          = ‖w‖ ^ 2 / d
            - Inner.inner ℝ
                (Work.Diff.C.rgrad (I := I) (M := M)
                  (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
                  (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
                (Submission.JacobiGlobal.covAlong cov
                  (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                    (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                      (d • (u + s' • η))) s) 0) := by
        linarith [hB, hfirst, hsec, hη2]
      have h4 : Work.Diff.C.rhess cov (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) V V
          = (‖w‖ ^ 2 - (Inner.inner ℝ u w) ^ 2) / d
            - Inner.inner ℝ
                (Work.Diff.C.rgrad (I := I) (M := M)
                  (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
                  (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)))
                (Submission.JacobiGlobal.covAlong cov
                  (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
                    (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p
                      (d • (u + s' • η))) s) 0) := by
        linarith [hrouteI]
      rw [hE, h3, h4]
      field_simp
      try ring

end Work.Diff.C
