import Submission.HolDet
import Submission.Commons.LinearAlgebra.Orthogonal.fixed_vector_compl_of_det_one
import Submission.Commons.LinearAlgebra.Orthogonal.det_eq_one_of_inner_preserving_of_pos

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiTensor
open Submission.OrientSign
open Submission.ChartConnection
open Submission.BonnetMyers
open Submission.Jacobi

/-!
# The composite holonomy of a chart-covered loop: it is an isometry, it fixes the chart velocity,
and (for an even-dimensional manifold and a loop of sign `1`) it fixes a nonzero normal vector

This module continues `Submission.HolDet`.  It proves the two metric properties of the composite
holonomy `holAux` (`chartGram_holAux_loop`: it preserves the chart Gram form at the base point;
`holAux_deriv_aux`/`holAux_deriv_loop`: it fixes the chart velocity of a geodesic, given that the
velocity is periodic), and combines them with the determinant theorem
(`Submission.HolDet.sign_det_holAux`) and Synge's linear-algebra input
(`Commons.LinearAlgebra.Orthogonal.fixed_vector_compl_of_det_one`) into
`exists_fixed_normal_coord`: **for an even-dimensional manifold the holonomy of a chart-covered loop
of sign `1` fixes a nonzero coordinate vector orthogonal to the velocity** — the Synge input of the
even-dimensional Klingenberg estimate.
-/

namespace Submission.HolDet

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}

/-- **The composite holonomy preserves the chart Gram form at the base point of a closed curve.** -/
theorem chartGram_holAux_loop (hP : IsChartLoop (H := H) P γ z) (hmet : IsMetricCompatible cov)
    (hdiff : ∀ k < P.N, ∀ t ∈ Ioo (P.t k) (P.t (k+1)), HasDerivAt (coordC (I := I) (z := z) (γ := γ) k)
      (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t)
    (hγcont : ContinuousOn γ (Icc (P.t 0) (P.t P.N)))
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hloop : γ (P.t P.N) = γ (P.t 0)) (v w : E) :
    chartGram (I := I) (z 0) (γ (P.t 0))
        (holAux (cov := cov) htor hu hw htgt P.N v) (holAux (cov := cov) htor hu hw htgt P.N w)
      = chartGram (I := I) (z 0) (γ (P.t 0)) v w := by
  have h := chartGram_holAux_aux (cov := cov) hP hmet hdiff hγcont hsrc htor hu hw htgt
    P.N le_rfl v w
  rwa [hP.2.2, hloop] at h

/-- **The determinant of the composite holonomy of a chart-covered loop of sign `1` is positive.** -/
theorem det_holAux_pos (hP : IsChartLoop (H := H) P γ z)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hloopSign : loopSignOf (I := I) P γ z = 1) :
    0 < LinearMap.det ((holAux (cov := cov) htor hu hw htgt P.N).toLinearMap) := by
  have h := sign_det_holAux (cov := cov) hP htor hu hw htgt
  rw [hloopSign] at h
  by_contra hcon
  push_neg at hcon
  rw [if_neg (not_lt.mpr hcon)] at h
  norm_num at h

/-- The chart trivialisation of the tangent bundle, as a linear map. -/
noncomputable def clmC (z : M) (q : M) : TangentSpace I q →ₗ[ℝ] E :=
  ((trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ q).toLinearMap

/-- The inverse chart trivialisation of the tangent bundle, as a linear map. -/
noncomputable def frameC (z : M) (q : M) : E →ₗ[ℝ] TangentSpace I q :=
  ((trivializationAt E (TangentSpace I) z).symmL ℝ q).toLinearMap

theorem frameC_apply (z : M) (q : M) (v : E) :
    frameC (I := I) z q v = frameVector (I := I) z q v := rfl

theorem clmC_apply (z : M) (q : M) (v : TangentSpace I q) :
    clmC (I := I) z q v
      = (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ q v := rfl

theorem frameVector_inj {z : M} {q : M} (hqs : q ∈ (extChartAt I z).source) {a b : E}
    (h : frameVector (I := I) z q a = frameVector (I := I) z q b) : a = b := by
  rw [← Submission.GExpFlow.clm_frameVector (I := I) hqs a,
    ← Submission.GExpFlow.clm_frameVector (I := I) hqs b]
  exact congrArg ((trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ q) h

/-- The chart trivialisation of the tangent bundle at a point, as a linear equivalence. -/
noncomputable def frameEquiv (z : M) (q : M) (hqs : q ∈ (extChartAt I z).source) :
    E ≃ₗ[ℝ] TangentSpace I q :=
  LinearEquiv.ofLinear (frameC (I := I) z q) (clmC (I := I) z q)
    (by ext v
        show frameC (I := I) z q (clmC (I := I) z q v) = v
        rw [frameC_apply, clmC_apply]
        exact Submission.GExpFlow.frameVector_clm (I := I) hqs v)
    (by ext w
        show clmC (I := I) z q (frameC (I := I) z q w) = w
        rw [frameC_apply, clmC_apply]
        exact Submission.GExpFlow.clm_frameVector (I := I) hqs w)

theorem frameEquiv_apply (z : M) (q : M) (hqs : q ∈ (extChartAt I z).source) (v : E) :
    frameEquiv (I := I) z q hqs v = frameVector (I := I) z q v := rfl

theorem frameEquiv_symm_apply (z : M) (q : M) (hqs : q ∈ (extChartAt I z).source)
    (v : TangentSpace I q) :
    (frameEquiv (I := I) z q hqs).symm v
      = (trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ q v := rfl

/-- **The intrinsic holonomy**: the composite holonomy transported to an endomorphism of the
tangent space at the base point by the chart trivialisation. -/
noncomputable def intrHol (hqs : γ (P.t 0) ∈ (extChartAt I (z 0)).source)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) :
    TangentSpace I (γ (P.t 0)) →ₗ[ℝ] TangentSpace I (γ (P.t 0)) :=
  (frameEquiv (I := I) (z 0) (γ (P.t 0)) hqs : E →ₗ[ℝ] _) ∘ₗ
    ((holAux (cov := cov) htor hu hw htgt P.N).toLinearMap ∘ₗ
      ((frameEquiv (I := I) (z 0) (γ (P.t 0)) hqs).symm : _ →ₗ[ℝ] E))

theorem intrHol_apply (hqs : γ (P.t 0) ∈ (extChartAt I (z 0)).source) (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (v : TangentSpace I (γ (P.t 0))) :
    intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt v
      = frameVector (I := I) (z 0) (γ (P.t 0))
          (holAux (cov := cov) htor hu hw htgt P.N
            ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) v)) :=
  rfl

theorem intrHol_det (hqs : γ (P.t 0) ∈ (extChartAt I (z 0)).source) (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) :
    LinearMap.det (intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt)
      = LinearMap.det ((holAux (cov := cov) htor hu hw htgt P.N).toLinearMap) :=
  LinearMap.det_conj _ (frameEquiv (I := I) (z 0) (γ (P.t 0)) hqs)

theorem intrHol_inner (hP : IsChartLoop (H := H) P γ z) (hmet : IsMetricCompatible cov)
    (hdiff : ∀ k < P.N, ∀ t ∈ Ioo (P.t k) (P.t (k+1)), HasDerivAt (coordC (I := I) (z := z) (γ := γ) k)
      (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t)
    (hγcont : ContinuousOn γ (Icc (P.t 0) (P.t P.N)))
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hloop : γ (P.t P.N) = γ (P.t 0))
    (hqs : γ (P.t 0) ∈ (extChartAt I (z 0)).source) :
    ∀ x y : TangentSpace I (γ (P.t 0)),
      inner ℝ (intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt x)
          (intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt y)
        = inner ℝ x y := by
  intro x y
  have hclm : ∀ v : TangentSpace I (γ (P.t 0)),
      (trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) v
        = clmC (I := I) (z 0) (γ (P.t 0)) v := fun v => (clmC_apply (I := I) (z 0) (γ (P.t 0)) v).symm
  rw [intrHol_apply, intrHol_apply]
  change chartGram (I := I) (z 0) (γ (P.t 0))
      (holAux (cov := cov) htor hu hw htgt P.N
        ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) x))
      (holAux (cov := cov) htor hu hw htgt P.N
        ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) y))
    = inner ℝ x y
  rw [chartGram_holAux_loop (cov := cov) hP hmet hdiff hγcont hsrc htor hu hw htgt hloop]
  change inner ℝ
      (frameVector (I := I) (z 0) (γ (P.t 0))
        ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) x))
      (frameVector (I := I) (z 0) (γ (P.t 0))
        ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) y))
    = inner ℝ x y
  rw [Submission.GExpFlow.frameVector_clm (I := I) hqs x,
    Submission.GExpFlow.frameVector_clm (I := I) hqs y]

/-- **The chart-level transport fixes the chart velocity of a geodesic, over the whole cover.** -/
theorem holAux_deriv_aux (hP : IsChartLoop (H := H) P γ z)
    (hgeo : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      HasDerivAt (deriv (coordC (I := I) (z := z) (γ := γ) k))
        (chartGeodesicVectorField cov (z k)
          (coordC (I := I) (z := z) (γ := γ) k t,
            deriv (coordC (I := I) (z := z) (γ := γ) k) t)) t)
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (hγmd : ∀ t ∈ Icc (P.t 0) (P.t P.N), MDifferentiableAt 𝓘(ℝ) I γ t)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) :
    ∀ k, k ≤ P.N → holAux (cov := cov) htor hu hw htgt k
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
      = deriv (coordC (I := I) (z := z) (γ := γ) k) (P.t k) := by
  intro k
  refine Nat.le_induction ?_ ?_ k (Nat.zero_le k)
  · intro _
    have h0 : holAux (cov := cov) htor hu hw htgt 0 = 1 := rfl
    rw [h0, one_apply_eq_self]
  · intro m _ ih hm
    have hlt : m < P.N := by omega
    have hmem : P.t (m+1) ∈ Icc (P.t 0) (P.t P.N) :=
      ⟨P.mono_le (Nat.zero_le _) (by omega), P.mono_le (by omega) le_rfl⟩
    have hstep : chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
        ((pieceTrans (cov := cov) htor hu hw htgt m hlt)
          (deriv (coordC (I := I) (z := z) (γ := γ) m) (P.t m)))
        = deriv (coordC (I := I) (z := z) (γ := γ) (m+1)) (P.t (m+1)) := by
      rw [fundSol_velocity (cov := cov) hgeo hsrc htor hu hw htgt m hlt]
      rw [show deriv (coordC (I := I) (z := z) (γ := γ) m) (P.t (m+1))
          = deriv (fun s : ℝ => (extChartAt I (z m)) (γ s)) (P.t (m+1)) from rfl]
      rw [chartTransition_velocity (I := I) (hγmd (P.t (m+1)) hmem) (isChartLoop_junction hP hlt)]
      rfl
    rw [show holAux (cov := cov) htor hu hw htgt (m+1)
        = (chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
            * pieceTrans (cov := cov) htor hu hw htgt m hlt) * holAux (cov := cov) htor hu hw htgt m
        from by rw [holAux]; exact dif_pos hlt,
      mul_apply_eq_comp, mul_apply_eq_comp, ih (by omega), hstep]

/-- **The chart transport fixes the chart velocity when the velocity is periodic.** -/
theorem holAux_deriv_loop (hP : IsChartLoop (H := H) P γ z)
    (hgeo : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      HasDerivAt (deriv (coordC (I := I) (z := z) (γ := γ) k))
        (chartGeodesicVectorField cov (z k)
          (coordC (I := I) (z := z) (γ := γ) k t,
            deriv (coordC (I := I) (z := z) (γ := γ) k) t)) t)
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (hγmd : ∀ t ∈ Icc (P.t 0) (P.t P.N), MDifferentiableAt 𝓘(ℝ) I γ t)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hvelper : deriv (coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)) :
    holAux (cov := cov) htor hu hw htgt P.N
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0) := by
  rw [holAux_deriv_aux (cov := cov) hP hgeo hsrc hγmd htor hu hw htgt P.N le_rfl, hvelper]

/-- **Synge's linear-algebra input, ready to use**: for an even-dimensional manifold the composite
holonomy of a chart-covered loop of sign `1` fixes a nonzero vector of the chart coordinates that is
orthogonal to the coordinate velocity. -/
theorem exists_fixed_normal_coord (hP : IsChartLoop (H := H) P γ z) (hmet : IsMetricCompatible cov)
    (hdiff : ∀ k < P.N, ∀ t ∈ Ioo (P.t k) (P.t (k+1)), HasDerivAt (coordC (I := I) (z := z) (γ := γ) k)
      (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t)
    (hγcont : ContinuousOn γ (Icc (P.t 0) (P.t P.N)))
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (hgeo : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      HasDerivAt (deriv (coordC (I := I) (z := z) (γ := γ) k))
        (chartGeodesicVectorField cov (z k)
          (coordC (I := I) (z := z) (γ := γ) k t,
            deriv (coordC (I := I) (z := z) (γ := γ) k) t)) t)
    (hγmd : ∀ t ∈ Icc (P.t 0) (P.t P.N), MDifferentiableAt 𝓘(ℝ) I γ t)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hloop : γ (P.t P.N) = γ (P.t 0))
    (hvelper : deriv (coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
    (hloopSign : loopSignOf (I := I) P γ z = 1)
    (hvelne : deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0) ≠ 0)
    (hEven : Even (Module.finrank ℝ E)) :
    ∃ v : E, v ≠ 0
      ∧ chartGram (I := I) (z 0) (γ (P.t 0))
          (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)) v = 0
      ∧ holAux (cov := cov) htor hu hw htgt P.N v = v := by
  haveI : FiniteDimensional ℝ (TangentSpace I (γ (P.t 0))) := inferInstanceAs (FiniteDimensional ℝ E)
  have hqs : γ (P.t 0) ∈ (extChartAt I (z 0)).source := by
    rw [extChartAt_source]; exact isChartLoop_src_left hP (Partition.pos_N P)
  have hinner := intrHol_inner (cov := cov) hP hmet hdiff hγcont hsrc htor hu hw htgt hloop hqs
  have hfix := intrHol_det (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt
  have hdet : LinearMap.det
      (intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt) = 1 := by
    have hpos : 0 < LinearMap.det
        (intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt) := by
      rw [hfix]
      exact det_holAux_pos (cov := cov) hP htor hu hw htgt hloopSign
    exact Commons.LinearAlgebra.Orthogonal.det_eq_one_of_inner_preserving_of_pos _ hinner hpos
  have he_ne : frameVector (I := I) (z 0) (γ (P.t 0))
      (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)) ≠ 0 := by
    intro h0
    have h0' : frameVector (I := I) (z 0) (γ (P.t 0))
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
        = frameVector (I := I) (z 0) (γ (P.t 0)) (0 : E) := by
      rw [h0]
      exact (map_zero (frameC (I := I) (z 0) (γ (P.t 0)))).symm
    exact hvelne (frameVector_inj (I := I) hqs h0')
  have he_fix : intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt
      (frameVector (I := I) (z 0) (γ (P.t 0))
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)))
      = frameVector (I := I) (z 0) (γ (P.t 0))
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)) := by
    rw [intrHol_apply (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt
      (frameVector (I := I) (z 0) (γ (P.t 0))
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)))]
    rw [Submission.GExpFlow.clm_frameVector (I := I) hqs
      (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))]
    rw [holAux_deriv_loop (cov := cov) hP hgeo hsrc hγmd htor hu hw htgt hvelper]
  obtain ⟨v, hvne, hvorth, hvfix⟩ :=
    Commons.LinearAlgebra.Orthogonal.fixed_vector_compl_of_det_one
      (f := intrHol (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt)
      (hf := hinner) (hfdim := hEven)
      (e := frameVector (I := I) (z 0) (γ (P.t 0))
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)))
      (he := he_ne) (hfe := he_fix) (hdet := hdet)
  refine ⟨(trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) v,
    ?_, ?_, ?_⟩
  · intro h0
    have h1 : v = 0 := by
      rw [← Submission.GExpFlow.frameVector_clm (I := I) hqs v, h0]
      exact map_zero (frameC (I := I) (z 0) (γ (P.t 0)))
    exact hvne h1
  · rw [chartGram_apply]
    rw [show frameVector (I := I) (z 0) (γ (P.t 0))
          ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) v)
        = v from Submission.GExpFlow.frameVector_clm (I := I) hqs v]
    exact hvorth
  · have happ := intrHol_apply (cov := cov) (P := P) (z := z) (γ := γ) hqs htor hu hw htgt v
    have h1 : frameVector (I := I) (z 0) (γ (P.t 0))
        (holAux (cov := cov) htor hu hw htgt P.N
          ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0)) v))
        = v := by
      rw [← happ]
      exact hvfix
    have h2 := congrArg ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ
      (γ (P.t 0))) h1
    simpa only [Submission.GExpFlow.clm_frameVector (I := I) hqs] using h2

end

end Submission.HolDet
