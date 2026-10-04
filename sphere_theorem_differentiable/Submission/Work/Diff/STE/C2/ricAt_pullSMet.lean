/-
# The Ricci tensor of a pull-back metric (Layer C2, DeTurck trick)

`Work.Diff.STE.C2.ricAt_pullSMet`: the Ricci tensor of the pull-back `φ*g` of a smooth metric `g`
along a diffeomorphism `φ` is the pull-back of the Ricci tensor:

`ricAt (lcOf (φ*g)) x u v = ricAt (lcOf g) (φ x) (dφ_x u) (dφ_x v)`.

Route.  `ricAt cov x u v` is the trace (in the canonical basis of `E`) of the endomorphism
`w ↦ R(w,u)v` of `T_xM`; and the curvature of the pull-back connection is the pull-back of the
curvature (`curv_pullCov_naturality`).  The main points of the formalisation are

* `pullCov_torsion_eq_zero`: the pull-back of a torsion-free connection is torsion-free;
* `lcOf_pullSMet_apply`: `pullCov φ (lcOf g)` agrees with the Levi-Civita connection of `φ*g` on
  differentiable fields — both are Levi-Civita for the pull-back metric (`IsLeviCivitaConnection`
  from torsion-freeness plus `pullCov_metric_compat`, and Mathlib's
  `isLeviCivitaConnection_leviCivitaConnection`), so `IsLeviCivitaConnection.uniqueness` applies;
* `curv_lcOf_pullSMet`: consequently `curv (lcOf (φ*g))` is the pull-back of `curv (lcOf g)`;
* `sum_coord_finBasis_eq_trace`: the canonical sum `∑ i, coord i (X (b i))` is `LinearMap.trace`,
  so the conjugacy `D ∘ L = id` of `dφ_x` and `d(φ⁻¹)_{φ x}` gives the invariance of the trace.
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Defs
import Submission.Work.Diff.STE.C2.PullCovAux
import Submission.Work.Diff.STE.C2.pullCov_leibniz
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.curvbasic
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
import Submission.Curvature
import Submission.Work.Diff.STE.C2.curv_pullCov_naturality
import Submission.Work.Diff.STE.C2.pullCov_metric_compat

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] [T2Space M]

/-! ## The torsion of the pulled-back connection -/

theorem pullCov_torsion_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞))
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (htor : cov.torsion = 0) :
    (Work.Diff.STE.C2.pullCov φ cov).torsion = 0 := by
  funext x
  ext a b
  exact pullCov_torsion_zero_aux φ cov htor (pullCov_isCovariantDerivative φ cov) x a b

/-! ## The trace of an endomorphism from its matrix in `finBasis` -/

theorem sum_coord_finBasis_eq_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : E →ₗ[ℝ] E) :
    ∑ i, (Module.finBasis ℝ E).coord i (X ((Module.finBasis ℝ E) i))
      = LinearMap.trace ℝ E X := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ E) X]
  simp only [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]


/-! ## The Levi-Civita connection of the pull-back metric -/

theorem lcOf_pullSMet_apply (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (g : Submission.Diff.SMet I M)
    (Y : Π x : M, TangentSpace I x) (x : M)
    (hY : MDifferentiableAt I I.tangent (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)) x) :
    (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Y x
      = Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) Y x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(Work.Diff.STE.C2.pullSMet φ g).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  have h1 : (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)).IsLeviCivitaConnection := by
    simp only [Submission.Diff.lcOf]
    exact CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I
  have htor : (Submission.Diff.lcOf g).torsion = 0 := by
    simpa using (Work.Diff.T.lc_smooth (I := I) (M := M) g).2.1
  have hmet : (Work.Diff.STE.C2.pullCov φ (Submission.Diff.lcOf g)).IsMetricCompatible
      (M := M) (V := TangentSpace I) := by
    rw [CovariantDerivative.isMetricCompatible_iff]
    intro x X σ τ hX hσ hτ
    exact pullCov_metric_compat φ g σ τ x hσ hτ (X x)
  have h2 : (Work.Diff.STE.C2.pullCov φ (Submission.Diff.lcOf g)).IsLeviCivitaConnection :=
    ⟨hmet, pullCov_torsion_eq_zero φ (Submission.Diff.lcOf g) htor⟩
  have hkey := CovariantDerivative.IsLeviCivitaConnection.uniqueness I h1 h2 hY
  exact ContinuousLinearMap.ext (fun X₀ => hkey X₀)

/-! ## The curvature of the pull-back Levi-Civita connection -/

theorem curv_lcOf_pullSMet (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (g : Submission.Diff.SMet I M)
    (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) X Y Z x
      = mfderiv I I (φ.symm : M → M) (φ x)
          (curv (Submission.Diff.lcOf g) (Work.Diff.STE.C2.pushField φ X)
            (Work.Diff.STE.C2.pushField φ Y) (Work.Diff.STE.C2.pushField φ Z) (φ x)) := by
  haveI hcovh : ContMDiffCovariantDerivative
      (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) ∞ :=
    (Work.Diff.T.lc_smooth (I := I) (M := M) (Work.Diff.STE.C2.pullSMet φ g)).1.some
  have hXmd : MDifferentiableAt I I.tangent
      (fun y : M ↦ (⟨y, X y⟩ : TangentBundle I M)) x := (hX x).mdifferentiableAt (by simp)
  have hYmd : MDifferentiableAt I I.tangent
      (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)) x := (hY x).mdifferentiableAt (by simp)
  have hZmd : MDifferentiableAt I I.tangent
      (fun y : M ↦ (⟨y, Z y⟩ : TangentBundle I M)) x := (hZ x).mdifferentiableAt (by simp)
  -- the two composed sections
  have hsec1 : CMDiff ∞ (T% (fun y : M ↦ (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Z y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply _ hcovh hZ hY
  have hsec2 : CMDiff ∞ (T% (fun y : M ↦ (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Z y (X y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply _ hcovh hZ hX
  -- the pointwise equality of the two connections on every smooth section
  have eZ : (fun y : M ↦ (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Z y)
      = (fun y : M ↦ Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) Z y) := by
    funext y
    exact lcOf_pullSMet_apply φ g Z y ((hZ y).mdifferentiableAt (by simp))
  have e1 : (fun y : M ↦ (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Z y (Y y))
      = (fun y : M ↦ Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) Z y (Y y)) := by
    funext y; rw [congrFun eZ y]
  have e2 : (fun y : M ↦ (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Z y (X y))
      = (fun y : M ↦ Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) Z y (X y)) := by
    funext y; rw [congrFun eZ y]
  have hconv : curv (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) X Y Z x
      = curv (Work.Diff.STE.C2.pullCov φ (Submission.Diff.lcOf g)) X Y Z x := by
    have h1 := lcOf_pullSMet_apply φ g
      (fun y : M ↦ (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Z y (Y y)) x
      ((hsec1 x).mdifferentiableAt (by simp))
    have h2 := lcOf_pullSMet_apply φ g
      (fun y : M ↦ (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) Z y (X y)) x
      ((hsec2 x).mdifferentiableAt (by simp))
    have h3 := lcOf_pullSMet_apply φ g Z x hZmd
    simp only [LeanEval.Geometry.SphereTheorem.curv]
    rw [h1, h2, h3, e1, e2]
    simp only [Work.Diff.STE.C2.pullCov_apply]
  rw [hconv]
  exact curv_pullCov_naturality φ (Submission.Diff.lcOf g) X Y Z x hXmd hYmd

/-! ## The Ricci tensor of the pull-back metric -/

theorem ricAt_pullSMet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (g : Submission.Diff.SMet I M)
    (x : M) (u v : TangentSpace I x) :
    Submission.Diff.ricAt (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) x u v
      = Submission.Diff.ricAt (Submission.Diff.lcOf g) (φ x)
          (mfderiv I I (φ : M → M) x u) (mfderiv I I (φ : M → M) x v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(Work.Diff.STE.C2.pullSMet φ g).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI hcovh : ContMDiffCovariantDerivative
      (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) ∞ :=
    (Work.Diff.T.lc_smooth (I := I) (M := M) (Work.Diff.STE.C2.pullSMet φ g)).1.some
  have hcovg : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ :=
    (Work.Diff.T.lc_smooth (I := I) (M := M) g).1.some
  -- the linear maps
  let Dfun : TangentSpace I x →L[ℝ] TangentSpace I (φ x) := mfderiv I I (φ : M → M) x
  let Lfun : TangentSpace I (φ x) →L[ℝ] TangentSpace I x :=
    mfderiv I I (φ.symm : M → M) (φ x)
  let D : E →ₗ[ℝ] E := Dfun.toLinearMap
  let L : E →ₗ[ℝ] E := Lfun.toLinearMap
  have hDL : D.comp L = LinearMap.id := by
    ext w
    show mfderiv I I (φ : M → M) x (mfderiv I I (φ.symm : M → M) (φ x) w) = w
    exact mfderiv_apply_mfderiv_symm_self φ x w
  let A : E →ₗ[ℝ] E :=
    { toFun := fun w => Submission.Diff.rmVec (Submission.Diff.lcOf g) (φ x) w (D u) (D v)
      map_add' := fun a b => by
        simpa using Work.Diff.GE.rmVec_add_left (Submission.Diff.lcOf g) hcovg (φ x) a b
          (D u) (D v)
      map_smul' := fun c a => by
        simpa using Work.Diff.GE.rmVec_smul_left (Submission.Diff.lcOf g) hcovg (φ x) c a
          (D u) (D v) }
  let B : E →ₗ[ℝ] E :=
    { toFun := fun w => Submission.Diff.rmVec
        (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) x w u v
      map_add' := fun a b => by
        simpa using Work.Diff.GE.rmVec_add_left
          (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) hcovh x a b u v
      map_smul' := fun c a => by
        simpa using Work.Diff.GE.rmVec_smul_left
          (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) hcovh x c a u v }
  -- the vector-level naturality
  have hkey : ∀ w : E, B w = L (A (D w)) := by
    intro w
    have h2 : curv (Submission.Diff.lcOf g)
        (Work.Diff.STE.C2.pushField φ (Submission.Diff.smoothExt x w))
        (Work.Diff.STE.C2.pushField φ (Submission.Diff.smoothExt x u))
        (Work.Diff.STE.C2.pushField φ (Submission.Diff.smoothExt x v)) (φ x) = A (D w) := by
      rw [Submission.Curvature.curv_eq_of_apply_eq (Submission.Diff.lcOf g) hcovg
        (Work.Diff.STE.C2.pushField_contMDiff φ (Submission.Diff.smoothExt x w)
          (Work.Diff.GE.smoothExt_cmdiff x w))
        (Work.Diff.GE.smoothExt_cmdiff (φ x) (D w))
        (Work.Diff.STE.C2.pushField_contMDiff φ (Submission.Diff.smoothExt x u)
          (Work.Diff.GE.smoothExt_cmdiff x u))
        (Work.Diff.GE.smoothExt_cmdiff (φ x) (D u))
        (Work.Diff.STE.C2.pushField_contMDiff φ (Submission.Diff.smoothExt x v)
          (Work.Diff.GE.smoothExt_cmdiff x v))
        (Work.Diff.GE.smoothExt_cmdiff (φ x) (D v))
        (by rw [Work.Diff.STE.C2.pushField_apply_self, Work.Diff.GE.smoothExt_apply,
              Work.Diff.GE.smoothExt_apply]; rfl)
        (by rw [Work.Diff.STE.C2.pushField_apply_self, Work.Diff.GE.smoothExt_apply,
              Work.Diff.GE.smoothExt_apply]; rfl)
        (by rw [Work.Diff.STE.C2.pushField_apply_self, Work.Diff.GE.smoothExt_apply,
              Work.Diff.GE.smoothExt_apply]; rfl)]
      rfl
    show Submission.Diff.rmVec (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g))
        x w u v = L (A (D w))
    rw [show Submission.Diff.rmVec (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g))
          x w u v
        = curv (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g))
            (Submission.Diff.smoothExt x w) (Submission.Diff.smoothExt x u)
            (Submission.Diff.smoothExt x v) x from rfl]
    rw [curv_lcOf_pullSMet φ g (Submission.Diff.smoothExt x w)
        (Submission.Diff.smoothExt x u) (Submission.Diff.smoothExt x v) x
        (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_cmdiff x u)
        (Work.Diff.GE.smoothExt_cmdiff x v)]
    rw [h2]
    rfl
  -- trace step
  have hA : Submission.Diff.ricAt (Submission.Diff.lcOf g) (φ x)
        (mfderiv I I (φ : M → M) x u) (mfderiv I I (φ : M → M) x v)
      = ∑ i, (Module.finBasis ℝ E).coord i (A ((Module.finBasis ℝ E) i)) := rfl
  have hB : Submission.Diff.ricAt
        (Submission.Diff.lcOf (Work.Diff.STE.C2.pullSMet φ g)) x u v
      = ∑ i, (Module.finBasis ℝ E).coord i (B ((Module.finBasis ℝ E) i)) := rfl
  have htr : LinearMap.trace ℝ E B = LinearMap.trace ℝ E A := by
    have h1 : B = L.comp (A.comp D) := LinearMap.ext (fun w => hkey w)
    rw [h1, LinearMap.trace_comp_comm' (A.comp D) L, LinearMap.comp_assoc, hDL,
      LinearMap.comp_id]
  have hsum : ∑ i, (Module.finBasis ℝ E).coord i (B ((Module.finBasis ℝ E) i))
      = ∑ i, (Module.finBasis ℝ E).coord i (A ((Module.finBasis ℝ E) i)) := by
    rw [sum_coord_finBasis_eq_trace B, htr, ← sum_coord_finBasis_eq_trace A]
  rw [hB, hsum, ← hA]

end Work.Diff.STE.C2
