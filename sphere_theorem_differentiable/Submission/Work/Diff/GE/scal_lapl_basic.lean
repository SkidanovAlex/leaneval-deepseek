import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.rot_invariance
import Submission.Work.Diff.GE.scal_lapl_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared basics for the scalar Laplacian identity `Δ scal = scalAlg (lapRmFrame)`

Elementary tools reused by `scal_lapl.lean` and `evol_scal_kit.lean`:

* `scalAlg` as a continuous linear functional `scalAlgL` and the chain rule `hasDerivAt_scalAlg_comp`;
* frame independence of the scalar curvature `scalAt g x = scalAlg (rmFrame g x e)` for any
  `g`-orthonormal frame `e` of `TₓM`;
* the algebraic curvature symmetries of `rmP` (`rmP_anti12`, `rmP_anti34`, `rmP_bian3`,
  `rmP_pair_exchange`) and hence `IsAlgCurv (rmFrame g x e)` for an *arbitrary* frame;
* locality of `laplAt` / `mvfderiv` in the germ (`mvfderiv_congr_of_eventuallyEq_real`,
  `laplAt_congr_of_eventuallyEq`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## 1. `scalAlg` as a continuous linear functional -/

/-- `scalAlg` as a linear functional on curvature arrays. -/
noncomputable def scalAlgLM (n : ℕ) : Curv4 n →ₗ[ℝ] ℝ where
  toFun := scalAlg
  map_add' R S := by simp [scalAlg, Finset.sum_add_distrib]
  map_smul' c R := by simp [scalAlg, Finset.mul_sum]

/-- `scalAlg` as a continuous linear functional on curvature arrays. -/
noncomputable def scalAlgL (n : ℕ) : Curv4 n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (scalAlgLM n)

theorem scalAlgL_apply (n : ℕ) (R : Curv4 n) : scalAlgL n R = scalAlg R := rfl

/-- The chain rule for `scalAlg`: it is linear. -/
theorem hasDerivAt_scalAlg_comp {n : ℕ} (R : ℝ → Curv4 n) (R' : Curv4 n) (t : ℝ)
    (h : HasDerivAt R R' t) : HasDerivAt (fun s ↦ scalAlg (R s)) (scalAlg R') t := by
  have hcoord : ∀ (i j k l : Fin n), HasDerivAt (fun s ↦ R s i j k l) (R' i j k l) t := by
    intro i j k l
    have h1 := hasDerivAt_pi.mp h
    have h2 := hasDerivAt_pi.mp (h1 i)
    have h3 := hasDerivAt_pi.mp (h2 j)
    exact hasDerivAt_pi.mp (h3 k) l
  have hsum : HasDerivAt (fun s ↦ ∑ i, ∑ j, R s i j i j) (∑ i, ∑ j, R' i j i j) t := by
    refine HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ?_
    refine HasDerivAt.fun_sum (u := Finset.univ) fun j _ => ?_
    exact hcoord i j i j
  simpa only [scalAlg] using hsum

/-! ## 2. Frame independence of `scalAt` -/

/-- **The scalar curvature in any orthonormal frame.**  `scalAt g x` is defined through the
`Classical.epsilon`-chosen frame `onFrame g x`; any other `g`-orthonormal frame gives the same trace
because the two frames differ by an orthogonal matrix and `scalAlg` is `rot`-invariant. -/
theorem scalAt_eq_scalAlg_rmFrame_of_isONFrame (g : SMet I M) (hLC : LCSmooth I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    scalAt g x = scalAlg (rmFrame g x e) := by
  obtain ⟨A, hA, hAe⟩ :=
    onFrame_orthogonal_change g x (onFrame g x) e (isONFrame_onFrame g x) he
  show scalAlg (rmFrame g x (onFrame g x)) = scalAlg (rmFrame g x e)
  rw [rmFrame_eq_rot hLC g x (onFrame g x) e A hAe]
  exact (rot_invariance A hA (rmFrame g x (onFrame g x))).1.symm

/-! ## 3. The curvature array of a Levi-Civita connection is algebraic -/

/-- Antisymmetry in the first pair for `rmP`. -/
theorem rmP_anti12 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u v w z : TangentSpace I x) : rmP g x u v w z + rmP g x v u w z = 0 := by
  rw [rmP_antisymm hLC g x u v w z]
  ring

/-- Skew-adjointness in the last pair for `rmP`. -/
theorem rmP_anti34 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u v w z : TangentSpace I x) : rmP g x u v w z + rmP g x u v z w = 0 := by
  rw [rmP_skew hLC g x u v w z]
  ring

/-- The first Bianchi identity for `rmP`, in the form used by the frame calculus. -/
theorem rmP_bian3 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u v w z : TangentSpace I x) :
    rmP g x u v w z + rmP g x v z w u + rmP g x z u w v = 0 := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, htor, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have h := rmVec_bianchi (lcOf g) hcov htor x u v z
  have h2 := congrArg (fun t : TangentSpace I x => g.inner x t w) h
  simp only [map_add, map_zero, zero_apply, add_apply] at h2
  simpa only [rmP] using h2

/-- **Exchange of the two pairs** for the curvature form `rmP g x a b c d = g(R(a,b)d, c)` of the
Levi-Civita connection of `g`: `rmP a b c d = rmP c d a b`.  This is the classical consequence of the
first Bianchi identity and the two antisymmetries. -/
theorem rmP_pair_exchange (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    rmP g x a b c d = rmP g x c d a b := by
  linear_combination
    (1 / 2 : ℝ) * rmP_anti12 hLC g x a c d b - (1 / 2 : ℝ) * rmP_anti12 hLC g x a d b c
    - (1 / 2 : ℝ) * rmP_anti12 hLC g x a d c b + (1 / 2 : ℝ) * rmP_anti12 hLC g x b d a c
    + (1 / 2 : ℝ) * rmP_anti34 hLC g x a b c d - (1 / 2 : ℝ) * rmP_anti34 hLC g x a c b d
    + (1 / 2 : ℝ) * rmP_anti34 hLC g x a d b c + (1 / 2 : ℝ) * rmP_anti34 hLC g x b c a d
    - (1 / 2 : ℝ) * rmP_anti34 hLC g x b d a c - (1 / 2 : ℝ) * rmP_anti34 hLC g x c d a b
    + (1 / 2 : ℝ) * rmP_bian3 hLC g x a b c d - (1 / 2 : ℝ) * rmP_bian3 hLC g x a b d c
    + (1 / 2 : ℝ) * rmP_bian3 hLC g x a c b d - (1 / 2 : ℝ) * rmP_bian3 hLC g x b c a d

/-- The curvature components of the Levi-Civita connection of `g` in an *arbitrary* frame satisfy
the algebraic curvature identities. -/
theorem isAlgCurv_rmFrame_kit (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) : IsAlgCurv (rmFrame g x e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    show rmP g x (e j) (e i) (e k) (e l) = -rmP g x (e i) (e j) (e k) (e l)
    rw [rmP_antisymm hLC g x (e j) (e i) (e k) (e l)]
  · intro i j k l
    show rmP g x (e k) (e l) (e i) (e j) = rmP g x (e i) (e j) (e k) (e l)
    exact rmP_pair_exchange hLC g x (e k) (e l) (e i) (e j)
  · intro i j k l
    show rmP g x (e i) (e j) (e k) (e l) + rmP g x (e j) (e k) (e i) (e l)
      + rmP g x (e k) (e i) (e j) (e l) = 0
    linear_combination
      rmP_anti12 hLC g x (e i) (e k) (e j) (e l) + rmP_anti12 hLC g x (e i) (e k) (e l) (e j)
      + rmP_anti34 hLC g x (e i) (e j) (e k) (e l) - rmP_anti34 hLC g x (e i) (e k) (e j) (e l)
      + rmP_anti34 hLC g x (e j) (e k) (e i) (e l) - rmP_bian3 hLC g x (e i) (e j) (e l) (e k)

/-! ## 4. Locality of `laplAt` -/

open Filter in
/-- `mvfderiv` of `ℝ`-valued functions respects eventual equality.  (The library version
`Submission.ChartCurv.mvfderiv_congr_of_eventuallyEq` is stated for functions into the *model*
space `E`.) -/
theorem mvfderiv_congr_of_eventuallyEq_real {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- `laplAt g · x` only depends on the germ of the function at `x`. -/
theorem laplAt_congr_of_eventuallyEq (g : SMet I M) {u v : M → ℝ} (x : M)
    (h : u =ᶠ[𝓝 x] v) : laplAt g u x = laplAt g v x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmem : {z : M | u z = v z} ∈ 𝓝 x := h
  have hx : x ∈ interior {z : M | u z = v z} := mem_interior_iff_mem_nhds.mpr hmem
  have hinner : ∀ w : TangentSpace I x,
      (fun y : M ↦ mvfderiv I u y (smoothExt x w y))
        =ᶠ[𝓝 x] (fun y : M ↦ mvfderiv I v y (smoothExt x w y)) := by
    intro w
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    have hy' : u =ᶠ[𝓝 y] v :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
    rw [mvfderiv_congr_of_eventuallyEq_real hy']
  simp only [laplAt, hessAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : mvfderiv I (fun y : M ↦ mvfderiv I u y (smoothExt x (onFrame g x i) y)) x
      = mvfderiv I (fun y : M ↦ mvfderiv I v y (smoothExt x (onFrame g x i) y)) x :=
    mvfderiv_congr_of_eventuallyEq_real (hinner (onFrame g x i))
  have h2 : mvfderiv I u x = mvfderiv I v x :=
    mvfderiv_congr_of_eventuallyEq_real h
  rw [h1, h2]


end Work.Diff.GE
