import ChallengeDeps
import Mathlib

/-!
# In a chart, the Riemannian metric is a smooth symmetric positive family of bilinear forms

Task: prove the final theorem `chart_metric` (fill in the proof).

## Setting (the challenge hypotheses)

    {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

`TangentSpace I x` is a (non-reducible) type synonym for `E`, so an element `u : E` can be used
as an element of any fibre via `(u : TangentSpace I x)`.  The fibre inner products come from

    (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)) :
          RiemannianMetric (fun x : M => TangentSpace I x)

whose field `.inner x : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` is a continuous
bilinear form on the fibre; it satisfies `.symm x u v : inner x u v = inner x v u` and
`.pos x v hv : 0 < inner x v v` for `v ≠ 0`.  Use these directly — do NOT rely on the
`InnerProductSpace`/`Inner` typeclass on the fibre (instance synthesis on the irreducible
`TangentSpace I x` fails in this snapshot).

## Goal

Prove that on a neighbourhood of `φ p := extChartAt I p p`, the metric tensor in coordinates is
a smooth, symmetric, positive definite family of bilinear forms agreeing with the fibre inner
products:

    ∃ U : Set E, (extChartAt I p p) ∈ U ∧ IsOpen U ∧
      ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ,
        (∀ q : E × E × E, q.1 ∈ U →
           ContDiffAt ℝ 3 (fun y : E => ((g y) q.2.1) q.2.2) q.1) ∧   -- smoothness of evaluations
        (∀ y ∈ U, ∀ u v : E, (g y) u v = (g y) v u) ∧
        (∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < (g y) v v) ∧
        (∀ y ∈ U, ∀ u v : E,
           (g y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                         ((extChartAt I p).symm y)
                         (u : TangentSpace I ((extChartAt I p).symm y))
                         (v : TangentSpace I ((extChartAt I p).symm y)))

(If the pointwise-smoothness clause is awkward, you may instead prove `ContDiffOn ℝ 3 g U` where
`g : E → E →L[ℝ] E →L[ℝ] ℝ` and the codomain carries its normed-space structure.)

## Proof route

1. Define the chart metric `g y := (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner ((extChartAt I p).symm y)` coerced to `E →L E →L ℝ` (definitionally valid since `TangentSpace I x = E`).  Symmetry and positivity come from `.symm`/`.pos` of the bundle metric.
2. **Smoothness**: fix `u v : E`.  The function `y ↦ (g y) u v` equals, along the chart
   diffeomorphism, `m ↦ inner m (u : TangentSpace I m) (v : TangentSpace I m)` composed with the
   chart inverse.  Show `m ↦ inner m u_m v_m` is `ContMDiffAt I ∞ p` by:
   * the sections `m ↦ TotalSpace.mk' E m (u : TangentSpace I m)` and similarly `v` are
     ContMDiffAt: use `Mathlib/Geometry/Manifold/VectorBundle/Basic.lean`,
     `contMDiffAt_section_iff` with `e := trivializationAt E (TangentSpace I) p`
     (`[MemTrivializationAtlas]` holds for the tangent bundle): the section is smooth iff its
     trivialized coordinates are smooth; for the tangent bundle those coordinates are the
     transition derivatives applied to the constant `u`, smooth in `m` because the manifold is
     `C^∞` (`IsManifold I ∞ M`); alternatively use existing lemmas for the tangent bundle if any.
   * apply `ContMDiffAt.inner_bundle` (in `Geometry/Manifold/VectorBundle/Riemannian.lean`) to
     these two sections to get `ContMDiffAt I ∞ (fun m => ⟪u_m, v_m⟫) p`, where `⟪·,·⟫` is the
     bundle inner product (equal to `.inner m` by `IsContMDiffRiemannianBundle`'s content or by
     definition of the inner product on the fibres — reconcile via
     `RiemannianBundle`/`RiemannianMetric`; if `inner` notation is unavailable, restate with the
     bundle metric `.inner` directly by copying the proof of `ContMDiffAt.inner_bundle`).
   * compose with the chart inverse `(extChartAt I p).symm` (a ContMDiffAt map into `M`) to get
     `ContDiffAt ℝ ∞ (fun y => (g y) u v) (extChartAt I p p)` (in the model, `ContMDiffAt` with
     chart model reduces to `ContDiffAt`; `contMDiffAt_iff_contDiffAt`-type lemmas).
   * restrict to a neighbourhood and lower the smoothness from `∞` to `3`.
3. Package into the theorem (choose `U := (extChartAt I p).target ∩ ball (extChartAt I p p) r`
   for small `r`, or any open set where the above holds).

Do NOT change the statement of `chart_metric`.  You may add helper definitions/lemmas.  No placeholders or axioms may remain.
-/

open scoped Manifold ContDiff Bundle Topology
open Set Bundle ContinuousLinearMap

namespace Submission

open LeanEval.Geometry

noncomputable section

/-! ## Local machinery

All statements below refer to the manifold `M` modelled on `I : ModelWithCorners ℝ E H`
(`[I.Boundaryless]`, `[IsManifold I ∞ M]`) whose tangent bundle `x ↦ TangentSpace I x` is
equipped with a `C^∞` Riemannian structure (`[IsContMDiffRiemannianBundle I ∞ E …]`, fibre
scalar products given by `Bundle.RiemannianBundle.g`).  The extended chart at a point `p` is
`φ := extChartAt I p : PartialEquiv M E`, and `e := trivializationAt E (TangentSpace I) p` is the
tangent-bundle trivialisation over the chart domain.  For `m` in the chart the linear map
`e.symmL ℝ m : E →L[ℝ] TangentSpace I m` is the coordinate-frame map: it sends a coordinate
vector `u` to the tangent vector at `m` whose trivialised coordinates are constantly `u`.  By
`TangentBundle.symmL_trivializationAt` this is exactly `mfderiv[range I] φ.symm (φ m)`, the
derivative of the inverse chart.
-/

/-- Pullback of a bilinear form along a linear map. -/
def pull {C A : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (B : A →L[ℝ] (A →L[ℝ] ℝ)) (T : C →L[ℝ] A) : C →L[ℝ] (C →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ C A ℝ).flip T).comp (B.comp T)

@[simp]
lemma pull_apply {C A : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (B : A →L[ℝ] (A →L[ℝ] ℝ)) (T : C →L[ℝ] A) (u v : C) :
    (pull B T u) v = B (T u) (T v) := by
  simp [pull]

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- For `m` in the chart domain at `p`, the section `m ↦ ⟨m, e.symmL ℝ m u⟩` (tangent vectors
with constant trivialised coordinates `u`) is `C^∞` at `m₀`. -/
lemma chartSect_contMDiffAt (p : M) {m0 : M} (hm0 : m0 ∈ (extChartAt I p).source) (u : E) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun m : M => (TotalSpace.mk' E m ((trivializationAt E (TangentSpace I) p).symmL ℝ m u) :
        Bundle.TotalSpace E (fun x : M => TangentSpace I x))) m0 := by
  let e : Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E (fun x : M => TangentSpace I x) → M)
    := trivializationAt E (TangentSpace I) p
  let s : (x : M) → (fun x : M => TangentSpace I x) x := fun m => e.symmL ℝ m u
  have he : m0 ∈ e.baseSet := by
    simpa [e, s, extChartAt_source] using hm0
  have heq : (fun m : M => (e ⟨m, s m⟩).2) =ᶠ[𝓝 m0] (fun _ : M => (u : E)) := by
    filter_upwards [e.open_baseSet.mem_nhds he] with m hm
    simp only [s]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (e := e) hm]
    exact Trivialization.continuousLinearMapAt_symmL (R := ℝ) (e := e) hm u
  have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun _ : M => (u : E)) m0 := contMDiffAt_const
  have hcoord : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun m : M => (e ⟨m, s m⟩).2) m0 :=
    hc.congr_of_eventuallyEq heq
  exact (Bundle.Trivialization.contMDiffAt_section_iff (s := s) (e := e) he).mpr hcoord

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]

/-- The fibre scalar product (given by the `RiemannianBundle` data) equals the scalar product of
`ContMDiffAt.inner_bundle`, so the inner product of two tangent vectors at `m` is the smooth
evaluation of the family `m ↦ inner m`. -/
lemma fibreInner_eq (m : M) (v w : TangentSpace I m) :
    (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner m v w = inner ℝ v w :=
  rfl

/-- The `J`-map `m ↦ inner m (e.symmL m u) (e.symmL m v)` is `C^∞` at each point of the chart
domain, where `e := trivializationAt E (TangentSpace I) p`. -/
lemma chartInner_contMDiffAt (p : M) {m0 : M} (hm0 : m0 ∈ (extChartAt I p).source) (u v : E) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun m : M => ((Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner m)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m u)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m v)) m0 := by
  let e : Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E (fun x : M => TangentSpace I x) → M)
    := trivializationAt E (TangentSpace I) p
  let su : (x : M) → (fun x : M => TangentSpace I x) x := fun m => e.symmL ℝ m u
  let sv : (x : M) → (fun x : M => TangentSpace I x) x := fun m => e.symmL ℝ m v
  have hsu : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun m : M => (TotalSpace.mk' E m (e.symmL ℝ m u) :
        Bundle.TotalSpace E (fun x : M => TangentSpace I x))) m0 := by
    simpa [e] using chartSect_contMDiffAt (I := I) (M := M) p hm0 u
  have hsv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun m : M => (TotalSpace.mk' E m (e.symmL ℝ m v) :
        Bundle.TotalSpace E (fun x : M => TangentSpace I x))) m0 := by
    simpa [e] using chartSect_contMDiffAt (I := I) (M := M) p hm0 v
  have h := ContMDiffAt.inner_bundle (IB := I) (n := ∞) (F := E)
    (E := fun x : M => TangentSpace I x) (b := fun m : M => m)
    (v := su) (w := sv) (x := m0) hsu hsv
  -- h : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun b => inner ℝ (su b) (sv b)) m0
  -- The fibre inner product (from the `RiemannianBundle` instance) is exactly `g.inner`, so `h`
  -- is the smoothness statement we need.
  have hg : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun m : M => ((Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner m)
         (su m) (sv m)) m0 := by
    convert h using 1
    ext m
    exact fibreInner_eq (I := I) (M := M) m (su m) (sv m)
  simpa [e, su, sv, Bundle.RiemannianBundle.g] using hg

/-- In the chart target, `symmL` of the tangent trivialisation at `p` is the manifold derivative
of the inverse chart (both have the coordinate vector as input). -/
lemma chart_lm_eq_mfderiv (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    (trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y) =
      mfderiv[range I] (extChartAt I p).symm y := by
  let φ := extChartAt I p
  have hmem : φ.symm y ∈ (chartAt H p).source := by
    have hsrc : φ.symm y ∈ φ.source := φ.map_target hy
    simpa [φ, extChartAt_source] using hsrc
  have hL := TangentBundle.symmL_trivializationAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (x₀ := p) (x := φ.symm y) hmem
  rw [PartialEquiv.right_inv (extChartAt I p) hy] at hL
  simpa [φ] using hL

/-- In coordinates (over the chart target) the evaluations of the pulled-back metric are `C^∞`. -/
lemma chartEval_contDiffAt (p : M) {y0 : E} (hy0 : y0 ∈ (extChartAt I p).target) (u v : E) :
    ContDiffAt ℝ ∞
      (fun y : E => ((Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
         ((extChartAt I p).symm y))
         ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y) u)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y) v)) y0 := by
  let φ := extChartAt I p
  let m0 : M := φ.symm y0
  have hm0 : m0 ∈ (extChartAt I p).source := by
    exact (φ.map_target hy0)
  have hJ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun m : M => ((Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner m)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m u)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m v)) m0 := by
    exact chartInner_contMDiffAt (I := I) (M := M) p hm0 u v
  have hSymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (fun y : E => (extChartAt I p).symm y)
      (extChartAt I p).target y0 := by
    exact contMDiffWithinAt_extChartAt_symm_target (I := I) (n := ∞) p hy0
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      ((fun m : M => ((Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner m)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m u)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m v)) ∘ (extChartAt I p).symm)
      (extChartAt I p).target y0 := by
    exact ContMDiffAt.comp_contMDiffWithinAt (x := y0) hJ hSymm
  have hcd : ContDiffWithinAt ℝ ∞
      ((fun m : M => ((Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner m)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m u)
         ((trivializationAt E (TangentSpace I) p).symmL ℝ m v)) ∘ (extChartAt I p).symm)
      (extChartAt I p).target y0 := by
    exact (contMDiffWithinAt_iff_contDiffWithinAt (𝕜 := ℝ)).mp hcomp
  exact hcd.contDiffAt ((isOpen_extChartAt_target (I := I) p).mem_nhds hy0)

/-- In a chart, the Riemannian metric is a smooth symmetric positive family of bilinear forms
agreeing with the fibre inner product of the bundle. -/
theorem chart_metric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (p : M) :
    ∃ U : Set E, (extChartAt I p p) ∈ U ∧ IsOpen U ∧
      ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ,
        (∀ q : E × E × E, q.1 ∈ U →
           ContDiffAt ℝ 3 (fun y : E => ((g y) q.2.1) q.2.2) q.1) ∧
        (∀ y ∈ U, ∀ u v : E, (g y) u v = (g y) v u) ∧
        (∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < (g y) v v) ∧
        (∀ y ∈ U, ∀ u v : E,
           (g y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                         ((extChartAt I p).symm y)
                         ((mfderiv[range I] (extChartAt I p).symm y) u)
                         ((mfderiv[range I] (extChartAt I p).symm y) v)) := by
  let φ := extChartAt I p
  let e : Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E (fun x : M => TangentSpace I x) → M)
    := trivializationAt E (TangentSpace I) p
  let gmetric := Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)
  let g : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun y : E => pull (gmetric.inner (φ.symm y)) (e.symmL ℝ (φ.symm y))
  refine ⟨(extChartAt I p).target, mem_extChartAt_target p,
    isOpen_extChartAt_target (I := I) p, g, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hE : ContDiffAt ℝ (3 : ℕ∞ω)
        (fun y : E => ((Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
           ((extChartAt I p).symm y))
           ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y) q.2.1)
           ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y) q.2.2)) q.1 := by
      exact ContDiffAt.of_le (chartEval_contDiffAt (I := I) (M := M) p hq q.2.1 q.2.2)
        (ENat.LEInfty.out (m := (3 : ℕ∞ω)))
    exact hE
  · intro y hy u v
    simpa [g] using (gmetric.symm (φ.symm y) (e.symmL ℝ (φ.symm y) u) (e.symmL ℝ (φ.symm y) v))
  · intro y hy v hv
    have hm_e : φ.symm y ∈ e.baseSet := by
      have hsrc : φ.symm y ∈ φ.source := φ.map_target hy
      simpa [φ, e, extChartAt_source] using hsrc
    have hTv : e.symmL ℝ (φ.symm y) v ≠ 0 := by
      intro hz
      have h1 := Trivialization.continuousLinearMapAt_symmL (R := ℝ) (e := e) hm_e v
      rw [hz] at h1
      have hz' : (0 : E) = v := by simpa using h1
      exact hv hz'.symm
    simpa [g] using (gmetric.pos (φ.symm y) (e.symmL ℝ (φ.symm y) v) hTv)
  · intro y hy u v
    have hL := chart_lm_eq_mfderiv (I := I) (M := M) p hy
    simp [g]
    rw [hL]
    rfl

end

end

end Submission
