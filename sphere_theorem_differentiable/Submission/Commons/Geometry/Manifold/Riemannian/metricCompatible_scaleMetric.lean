import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Topology.VectorBundle.Riemannian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Geometry.Manifold.Riemannian

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Metric

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]

omit [IsManifold IM ∞ M] in
/-- **Scalar multiplication by a constant commutes with `mvfderiv`.**  Constant scaling of a
vector-valued function scales its manifold derivative; when the function is not differentiable at
the point both sides vanish, so no differentiability hypothesis is needed. -/
lemma mvfderiv_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (f : M → F) (x : M) :
    mvfderiv IM (fun y : M => c • f y) x = c • mvfderiv IM f x := by
  by_cases hf : MDifferentiableAt IM (modelWithCornersSelf ℝ F) f x
  · have hfun : (fun y : M => c • f y) = (fun _ : M => c) • f := rfl
    rw [hfun, mvfderiv_smul (mdifferentiableAt_const (c := c) (x := x)) hf, mvfderiv_const]
    simp
  · by_cases hc : c = 0
    · subst hc
      simp [mvfderiv_const]
    · have hG : ¬ MDifferentiableAt IM (modelWithCornersSelf ℝ F) (fun y : M => c • f y) x := by
        intro hh
        have h1 : MDifferentiableAt IM (modelWithCornersSelf ℝ F)
            (fun y : M => c⁻¹ • (c • f y)) x := hh.const_smul c⁻¹
        have h2 : MDifferentiableAt IM (modelWithCornersSelf ℝ F) f x :=
          h1.congr_of_eventuallyEq (by
            filter_upwards with y
            rw [smul_smul, inv_mul_cancel₀ hc, one_smul])
        exact hf h2
      rw [show mvfderiv IM (fun y : M => c • f y) x = 0 by
            simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hG],
          show mvfderiv IM f x = 0 by
            simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf],
          smul_zero]

/-- **Metric compatibility survives scaling of the fibre metric by a constant.**  Here
`CovariantDerivative IM EM (TangentSpace IM)` is Mathlib's covariant-derivative interface and
`mvfderiv` is the manifold derivative; the hypothesis `h` is exactly the statement that `cov` is
compatible with the family of inner products `g` (expansion of `mvfderiv` of an inner product as a
sum of two inner products).  Scaling `g` by a positive constant preserves it.

Hint: `HasMFDerivAt.const_smul` / `mvfderiv_const_smul` gives
`mvfderiv IM (fun y => c * F y) x v = c * mvfderiv IM F x v`, and `hinner y (Y y) (Z y)` rewrites
the integrand. -/
theorem metricCompatible_scaleMetric
    (g g' : RiemannianMetric (fun x : M => TangentSpace IM x)) {c : ℝ} (hc : 0 < c)
    (hinner : ∀ (x : M) (v w : TangentSpace IM x), g'.inner x v w = c * g.inner x v w)
    (cov : CovariantDerivative IM EM (TangentSpace IM (M := M)))
    (h : ∀ (Y Z : Π x : M, TangentSpace IM x),
          ContMDiff IM (IM.prod (modelWithCornersSelf ℝ EM)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : M => (⟨x, Y x⟩ : TotalSpace EM (TangentSpace IM))) →
          ContMDiff IM (IM.prod (modelWithCornersSelf ℝ EM)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : M => (⟨x, Z x⟩ : TotalSpace EM (TangentSpace IM))) →
          ∀ (x : M) (v : TangentSpace IM x),
            mvfderiv IM (fun y : M => g.inner y (Y y) (Z y)) x v
              = g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v)) :
    ∀ (Y Z : Π x : M, TangentSpace IM x),
      ContMDiff IM (IM.prod (modelWithCornersSelf ℝ EM)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => (⟨x, Y x⟩ : TotalSpace EM (TangentSpace IM))) →
      ContMDiff IM (IM.prod (modelWithCornersSelf ℝ EM)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => (⟨x, Z x⟩ : TotalSpace EM (TangentSpace IM))) →
      ∀ (x : M) (v : TangentSpace IM x),
        mvfderiv IM (fun y : M => g'.inner y (Y y) (Z y)) x v
          = g'.inner x (cov Y x v) (Z x) + g'.inner x (Y x) (cov Z x v) := by
  intro Y Z hY hZ x v
  have hF := h Y Z hY hZ x v
  have hkey : mvfderiv IM (fun y : M => g'.inner y (Y y) (Z y)) x v
      = c * mvfderiv IM (fun y : M => g.inner y (Y y) (Z y)) x v := by
    have hfun : (fun y : M => g'.inner y (Y y) (Z y))
        = fun y : M => c • g.inner y (Y y) (Z y) :=
      funext fun y => hinner y (Y y) (Z y)
    rw [hfun, mvfderiv_const_smul]
    simp [smul_eq_mul]
  rw [hkey, hF, hinner x (cov Y x v) (Z x), hinner x (Y x) (cov Z x v)]
  ring

end Commons.Geometry.Manifold.Riemannian