import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.HessLowerKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C: auxiliary lemmas for the lower Hessian comparison

Self-contained facts used by `Work.Diff.C.hess_lower_v2`:

* `Work.Diff.C.curvLe_of_pinched` — the frozen `Pinched cov κ Λ` implies the pointwise upper
  curvature bound `RauchK.CurvLe cov Λ`;
* `Work.Diff.C.rdist_GExp_smul_le` — the distance from `x` to a point of the ray `t ↦ GExp x (t • v)`
  is at most `t‖v‖`;
* `Work.Diff.C.lipschitz_mvfderiv_le'` — the derivative of a `1`-Lipschitz function is bounded by
  `1` (a self-contained copy of `Work.Diff.C.lipschitz_mvfderiv_le`, written with this file's
  import set so that it can be used together with `Work.Diff.C.hess_dist_jacobi_shapeOp`).
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E]

/-- The frozen pinching predicate `Pinched cov κ Λ` implies the pointwise upper curvature bound
`RauchK.CurvLe cov Λ`. -/
theorem curvLe_of_pinched {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] {κ Λ : ℝ} (h : Pinched cov κ Λ) :
    Submission.RauchK.CurvLe cov Λ := by
  intro x u v hu hv huv
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  have h1 : Inner.inner ℝ (X x) (X x) = 1 := by
    rw [hXx, real_inner_self_eq_norm_sq, hu]; norm_num
  have h2 : Inner.inner ℝ (Y x) (Y x) = 1 := by
    rw [hYx, real_inner_self_eq_norm_sq, hv]; norm_num
  have h3 : Inner.inner ℝ (X x) (Y x) = 0 := by rw [hXx, hYx]; exact huv
  have hle := (h X Y hX hY x h1 h2 h3).2
  rw [← hXx, ← hYx]
  rw [Submission.CurvatureVec.curvVec_eq (cov := cov) (hcov := inferInstance) (x := x)
    (u := X x) (v := Y x) (w := Y x) hX hY hY rfl rfl rfl]
  exact hle

/-- **The distance from the base point to its own ray**: `d(x, GExp x (t • v)) ≤ t · ‖v‖` for
`t ≥ 0`. -/
theorem rdist_GExp_smul_le {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (x : M)
    (v : TangentSpace I x) {t : ℝ} (ht : 0 ≤ t) :
    rdist (I := I) x (Submission.GlobalExp.GExp (cov := cov) hmet x (t • v)) ≤ t * ‖v‖ := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    rw [smul_zero, Submission.GlobalExp.GExp_zero, norm_zero, mul_zero, rdist,
      Manifold.riemannianEDist_self, ENNReal.toReal_zero]
  · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hη : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ hnv]
    have hsm : t • v = (t * ‖v‖) • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hnv, mul_one]
    rw [hsm]
    have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le (I := I) (cov := cov) hmet x hη
      (a := 0) (b := t * ‖v‖) le_rfl (by positivity)
    rw [zero_smul, Submission.GlobalExp.GExp_zero, sub_zero] at h
    rw [rdist]
    calc (Manifold.riemannianEDist I x
          (Submission.GlobalExp.GExp (cov := cov) hmet x ((t * ‖v‖) • (‖v‖⁻¹ • v)))).toReal
        ≤ (ENNReal.ofReal (t * ‖v‖)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = t * ‖v‖ := ENNReal.toReal_ofReal (by positivity)

/-- **The derivative of a `1`-Lipschitz function is bounded by `1`.**  For every tangent vector `v`
one has `|dF_x(v)| ≤ ‖v‖`, where `F` is `1`-Lipschitz with respect to the Riemannian distance. -/
theorem lipschitz_mvfderiv_le' {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {F : M → ℝ} (hF : ∀ y z : M, |F y - F z| ≤ rdist (I := I) y z) (x : M)
    (v : TangentSpace I x) :
    |mvfderiv I F x v| ≤ ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · set γ : ℝ → M := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (t • v) with hγ
    have hcomm : ∀ y z : M, rdist (I := I) y z = rdist (I := I) z y := by
      intro y z
      rw [rdist, rdist, Manifold.riemannianEDist_comm]
    have hγ0 : γ 0 = x := by
      show Submission.GlobalExp.GExp (cov := cov) hmet x ((0 : ℝ) • v) = x
      rw [zero_smul]
      exact Submission.GlobalExp.GExp_zero hmet x
    have hdist_all : ∀ t : ℝ, rdist (I := I) x (γ t) ≤ |t| * ‖v‖ := by
      intro t
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h]
        exact rdist_GExp_smul_le (I := I) (cov := cov) hmet x v h
      · have h2 := rdist_GExp_smul_le (I := I) (cov := cov) hmet x (-v)
          (by linarith : (0 : ℝ) ≤ -t)
        have hkey : (-t) • (-v) = t • v := by rw [smul_neg, neg_smul, neg_neg]
        rw [hkey, norm_neg] at h2
        rw [abs_of_neg h]
        exact h2
    have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ := by
      rw [hγ]
      exact Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet x hv
    have hγmd : MDiffAt γ 0 :=
      (hγsm.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)
    have hvel : (mfderiv 𝓘(ℝ) I γ 0) (1 : ℝ) = v := by
      rw [← Submission.Geodesic.curveVelocity_apply, hγ]
      exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet x hv
    by_cases hmd : MDifferentiableAt I (𝓘(ℝ, ℝ)) F x
    · have hFmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (F ∘ γ) 0 :=
        (hγ0 ▸ hmd).comp 0 hγmd
      have hchain : mvfderiv I F x v = deriv (F ∘ γ) 0 := by
        have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
          (g := F) (γ := γ) (t := 0) (hγ0 ▸ hmd) hγmd
        have h2 : (mvfderiv I F (γ 0)) ((mfderiv 𝓘(ℝ) I γ 0) (1 : ℝ))
            = (mvfderiv I F x) v := by
          rw [hγ0]
          exact congrArg (fun w => (mvfderiv I F x) w) hvel
        exact h2.symm.trans h
      have hD : HasDerivAt (F ∘ γ) (deriv (F ∘ γ) 0) 0 :=
        (mdifferentiableAt_iff_differentiableAt.mp hFmd).hasDerivAt
      have hslope : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |slope (F ∘ γ) 0 t| ≤ ‖v‖ := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h1 : |F (γ t) - F x| ≤ |t| * ‖v‖ := by
          have h := hF (γ t) x
          rw [hcomm] at h
          exact h.trans (hdist_all t)
        rw [slope_fun_def_field]
        simp only [sub_zero, Function.comp_apply, hγ0]
        rw [abs_div, div_le_iff₀ (abs_pos.mpr ht)]
        nlinarith [h1]
      have hlim1 : Tendsto (fun t : ℝ => |slope (F ∘ γ) 0 t|) (𝓝[≠] (0 : ℝ))
          (𝓝 |deriv (F ∘ γ) 0|) :=
        (continuous_abs.tendsto _).comp hD.tendsto_slope
      have hfin := le_of_tendsto_of_tendsto hlim1 tendsto_const_nhds hslope
      rw [hchain]
      exact hfin
    · have hmf : mfderiv I (𝓘(ℝ, ℝ)) F x = 0 := by
        simp only [mfderiv, hmd, reduceIte]
      have hmvf : mvfderiv I F x v = 0 := by
        rw [mvfderiv, hmf]
        simp
      rw [hmvf, abs_zero]
      exact norm_nonneg v

end Work.Diff.C
