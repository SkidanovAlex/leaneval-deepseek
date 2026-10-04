import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.init_data
import Submission.HopfRinow2
import Submission.HopfRinow
import Submission.GExpVelocity
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp Submission.Geodesic

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]

/-- **Elementary trigonometric inequality.**  A one-sided second-order Taylor bound for `cos`:
`|cos s - cos t| ≤ (|sin t| + |s - t|)·|s - t|`. -/
lemma eik_abs_cos_sub_cos_le (s t : ℝ) :
    |Real.cos s - Real.cos t| ≤ (|Real.sin t| + |s - t|) * |s - t| := by
  have hsplit : |(s + t) / 2 - t| = |s - t| / 2 := by
    rw [show (s + t) / 2 - t = (s - t) / 2 by ring, abs_div]
    norm_num
  have hA : |Real.sin ((s + t) / 2)| ≤ |Real.sin t| + |s - t| / 2 := by
    have h1 : Real.sin ((s + t) / 2) = Real.sin t + (Real.sin ((s + t) / 2) - Real.sin t) := by ring
    have h2 : |Real.sin ((s + t) / 2) - Real.sin t| ≤ |s - t| / 2 := by
      have := Real.abs_sin_sub_sin_le ((s + t) / 2) t
      rwa [hsplit] at this
    rw [h1]
    exact le_trans (abs_add_le _ _) (add_le_add le_rfl h2)
  have hB : |Real.sin ((s - t) / 2)| ≤ |s - t| / 2 := by
    have h := Real.abs_sin_le_abs (x := (s - t) / 2)
    rwa [show |(s - t) / 2| = |s - t| / 2 by rw [abs_div]; norm_num] at h
  have hA0 : 0 ≤ |Real.sin t| + |s - t| / 2 := by positivity
  have hAB : |Real.sin ((s + t) / 2)| * |Real.sin ((s - t) / 2)|
      ≤ (|Real.sin t| + |s - t| / 2) * (|s - t| / 2) :=
    mul_le_mul hA hB (abs_nonneg _) hA0
  have h2 : (2 : ℝ) * |Real.sin ((s + t) / 2)| * |Real.sin ((s - t) / 2)|
      ≤ 2 * (|Real.sin t| + |s - t| / 2) * (|s - t| / 2) := by nlinarith [hAB]
  calc |Real.cos s - Real.cos t|
      = |(-2 : ℝ) * Real.sin ((s + t) / 2) * Real.sin ((s - t) / 2)| := by
        rw [Real.cos_sub_cos]
    _ = 2 * |Real.sin ((s + t) / 2)| * |Real.sin ((s - t) / 2)| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (|Real.sin t| + |s - t| / 2) * (|s - t| / 2) := h2
    _ = (|Real.sin t| + |s - t| / 2) * |s - t| := by ring
    _ ≤ (|Real.sin t| + |s - t|) * |s - t| := by
        have h : |Real.sin t| + |s - t| / 2 ≤ |Real.sin t| + |s - t| := by
          linarith [abs_nonneg (s - t)]
        exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

/-- The Riemannian distance satisfies the triangle inequality (in the `rdist` vocabulary). -/
lemma eik_rdist_triangle_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x y z : M) :
    rdist (I := I) x z ≤ rdist (I := I) x y + rdist (I := I) y z := by
  have htri := Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)
  have h1 : Manifold.riemannianEDist I x y ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top hmet htor x y).ne
  have h2 : Manifold.riemannianEDist I y z ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top hmet htor y z).ne
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) htri
  rw [ENNReal.toReal_add h1 h2] at h3
  exact h3

/-- The distance along a ray of the global exponential map: for a **unit** direction `η`,
`d(GExp x (a•η), GExp x (b•η)) ≤ b - a` for `0 ≤ a ≤ b`. -/
lemma eik_rdist_GExp_ray_sub_le (hmet : IsMetricCompatible cov) (x : M)
    {η : TangentSpace I x} (hη : ‖η‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    rdist (I := I) (GExp (cov := cov) hmet x (a • η))
      (GExp (cov := cov) hmet x (b • η)) ≤ b - a := by
  have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le hmet x hη ha hab
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by linarith)] at h2

/-- The distance from the base point to its own ray: `d(x, GExp x (t•v)) ≤ t·‖v‖` for `t ≥ 0`. -/
lemma eik_rdist_GExp_smul_le (hmet : IsMetricCompatible cov) (x : M) (v : TangentSpace I x)
    {t : ℝ} (ht : 0 ≤ t) : rdist (I := I) x (GExp (cov := cov) hmet x (t • v)) ≤ t * ‖v‖ := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    rw [smul_zero, GExp_zero, norm_zero, mul_zero, rdist, Manifold.riemannianEDist_self,
      ENNReal.toReal_zero]
  · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hη : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hnv]
    have hsm : t • v = (t * ‖v‖) • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hnv, mul_one]
    rw [hsm]
    have h := eik_rdist_GExp_ray_sub_le (I := I) (M := M) (cov := cov) hmet x hη (a := 0)
      (b := t * ‖v‖) le_rfl (by positivity)
    rw [zero_smul, GExp_zero, sub_zero, rdist] at h
    exact h


/-- **Upper bound for the differential of `fcos`.**  For every tangent vector `v`,
`|d(fcos q)_x(v)| ≤ |sin (rdist q x)|·‖v‖`.  No smoothness of the distance function is needed
here: the bound follows from the `1`-Lipschitz property of `rdist q ·` along the rays of the
exponential map together with the mean-value estimate `eik_abs_cos_sub_cos_le` for `cos`. -/
lemma eik_abs_mvfderiv_fcos_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q x : M} (hsm : CMDiffAt ∞ (fcos (I := I) (M := M) q) x) (v : TangentSpace I x) :
    |mvfderiv I (fcos (I := I) (M := M) q) x v|
      ≤ |Real.sin (rdist (I := I) q x)| * ‖v‖ := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    rw [norm_zero, mul_zero]
    simp
  · set γ : ℝ → M := fun t => GExp (cov := cov) hmet x (t • v) with hγdef
    have hγ0 : γ 0 = x := by
      show GExp (cov := cov) hmet x ((0 : ℝ) • v) = x
      rw [zero_smul, GExp_zero]
    have hγmd : MDifferentiableAt 𝓘(ℝ) I γ 0 :=
      init_ray_mdiffAt (I := I) (M := M) (cov := cov) hmet x v
    have hvel : mfderiv 𝓘(ℝ) I γ 0 (1 : ℝ) = v := by
      rw [← curveVelocity_apply]
      exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet x hv
    have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fcos (I := I) (M := M) q) x :=
      hsm.mdifferentiableAt (by simp)
    have hFmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((fcos (I := I) (M := M) q) ∘ γ) 0 :=
      (hγ0 ▸ hfmd).comp 0 hγmd
    have hchain : mvfderiv I (fcos (I := I) (M := M) q) x v
        = deriv ((fcos (I := I) (M := M) q) ∘ γ) 0 := by
      have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
        (g := fcos (I := I) (M := M) q) (γ := γ) (t := 0) (hγ0 ▸ hfmd) hγmd
      have h2 : (mvfderiv I (fcos (I := I) (M := M) q) (γ 0))
          ((mfderiv 𝓘(ℝ) I γ 0) (1 : ℝ))
            = (mvfderiv I (fcos (I := I) (M := M) q) x) v := by
        rw [hγ0]
        exact congrArg (fun w => (mvfderiv I (fcos (I := I) (M := M) q) x) w) hvel
      exact h2.symm.trans h
    have hD : HasDerivAt ((fcos (I := I) (M := M) q) ∘ γ)
        (deriv ((fcos (I := I) (M := M) q) ∘ γ) 0) 0 :=
      (mdifferentiableAt_iff_differentiableAt.mp hFmd).hasDerivAt
    have hlip : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        |rdist (I := I) q (γ t) - rdist (I := I) q x| ≤ t * ‖v‖ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      have h3 : rdist (I := I) x (γ t) ≤ t * ‖v‖ := by
        show rdist (I := I) x (GExp (cov := cov) hmet x (t • v)) ≤ t * ‖v‖
        exact eik_rdist_GExp_smul_le (I := I) (M := M) (cov := cov) hmet x v ht0
      have h1 : rdist (I := I) q (γ t) - rdist (I := I) q x ≤ rdist (I := I) x (γ t) := by
        have h := eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor q x (γ t)
        linarith
      have h2 : rdist (I := I) q x - rdist (I := I) q (γ t) ≤ rdist (I := I) x (γ t) := by
        have h := eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor q (γ t) x
        have h4 : rdist (I := I) (γ t) x = rdist (I := I) x (γ t) :=
          rdist_comm' (I := I) (M := M) (γ t) x
        linarith
      rw [abs_sub_le_iff]
      exact ⟨h1.trans h3, by linarith⟩
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        |((fcos (I := I) (M := M) q) ∘ γ) (0 + t) - ((fcos (I := I) (M := M) q) ∘ γ) 0|
          ≤ (|Real.sin (rdist (I := I) q x)| + t * ‖v‖) * (t * ‖v‖) := by
      filter_upwards [hlip, self_mem_nhdsWithin] with t ht htg
      have ht0 : 0 ≤ t := le_of_lt htg
      have htrig := eik_abs_cos_sub_cos_le (rdist (I := I) q (γ t)) (rdist (I := I) q x)
      have hconv : ((fcos (I := I) (M := M) q) ∘ γ) (0 + t) - ((fcos (I := I) (M := M) q) ∘ γ) 0
          = Real.cos (rdist (I := I) q (γ t)) - Real.cos (rdist (I := I) q x) := by
        simp only [Function.comp_apply, fcos, zero_add, hγ0]
      rw [hconv]
      refine htrig.trans ?_
      exact mul_le_mul (by linarith [abs_nonneg (rdist (I := I) q (γ t) - rdist (I := I) q x)])
        ht (abs_nonneg _) (add_nonneg (abs_nonneg _) (mul_nonneg ht0 (norm_nonneg v)))
    have hlim1 : Tendsto
        (fun t : ℝ =>
          |t⁻¹ • (((fcos (I := I) (M := M) q) ∘ γ) (0 + t) - ((fcos (I := I) (M := M) q) ∘ γ) 0)|)
        (𝓝[>] (0 : ℝ)) (𝓝 |deriv ((fcos (I := I) (M := M) q) ∘ γ) 0|) :=
      (continuous_abs.tendsto _).comp (by simpa using hD.tendsto_slope_zero_right)
    have hlim2 : Tendsto (fun t : ℝ => (|Real.sin (rdist (I := I) q x)| + t * ‖v‖) * ‖v‖)
        (𝓝[>] (0 : ℝ)) (𝓝 (|Real.sin (rdist (I := I) q x)| * ‖v‖)) := by
      have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        Filter.tendsto_id.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun t : ℝ => |Real.sin (rdist (I := I) q x)| + t * ‖v‖)
          (𝓝[>] (0 : ℝ)) (𝓝 (|Real.sin (rdist (I := I) q x)| + 0 * ‖v‖)) :=
        tendsto_const_nhds.add (ht.mul_const ‖v‖)
      simpa using h1.mul_const ‖v‖
    have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        |t⁻¹ • (((fcos (I := I) (M := M) q) ∘ γ) (0 + t) - ((fcos (I := I) (M := M) q) ∘ γ) 0)|
          ≤ (|Real.sin (rdist (I := I) q x)| + t * ‖v‖) * ‖v‖ := by
      filter_upwards [hev, self_mem_nhdsWithin] with t ht htg
      have htpos : 0 < t := htg
      have htne : t ≠ 0 := ne_of_gt htpos
      rw [zero_add] at ht
      have h1 : |t⁻¹ • (((fcos (I := I) (M := M) q) ∘ γ) (0 + t)
            - ((fcos (I := I) (M := M) q) ∘ γ) 0)|
          = t⁻¹ * |((fcos (I := I) (M := M) q) ∘ γ) t
              - ((fcos (I := I) (M := M) q) ∘ γ) 0| := by
        rw [smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr htpos), zero_add]
      rw [h1]
      calc t⁻¹ * |((fcos (I := I) (M := M) q) ∘ γ) t - ((fcos (I := I) (M := M) q) ∘ γ) 0|
          ≤ t⁻¹ * ((|Real.sin (rdist (I := I) q x)| + t * ‖v‖) * (t * ‖v‖)) :=
            mul_le_mul_of_nonneg_left ht (by positivity)
        _ = (|Real.sin (rdist (I := I) q x)| + t * ‖v‖) * ‖v‖ := by
            field_simp
    have hmain := le_of_tendsto_of_tendsto hlim1 hlim2 hbound
    rw [hchain]
    exact hmain

/-- **Lower bound for the gradient of `fcos`.**  At a point `x ≠ q` where `fcos q` is smooth, the
Hopf–Rinow minimising geodesic from `x` to `q` runs along which `rdist q` decreases at unit speed;
its initial velocity `η` is a unit vector, and `d(fcos q)_x(η) = sin (rdist q x)`.  Hence
`|sin (rdist q x)| ≤ ‖∇(fcos q) x‖`. -/
lemma eik_abs_sin_le_norm_rgrad_fcos (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q x : M} (hsm : CMDiffAt ∞ (fcos (I := I) (M := M) q) x)
    (hx : rdist (I := I) q x ≠ 0) :
    |Real.sin (rdist (I := I) q x)|
      ≤ ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖ := by
  obtain ⟨V, hVq, hVd⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq hmet htor x q
  set L : ℝ := ‖V‖ with hLdef
  have hrd : rdist (I := I) q x = L := by
    have h1 : rdist (I := I) x q = L := by
      show (Manifold.riemannianEDist I x q).toReal = L
      rw [hVd, ENNReal.toReal_ofReal (norm_nonneg V), ← hLdef]
    rw [rdist_comm' (I := I) (M := M) x q] at h1
    exact h1
  have hLpos : 0 < L := by
    rw [← hrd]
    show 0 < (Manifold.riemannianEDist I q x).toReal
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx)
  have hLne : L ≠ 0 := ne_of_gt hLpos
  set η : TangentSpace I x := L⁻¹ • V with hηdef
  have hηnorm : ‖η‖ = 1 := by
    rw [hηdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLpos), hLdef]
    exact inv_mul_cancel₀ (by rw [← hLdef]; exact hLne)
  have hηne : η ≠ 0 := by
    rw [← norm_pos_iff]
    rw [hηnorm]
    norm_num
  have hγL : GExp (cov := cov) hmet x (L • η) = q := by
    have h1 : L • η = V := by
      rw [hηdef]
      exact smul_inv_smul₀ hLne V
    rw [h1, hVq]
  set γ : ℝ → M := fun t => GExp (cov := cov) hmet x (t • η) with hγdef
  have hγ0 : γ 0 = x := by
    show GExp (cov := cov) hmet x ((0 : ℝ) • η) = x
    rw [zero_smul, GExp_zero]
  have hval : ∀ t ∈ Set.Icc (0 : ℝ) L, rdist (I := I) q (γ t) = L - t := by
    intro t ht
    obtain ⟨ht0, htL⟩ := ht
    show rdist (I := I) q (GExp (cov := cov) hmet x (t • η)) = L - t
    have hup1 : rdist (I := I) x (GExp (cov := cov) hmet x (t • η)) ≤ t := by
      have h := eik_rdist_GExp_ray_sub_le (I := I) (M := M) (cov := cov) hmet x hηnorm
        (a := 0) (b := t) le_rfl ht0
      rwa [zero_smul, GExp_zero, sub_zero] at h
    have hup2 : rdist (I := I) (GExp (cov := cov) hmet x (t • η)) q ≤ L - t := by
      have h := eik_rdist_GExp_ray_sub_le (I := I) (M := M) (cov := cov) hmet x hηnorm
        (a := t) (b := L) ht0 htL
      rwa [hγL] at h
    have htri : rdist (I := I) x q ≤ rdist (I := I) x (GExp (cov := cov) hmet x (t • η))
        + rdist (I := I) (GExp (cov := cov) hmet x (t • η)) q :=
      eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor x _ q
    have hxq : rdist (I := I) x q = L := by
      rw [rdist_comm' (I := I) (M := M) x q]
      exact hrd
    have heq : rdist (I := I) (GExp (cov := cov) hmet x (t • η)) q = L - t := by linarith
    exact ((rdist_comm' (I := I) (M := M) (GExp (cov := cov) hmet x (t • η)) q).symm).trans heq
  have hIcc : Set.Icc (0 : ℝ) L ∈ 𝓝[Set.Ici 0] (0 : ℝ) := by
    rw [mem_nhdsWithin_iff]
    refine ⟨L, hLpos, fun t ht => ⟨ht.2, ?_⟩⟩
    have ht1 : t ∈ Metric.ball (0 : ℝ) L := ht.1
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at ht1
    exact ht1.2.le
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ 0 :=
    init_ray_mdiffAt (I := I) (M := M) (cov := cov) hmet x η
  have hvel : mfderiv 𝓘(ℝ) I γ 0 (1 : ℝ) = η := by
    rw [← curveVelocity_apply]
    exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet x hηne
  have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fcos (I := I) (M := M) q) x :=
    hsm.mdifferentiableAt (by simp)
  have hFmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((fcos (I := I) (M := M) q) ∘ γ) 0 :=
    (hγ0 ▸ hfmd).comp 0 hγmd
  have hchain : mvfderiv I (fcos (I := I) (M := M) q) x η
      = deriv ((fcos (I := I) (M := M) q) ∘ γ) 0 := by
    have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fcos (I := I) (M := M) q) (γ := γ) (t := 0) (hγ0 ▸ hfmd) hγmd
    have h2 : (mvfderiv I (fcos (I := I) (M := M) q) (γ 0))
        ((mfderiv 𝓘(ℝ) I γ 0) (1 : ℝ))
          = (mvfderiv I (fcos (I := I) (M := M) q) x) η := by
      rw [hγ0]
      exact congrArg (fun w => (mvfderiv I (fcos (I := I) (M := M) q) x) w) hvel
    exact h2.symm.trans h
  have hD : HasDerivAt ((fcos (I := I) (M := M) q) ∘ γ)
      (deriv ((fcos (I := I) (M := M) q) ∘ γ) 0) 0 :=
    (mdifferentiableAt_iff_differentiableAt.mp hFmd).hasDerivAt
  have heq : ((fcos (I := I) (M := M) q) ∘ γ) =ᶠ[𝓝[Set.Ici 0] (0 : ℝ)]
      (Real.cos ∘ (fun t : ℝ => L - t)) := by
    filter_upwards [hIcc] with t ht
    show Real.cos (rdist (I := I) q (γ t)) = Real.cos (L - t)
    rw [hval t ht]
  have hbase : HasDerivAt (Real.cos ∘ (fun t : ℝ => L - t)) (Real.sin L) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => L - t) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub L
    have h3 := (Real.hasDerivAt_cos (L - 0)).comp 0 h1
    rw [show (-Real.sin (L - 0)) * (-1) = Real.sin L by simp] at h3
    exact h3
  have hA : HasFDerivWithinAt ((fcos (I := I) (M := M) q) ∘ γ)
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv ((fcos (I := I) (M := M) q) ∘ γ) 0))
      (Set.Ici 0) 0 :=
    (hasDerivWithinAt_iff_hasFDerivWithinAt).mp hD.hasDerivWithinAt
  have hB : HasFDerivWithinAt ((fcos (I := I) (M := M) q) ∘ γ)
      (ContinuousLinearMap.toSpanSingleton ℝ (Real.sin L)) (Set.Ici 0) 0 := by
    have h0 : ((fcos (I := I) (M := M) q) ∘ γ) 0 = (Real.cos ∘ (fun t : ℝ => L - t)) 0 := by
      show Real.cos (rdist (I := I) q (γ 0)) = Real.cos (L - 0)
      rw [hγ0, hrd, sub_zero]
    exact (hasDerivWithinAt_iff_hasFDerivWithinAt).mp
      (hbase.hasDerivWithinAt.congr_of_eventuallyEq heq h0)
  have hderivval : deriv ((fcos (I := I) (M := M) q) ∘ γ) 0 = Real.sin L :=
    ContinuousLinearMap.toSpanSingleton_inj.mp ((uniqueDiffWithinAt_Ici 0).eq hA hB)
  have hchainval : mvfderiv I (fcos (I := I) (M := M) q) x η = Real.sin L := by
    rw [hchain, hderivval]
  calc |Real.sin (rdist (I := I) q x)|
      = |Real.sin L| := by rw [hrd]
    _ = |mvfderiv I (fcos (I := I) (M := M) q) x η| := by rw [hchainval]
    _ = |Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x) η| := by
        rw [inner_rgrad_mvfderiv']
    _ ≤ ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖ * ‖η‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖ := by rw [hηnorm, mul_one]

end Helpers

/-- **Eikonal equation for `fcos`.**  Where `fcos q = cos ∘ d(q,·)` is smooth,
`⟪∇f, ∇f⟫ = 1 - f²`.  (At the critical values `f = ±1` the gradient vanishes, so the identity
holds there too; the proof may use that `d(q,·)` has unit gradient where it is smooth.) -/
theorem rgrad_fcos_eikonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M] [PathConnectedSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q x : M} (hsm : CMDiffAt ∞ (fcos (I := I) (M := M) q) x) :
    Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
      = 1 - (fcos (I := I) (M := M) q x) ^ 2 := by
  have hup := eik_abs_mvfderiv_fcos_le hmet htor hsm
  have hnorm_le : ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖
      ≤ |Real.sin (rdist (I := I) q x)| := by
    by_cases h0 : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x = 0
    · rw [h0, norm_zero]
      exact abs_nonneg _
    · have hne : ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖ ≠ 0 :=
        norm_ne_zero_iff.mpr h0
      set w : TangentSpace I x := (‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖)⁻¹
        • rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x with hwdef
      have hwn : ‖w‖ = 1 := by
        rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr h0))]
        exact inv_mul_cancel₀ hne
      have hinner : mvfderiv I (fcos (I := I) (M := M) q) x w
          = ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖ := by
        rw [← inner_rgrad_mvfderiv' (fcos (I := I) (M := M) q) x w, hwdef,
          real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hh := hup w
      rw [hinner, hwn, mul_one] at hh
      rwa [abs_of_nonneg (norm_nonneg _)] at hh
  by_cases hsin : Real.sin (rdist (I := I) q x) = 0
  · have hnorm0 : ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖ = 0 := by
      rw [hsin, abs_zero] at hnorm_le
      exact le_antisymm hnorm_le (norm_nonneg _)
    have hgrad0 : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x = 0 :=
      norm_eq_zero.mp hnorm0
    rw [hgrad0, inner_zero_left]
    have hsq := Real.sin_sq_add_cos_sq (rdist (I := I) q x)
    rw [hsin] at hsq
    show (0 : ℝ) = 1 - Real.cos (rdist (I := I) q x) ^ 2
    linarith
  · have hx0 : rdist (I := I) q x ≠ 0 := fun h => hsin (by rw [h]; exact Real.sin_zero)
    have hlow := eik_abs_sin_le_norm_rgrad_fcos hmet htor hsm hx0
    have hnorm_eq : ‖rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x‖
        = |Real.sin (rdist (I := I) q x)| := le_antisymm hnorm_le hlow
    rw [real_inner_self_eq_norm_sq, hnorm_eq, sq_abs]
    have hsq := Real.sin_sq_add_cos_sq (rdist (I := I) q x)
    show Real.sin (rdist (I := I) q x) ^ 2 = 1 - Real.cos (rdist (I := I) q x) ^ 2
    linarith

end Work.Diff.C
