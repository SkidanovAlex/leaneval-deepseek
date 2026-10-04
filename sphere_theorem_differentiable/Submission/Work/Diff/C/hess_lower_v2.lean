import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Lib
import Submission.Work.Diff.C.HessLowerKit
import Submission.Work.Diff.C.HessLowerAux
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.fcos_lipschitz
import Submission.Work.Diff.C.fcos_hess_pt
import Submission.Work.Diff.C.riccati_lower_bound
import Submission.Work.Diff.C.hess_dist_jacobi_shapeOp
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.Work.Diff.C.jacobi_modulus_log_deriv_lower

set_option backward.isDefEq.respectTransparency.types false

/-! # Lower Hessian comparison for the distance function (area C)

This file proves `Work.Diff.C.hess_lower_v2`: under the upper curvature bound `sec ≤ 1 + η` and
`√(1+η) · d(p,x) < π`, the Hessian of the Riemannian distance function is bounded below by the
model Hessian `√(1+η)·cot (√(1+η)·d)`.

The mathematical content of the file itself is the *reduction*:

* from the hypotheses to a unit-speed minimising geodesic `γ(t) = GExp p (t • u)` from `p` to `x`
  (Hopf–Rinow + the sub-arc minimising property);
* the radial reduction `Hess d (V,V) = Hess d (V_⊥, V_⊥)` (`V_⊥ = V - ⟪∇d,V⟫∇d`), from the local
  maximum principle for `⟪∇d,∇d⟫` (`|∇d| ≤ 1` by `1`-Lipschitzness, `= 1` at `x`);
* the final arithmetic.

The two genuinely geometric inputs are delegated:
`Work.Diff.C.hess_dist_jacobi_shapeOp` (the shape-operator identity
`Hess d(V,V) + ⟪∇d,V⟫²/d = ⟪∇_tZ(d), Z(d)⟫` for the Jacobi field `Z` with `Z 0 = 0`, `Z d = V`) and
`Work.Diff.C.jacobi_modulus_log_deriv_lower` (the Riccati/Sturm comparison
`√K cot(√K d)‖Z d‖² ≤ ⟪∇_tZ(d), Z(d)⟫`). -/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M] [CompactSpace M] [Nontrivial E] [PathConnectedSpace M]

/-- **The gradient of a `1`-Lipschitz function has norm at most `1`** (packaged from
`Work.Diff.C.lipschitz_mvfderiv_le`). -/
lemma inner_rgrad_self_le_one {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {F : M → ℝ} (hF : ∀ y z : M, |F y - F z| ≤ rdist (I := I) y z) (y : M) :
    Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y) ≤ 1 := by
  have hb := Work.Diff.C.lipschitz_mvfderiv_le' (I := I) (cov := cov) hmet htor hF y
    (rgrad (I := I) F y)
  have h1 : Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y)
      = mvfderiv I F y (rgrad (I := I) F y) :=
    inner_rgrad F y (rgrad (I := I) F y)
  have h2 : mvfderiv I F y (rgrad (I := I) F y) ≤ ‖rgrad (I := I) F y‖ :=
    le_trans (le_abs_self _) hb
  have h3 : (0 : ℝ) ≤ mvfderiv I F y (rgrad (I := I) F y) := by
    rw [← h1]; exact real_inner_self_nonneg
  have h4 : ‖rgrad (I := I) F y‖ ^ 2 ≤ ‖rgrad (I := I) F y‖ := by
    rw [← real_inner_self_eq_norm_sq, h1]; exact h2
  nlinarith [norm_nonneg (rgrad (I := I) F y), h4]

/-- **The radial part of the Hessian of the distance function vanishes.**  If `F` is `C^∞` at `x`,
`|∇F x| = 1`, and `|∇F| ≤ 1` everywhere (true for the distance function, which is `1`-Lipschitz),
then `Hess F (W, ∇F x) = 0` for every `W`.

Indeed `Hess F(W, ∇F x) = ½ · d(⟪∇F,∇F⟫)_x(W)` (metric compatibility), and `⟪∇F,∇F⟫` has a local
maximum at `x` with value `1`. -/
theorem rhess_radial_eq_zero {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x)
    (hunit : Inner.inner ℝ (rgrad (I := I) F x) (rgrad (I := I) F x) = 1)
    (hlip : ∀ y : M, Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y) ≤ 1)
    (W : TangentSpace I x) :
    rhess cov F x W (rgrad (I := I) F x) = 0 := by
  classical
  set g : M → ℝ := fun y => Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y) with hg
  have hgsm : CMDiffAt ∞ g x := by
    have h1 : ContMDiffAt I I.tangent ∞ (T% (fun y : M => rgrad (I := I) F y)) x :=
      grad_smoothAt (I := I) hF
    have h2 : CMDiffAt ∞ (fun y : M => Inner.inner ℝ (rgrad (I := I) F y)
        (rgrad (I := I) F y)) x := ContMDiffAt.inner_bundle h1 h1
    simpa only [hg] using h2
  have hgmd : MDiffAt g x := hgsm.mdifferentiableAt (by simp)
  have hdg : mvfderiv I g x = 0 := by
    ext W'
    rcases eq_or_ne W' 0 with h0 | h0
    · simp [h0]
    · set c : ℝ → M := fun s => Submission.GlobalExp.GExp (cov := cov) hmet x (s • W') with hc
      have hcm : ContMDiffOn 𝓘(ℝ) I ∞ c Set.univ :=
        Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet x h0
      have hcmd : MDiffAt c 0 :=
        (hcm.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)
      have hvel : mfderiv 𝓘(ℝ) I c 0 (1 : ℝ) = W' := by
        rw [← Submission.Geodesic.curveVelocity_apply]
        exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet x h0
      have hc0 : c 0 = x := by
        show Submission.GlobalExp.GExp (cov := cov) hmet x ((0 : ℝ) • W') = x
        rw [zero_smul]
        exact Submission.GlobalExp.GExp_zero hmet x
      have hmin : IsLocalMax (g ∘ c) 0 := by
        refine Filter.Eventually.of_forall fun s => ?_
        have h1 : g (c s) ≤ 1 := hlip (c s)
        have h2 : g (c 0) = 1 := by rw [hc0]; exact hunit
        show g (c s) ≤ g (c 0)
        rw [h2]
        exact h1
      have hderiv : deriv (g ∘ c) 0 = 0 := IsLocalMax.deriv_eq_zero hmin
      have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := g)
        (γ := c) (t := 0) (by rw [hc0]; exact hgmd) hcmd
      rw [hvel, hderiv] at hchain
      rw [hc0] at hchain
      exact hchain
  have hσmd : MDiffAt (T% (fun y : M => rgrad (I := I) F y)) x :=
    (grad_smoothAt (I := I) hF).mdifferentiableAt (by simp)
  have hcomp := mvfderiv_inner_eq_of_isMetricCompatible_pt (I := I) (x := x) cov hmet
    (σ := fun y : M => rgrad (I := I) F y) (τ := fun y : M => rgrad (I := I) F y)
    hσmd hσmd W
  rw [← hg] at hcomp
  rw [hdg, zero_apply] at hcomp
  have h3 : Inner.inner ℝ (cov (fun y : M => rgrad (I := I) F y) x W) (rgrad (I := I) F x) = 0 := by
    have h4 : Inner.inner ℝ (cov (fun y : M => rgrad (I := I) F y) x W) (rgrad (I := I) F x)
        + Inner.inner ℝ (rgrad (I := I) F x) (cov (fun y : M => rgrad (I := I) F y) x W) = 0 :=
      hcomp.symm
    rw [real_inner_comm] at h4
    linarith
  rw [rhess]
  exact h3

/-- **The radial reduction for the Hessian of the distance function.** -/
theorem rhess_radial_reduce {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x)
    (hunit : Inner.inner ℝ (rgrad (I := I) F x) (rgrad (I := I) F x) = 1)
    (hlip : ∀ y : M, Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y) ≤ 1)
    (V : TangentSpace I x) :
    rhess cov F x V V
      = rhess cov F x (V - (Inner.inner ℝ (rgrad (I := I) F x) V) • rgrad (I := I) F x)
          (V - (Inner.inner ℝ (rgrad (I := I) F x) V) • rgrad (I := I) F x) := by
  classical
  set g := rgrad (I := I) F x with hg
  set l : ℝ := Inner.inner ℝ g V with hl
  have hze : ∀ W : TangentSpace I x, rhess cov F x W g = 0 :=
    fun W => rhess_radial_eq_zero (I := I) (cov := cov) hmet htor hF hunit hlip W
  have hsym : ∀ W W' : TangentSpace I x, rhess cov F x W W' = rhess cov F x W' W :=
    fun W W' => rhess_symm_pt (I := I) (cov := cov) hmet htor hF W W'
  have hAg : rhess cov F x (V - l • g) g = 0 := hze _
  have hgA : rhess cov F x g (V - l • g) = 0 := by rw [hsym g (V - l • g)]; exact hze _
  have hgg : rhess cov F x g g = 0 := hze g
  have hQ : (V - l • g) + l • g = V := by abel
  conv_lhs => rw [← hQ]
  rw [rhess_add_left_pt, rhess_add_right_pt, rhess_add_right_pt, rhess_smul_right_pt,
    rhess_smul_left_pt, rhess_smul_left_pt, rhess_smul_right_pt, hAg, hgA, hgg]
  ring

end Helpers

/-- **Lower Hessian comparison for the distance function** under the upper curvature bound
`sec ≤ 1 + η`: for every `V ∈ T_xM`,

`√(1+η) · cot (√(1+η) · d(p,x)) · (⟪V,V⟫ - ⟪∇d(x), V⟫²) ≤ Hess d(x)(V,V)`,

provided `√(1+η)·d(p,x) < π`. -/
theorem hess_lower_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {η : ℝ} (hη : 0 < η) (hpinch : Pinched cov 1 (1 + η)) (p : M) {x : M} {V : TangentSpace I x}
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x)
    (hunit : Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1)
    (hlt : Real.sqrt (1 + η) * rdist (I := I) p x < Real.pi) :
    Real.sqrt (1 + η) * Real.cot (Real.sqrt (1 + η) * rdist (I := I) p x)
        * (Inner.inner ℝ V V - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) ^ 2)
      ≤ rhess cov (rdist (I := I) p) x V V := by
  classical
  haveI : Nontrivial E := ⟨⟨rgrad (I := I) (fun z : M ↦ rdist (I := I) p z) x, 0, by
    intro h0
    rw [h0] at hunit
    simp at hunit⟩⟩
  haveI : PathConnectedSpace M := inferInstance
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  set F : M → ℝ := fun z : M => rdist (I := I) p z with hFdef
  set K : ℝ := 1 + η with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hcurv : Submission.RauchK.CurvLe cov K := by
    rw [hKdef]; exact curvLe_of_pinched (I := I) (cov := cov) hpinch
  -- the distance function is `1`-Lipschitz, so `|∇d| ≤ 1` everywhere
  have hFlip : ∀ y z : M, |F y - F z| ≤ rdist (I := I) y z := by
    intro y z
    rw [abs_sub_comm]
    exact rdist_lipschitz (I := I) (M := M) (cov := cov) hmet htor p y z
  have hlip : ∀ y : M, Inner.inner ℝ (rgrad (I := I) F y) (rgrad (I := I) F y) ≤ 1 :=
    fun y => inner_rgrad_self_le_one (I := I) (cov := cov) hmet htor hFlip y
  -- `x ≠ p`, hence the distance is positive
  have hxne : x ≠ p := by
    intro hxp
    have hinner : ∀ w : TangentSpace I x, Inner.inner ℝ (rgrad (I := I) F x) w = 0 := by
      intro w
      rcases eq_or_ne w 0 with hw | hw
      · simp [hw]
      · set c : ℝ → M := fun s => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w) with hc
        have hcm : ContMDiffOn 𝓘(ℝ) I ∞ c Set.univ :=
          Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hw
        have hcmd : MDiffAt c 0 :=
          (hcm.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)
        have hvel : mfderiv 𝓘(ℝ) I c 0 (1 : ℝ) = w := by
          rw [← Submission.Geodesic.curveVelocity_apply]
          exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet p hw
        have hc0 : c 0 = x := by
          show Submission.GlobalExp.GExp (cov := cov) hmet p ((0 : ℝ) • w) = x
          rw [zero_smul, Submission.GlobalExp.GExp_zero, hxp]
        have hmin : IsLocalMin (F ∘ c) 0 := by
          refine Filter.Eventually.of_forall fun s => ?_
          show F (c 0) ≤ F (c s)
          rw [hc0, hxp]
          have : F p = 0 := by
            show (Manifold.riemannianEDist I p p).toReal = 0
            rw [Manifold.riemannianEDist_self]; rfl
          rw [this]
          exact ENNReal.toReal_nonneg
        have hderiv : deriv (F ∘ c) 0 = 0 := IsLocalMin.deriv_eq_zero hmin
        have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := F)
          (γ := c) (t := 0) (by rw [hc0]; exact hsm.mdifferentiableAt (by simp)) hcmd
        rw [hvel, hderiv] at hchain
        rw [hc0] at hchain
        rw [inner_rgrad]
        exact hchain
    have h0 : rgrad (I := I) F x = 0 := by
      have := hinner (rgrad (I := I) F x)
      rwa [inner_self_eq_zero] at this
    rw [h0] at hunit
    simp at hunit
  have hdpos : 0 < rdist (I := I) p x := by
    rw [rdist]
    exact ENNReal.toReal_pos
      (fun h0 => hxne ((Submission.EDist.riemannianEDist_eq_zero_iff).mp h0).symm)
      (ne_of_lt (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p x))
  -- the minimising geodesic from `p` to `x`
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p x
  have hdv : rdist (I := I) p x = ‖v‖ := by
    rw [rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v)]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdv
    linarith [hdv, hdpos]
  set d : ℝ := ‖v‖ with hddef
  set u : TangentSpace I p := ‖v‖⁻¹ • v with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hvne),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]
  have hune : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu; norm_num at hu
  have hvu : d • u = v := by
    rw [hddef, hudef, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  have hgx : Submission.GlobalExp.GExp (cov := cov) hmet p (d • u) = x := by
    rw [hvu]; exact hvG
  subst hgx
  set γ : ℝ → M := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (t • u) with hγdef
  -- `0 < d`
  have hd0 : 0 < d := lt_of_lt_of_eq hdpos hdv
  -- the geodesic data
  have hminB : Manifold.riemannianEDist I p
      (Submission.GlobalExp.geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) p u hu ‖v‖)
      = ENNReal.ofReal ‖v‖ := by
    rw [← Submission.HopfRinow.GExp_eq_geodCurve (cov := cov) hmet hu (norm_nonneg v)
      (r := ‖v‖) (norm_nonneg v) le_rfl]
    exact hvd
  have hmin : ∀ t ∈ Set.Icc (0 : ℝ) d,
      Manifold.riemannianEDist I p (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
        = ENNReal.ofReal t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) ‖v‖ := by rw [hddef] at ht; exact ht
    have h1 : Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)
        = Submission.GlobalExp.geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) p u hu t :=
      Submission.HopfRinow.GExp_eq_geodCurve (cov := cov) hmet hu (norm_nonneg v) (r := t)
        ht'.1 ht'.2
    rw [h1]
    have h2 := Submission.HingeKey.geodCurve_sub_arc_minimising' (I := I) (cov := cov) hmet
      (T := ‖v‖) (norm_nonneg v) hu (s := ‖v‖) (norm_nonneg v) le_rfl hminB 0
      ⟨le_refl (0 : ℝ), norm_nonneg v⟩ t ⟨ht'.1, ht'.2⟩ ht'.1
    rw [(Submission.GlobalExp.geodCurve_spec (cov := cov) hmet ‖v‖ (norm_nonneg v) p u hu).1,
      sub_zero] at h2
    exact h2
  have hdrd : rdist (I := I) p (Submission.GlobalExp.GExp (cov := cov) hmet p (d • u)) = d := by
    rw [rdist, hmin d ⟨hd0.le, le_rfl⟩, ENNReal.toReal_ofReal hd0.le]
  have hKd : Real.sqrt K * d < Real.pi := by
    rw [hKdef, ← hdrd]
    simpa only using hlt
  have hγsm : ContMDiff 𝓘(ℝ) I ∞ γ := by
    rw [hγdef, ← contMDiffOn_univ]
    exact Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hune
  -- local minimality of the perturbed rays (delegated)
  have hminW : ∀ w : TangentSpace I p, ∀ᶠ s in 𝓝 (0 : ℝ),
      Manifold.riemannianEDist I p
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((d • u) + s • w))
        = ENNReal.ofReal ‖(d • u) + s • w‖ := by
    refine ray_minimising_near_perturbation (I := I) (cov := cov) hmet htor hKpos hcurv p
      (v := d • u) ?_ ?_ ?_ hsm hunit
    · rw [hvu]; exact hvne
    · have hdu : ‖d • u‖ = d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd0, hu, mul_one]
      rw [hdu, lt_div_iff₀ (Real.sqrt_pos.mpr hKpos), mul_comm]
      exact hKd
    · have hdu : ‖d • u‖ = d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd0, hu, mul_one]
      rw [hdu]
      exact hmin d ⟨hd0.le, le_rfl⟩
  -- the shape-operator identity (delegated), applied to the part of `V` orthogonal to `∇d`
  set l : ℝ := Inner.inner ℝ (rgrad (I := I) F (γ d)) V with hl
  set Vp : TangentSpace I (γ d) := V - l • rgrad (I := I) F (γ d) with hVp
  have horth : Inner.inner ℝ (rgrad (I := I) F (γ d)) Vp = 0 := by
    rw [hVp, hl, inner_sub_right, real_inner_smul_right, hunit]
    ring
  obtain ⟨Z, hZjac, hZ0, hZd, hident⟩ :=
    hess_dist_jacobi_shapeOp (I := I) (cov := cov) hmet htor hKpos hcurv p hd0
      (u := u) hu hKd hmin hminW hsm hunit Vp
  -- the geodesic is unit speed, read off the chart data of the Jacobi field
  have hunitγ : ∀ t : ℝ, ‖Submission.Geodesic.curveVelocity (I := I) γ t‖ = 1 := by
    intro t
    obtain ⟨x₀, uch, wch, ych, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hZjac t
    have hsrc : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) t
        ∈ (chartAt H x₀).source := by
      rw [h3.self_of_nhds]
      exact Submission.ChartConnection.mem_source_chartCurve (I := I) h1.self_of_nhds
    have hγmd : MDifferentiableAt 𝓘(ℝ) I
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) t :=
      (hγsm.contMDiffAt).mdifferentiableAt (by simp)
    have hvel := Submission.ChartIndep.frameVector_chartVel_eq_curveVelocity (I := I)
      (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      (t₀ := t) hsrc h1 h3 h2 hγmd
    rw [← hvel]
    have h2' : ‖Submission.Geodesic.frameVector (I := I) x₀
          ((fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) t) (wch t)‖
        = Real.sqrt (Submission.ChartConnection.chartGram (I := I) x₀
          ((fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) t)
          (wch t) (wch t)) := by
      rw [Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq,
        Real.sqrt_sq (norm_nonneg _)]
    rw [h2', h3.self_of_nhds, h5.self_of_nhds]
    norm_num
  -- the Riccati/Sturm comparison (delegated)
  have hZs : ∀ t, Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Z t := by
    intro t
    exact Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hZjac
      (hγsm.contMDiffOn.mono (fun s _ => Set.mem_univ s))
  have hric := jacobi_modulus_log_deriv_lower (I := I) (cov := cov) hmet htor hKpos hcurv
    hd0 hKd hγsm hunitγ hZs hZjac hZ0
  -- assemble
  have hred := rhess_radial_reduce (I := I) (cov := cov) hmet htor (F := F) hsm hunit hlip V
  have hZs' : Inner.inner ℝ (Z d) (Z d) = Inner.inner ℝ Vp Vp := by rw [hZd]
  have hpite : Inner.inner ℝ Vp Vp
      = Inner.inner ℝ V V - (Inner.inner ℝ (rgrad (I := I) F (γ d)) V) ^ 2 := by
    have hsym : Inner.inner ℝ V (rgrad (I := I) F (γ d))
        = Inner.inner ℝ (rgrad (I := I) F (γ d)) V := by rw [real_inner_comm]
    have hgg : Inner.inner ℝ (rgrad (I := I) F (γ d)) (rgrad (I := I) F (γ d)) = 1 := hunit
    simp only [hVp, hl, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hgg, hsym]
    ring
  have hid2 : rhess cov F (γ d) Vp Vp = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) Vp := by
    have h := hident
    rw [horth] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      add_zero] at h
    exact h
  rw [hdrd]
  change Real.sqrt K * Real.cot (Real.sqrt K * d)
      * (Inner.inner ℝ V V - (Inner.inner ℝ (rgrad (I := I) F (γ d)) V) ^ 2)
      ≤ rhess cov F (γ d) V V
  calc Real.sqrt K * Real.cot (Real.sqrt K * d)
        * (Inner.inner ℝ V V - (Inner.inner ℝ (rgrad (I := I) F (γ d)) V) ^ 2)
      = Real.sqrt K * Real.cot (Real.sqrt K * d) * Inner.inner ℝ Vp Vp := by
        rw [← hpite]
    _ = Real.sqrt K * Real.cot (Real.sqrt K * d) * Inner.inner ℝ (Z d) (Z d) := by rw [hZs']
    _ ≤ Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) (Z d) := hric
    _ = Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov Z d) Vp := by rw [hZd]
    _ = rhess cov F (γ d) Vp Vp := hid2.symm
    _ = rhess cov F (γ d) V V := hred.symm

end Work.Diff.C
