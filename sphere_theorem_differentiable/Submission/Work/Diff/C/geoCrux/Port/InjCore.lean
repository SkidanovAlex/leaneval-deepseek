import Mathlib
import Submission.Work.Diff.C.geoCrux.Port.CoreStmts
import Submission.Work.Diff.C.geoCrux.injectivity_radius
import Submission.Work.Diff.C.fb_cap_depth

set_option backward.isDefEq.respectTransparency.types false

/-!
# The injectivity radius from the C-area hypotheses, without a global diameter bound

`Work.Diff.C.geoCrux.Port.InjRadiusCoreProp` is the injectivity-radius input
`InjAtLeast hmet x (π - arccos (1-c))` for **every** point `x`, from the C-area hypotheses
(`hsmC`, `hHess`, `hcont`, `hgrad`, `4 ε₁ π < c`, `c ≤ 1/4`) alone — i.e. *without* the global
diameter bound `hdiam : ∀ x y, rdist x y ≤ π` that
`Work.Diff.C.geoCrux.injectivity_radius` (`InjectivityProp`) carries.

## Route

The proof is the same Grönwall/ODE argument as in `geoCrux/injectivity_radius.lean` (via
`geoCrux/rayCore.lean`), except that the hypothesis `hdiam` is *never used*: everywhere the argument
needs `rdist q` to be `C^∞` with unit gradient it is at a point `y` with
`0 < rdist q y < π - arccos (1-c)`, and there the local statement

* `Work.Diff.C.fbcap_rdist_smooth` (`Diff/C/fb_cap_depth.lean`, proved)

supplies smoothness and the eikonal *from `hsmC`/`hgrad` alone* (the `rdist q = arccos ∘ fcos q`
trick), with no diameter bound.  So this file is a faithful copy of the analytic core of
`rayCore.lean` and of the `injectivity_radius.lean` helpers, with the (inert) `hdiam` argument
removed and with `rdist_smooth_eikonal` replaced by the `hdiam`-free
`InjCore.rdist_smooth_ball`.

The copies live in the namespace `Work.Diff.C.geoCrux.InjCore` (they cannot shadow the originals,
which are imported), and `C_eq_one_of_deriv_bound` — the scalar Grönwall step, which never had a
`hdiam` hypothesis — is used from `Work.Diff.C.geoCrux.RayCore` directly.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C.geoCrux.Port

namespace InjCore

/-- **`rdist q` is `C^∞` at `y` when `0 < rdist q y < π - arccos (1-c)`.**

This is the `hdiam`-free replacement of `Work.Diff.C.GeoCrux.RdistSmoothProp` /
`Work.Diff.C.GeoCrux.rdist_smooth_eikonal`: since `π - arccos (1-c) < π`, the point `y` is strictly
interior to the ball, so `fcos q y = cos (rdist q y) > cos (π - arccos (1-c)) = -1 + c` and
`rdist q y < π`; `Work.Diff.C.fbcap_rdist_smooth` then gives the conclusion without any global
bound on `rdist`. -/
theorem rdist_smooth_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (q y : M) (hy0 : 0 < rdist (I := I) (M := M) q y)
    (hyπ : rdist (I := I) (M := M) q y < Real.pi - Real.arccos (1 - c)) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) y := by
  have hρπ : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
    have h : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg (1 - c)
    linarith
  have hyπ' : rdist (I := I) (M := M) q y < Real.pi := lt_of_lt_of_le hyπ hρπ
  have hρcos : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
    rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hx : -1 + c < fcos (I := I) (M := M) q y := by
    have hcos : Real.cos (Real.pi - Real.arccos (1 - c))
        < Real.cos (rdist (I := I) (M := M) q y) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hy0) hρπ hyπ
    rw [hρcos] at hcos
    exact hcos
  exact (Work.Diff.C.fbcap_rdist_smooth (I := I) (M := M) (cov := cov) hmet hc hy0 hyπ' hx
    (fun z hz => hsmC q z hz) (fun z hz => hgrad q z hz)).1

/-- **The distance along a radial ray grows with derivative `⟪∇d, γ'⟫`.** -/
theorem hasDerivAt_rdist_ray'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {q : M} {ξ : TangentSpace I q} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht0 : 0 < t)
    (hrd0 : 0 < rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
    (hrd : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) < Real.pi - Real.arccos (1 - c)) :
    HasDerivAt (fun s : ℝ => rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)))
      (Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)) t)) t := by
  have hξ' : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ'; norm_num at hξ'
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ) with hγ
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    rdist_smooth_ball (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad q (γ t) hrd0 hrd
  have hgmd : MDifferentiableAt I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    hsm.mdifferentiableAt (by simp)
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξ0
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (hγsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
  have hcomp : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ, ℝ))
      ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ) t :=
    hgmd.comp t hγmd
  have hval : deriv ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ) t
      = Inner.inner ℝ
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t))
          (Submission.Geodesic.curveVelocity (I := I) γ t) := by
    have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun z : M ↦ rdist (I := I) (M := M) q z) (γ := γ) (t := t) hgmd hγmd
    rw [← h, ← Work.Diff.C.inner_rgrad_mvfderiv_local
      (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)]
    rfl
  have hd : HasDerivAt ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ)
      (deriv ((fun z : M ↦ rdist (I := I) (M := M) q z) ∘ γ) t) t :=
    (hcomp.differentiableAt).hasDerivAt
  rw [hval] at hd
  exact hd

/-! ## Two algebraic facts about the orthogonal part of `γ'` -/

/-- **The orthogonal part of a unit vector is `1 - C²` long.**

For `g, w` with `⟪g,g⟫ = 1`, `⟪w,w⟫ = 1` and `C = ⟪g,w⟫`, the vector `w - C • g` is orthogonal to `g`
and has squared norm `1 - C²`. -/
theorem inner_perp_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (g w : V)
    (C : ℝ) (hg : Inner.inner ℝ g g = 1) (hw : Inner.inner ℝ w w = 1)
    (hC : C = Inner.inner ℝ g w) :
    Inner.inner ℝ (w - C • g) (w - C • g) = 1 - C ^ 2 := by
  have hgw : Inner.inner ℝ g w = C := hC.symm
  have hwg : Inner.inner ℝ w g = C := by rw [real_inner_comm]; exact hgw
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hg, hw, hgw, hwg]
  ring

/-- The orthogonal part `w - C • g` is orthogonal to `g`. -/
theorem inner_perp_eq_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (g w : V)
    (C : ℝ) (hg : Inner.inner ℝ g g = 1) (hC : C = Inner.inner ℝ g w) :
    Inner.inner ℝ g (w - C • g) = 0 := by
  simp only [inner_sub_right, real_inner_smul_right, hg, hC]
  ring

/-! ## The eikonal equation holds *eventually* on the region -/

/-- **The gradient of the distance is a unit vector on a neighbourhood.**

If `0 < rdist q x < π - arccos (1-c)` then `⟪∇(rdist q), ∇(rdist q)⟫ = 1` holds on a neighbourhood of
`x`: on the region `{0 < rdist q < π - arccos (1-c)}` the function `fcos q = cos ∘ rdist q` satisfies
the eikonal equation (`hgrad`) and `∇(fcos q) = -sin (rdist q) • ∇(rdist q)`, so
`sin²(rdist q)·⟪∇(rdist q), ∇(rdist q)⟫ = 1 - cos²(rdist q) = sin²(rdist q)`. -/
theorem eventually_eikonal_rdist'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {q x : M} (hx0 : 0 < rdist (I := I) (M := M) q x)
    (hxρ : rdist (I := I) (M := M) q x < Real.pi - Real.arccos (1 - c)) :
    ∀ᶠ y in 𝓝 x, Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y) = 1 := by
  have hρπ : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
    have h : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg (1 - c)
    linarith
  have hρcos : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
    rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hcont' : Continuous (fun y : M ↦ rdist (I := I) (M := M) q y) :=
    rdist_continuous (I := I) (M := M) q
  have h1 : ∀ᶠ y in 𝓝 x, 0 < rdist (I := I) (M := M) q y :=
    hcont'.continuousAt (isOpen_Ioi.mem_nhds hx0)
  have h2 : ∀ᶠ y in 𝓝 x, rdist (I := I) (M := M) q y < Real.pi - Real.arccos (1 - c) :=
    hcont'.continuousAt (isOpen_Iio.mem_nhds hxρ)
  filter_upwards [h1, h2] with y hy0 hyρ
  have hyπ : rdist (I := I) (M := M) q y < Real.pi := lt_of_lt_of_le hyρ hρπ
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) y :=
    rdist_smooth_ball (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad q y hy0 hyρ
  have hfcos_gt : -1 + c < fcos (I := I) (M := M) q y := by
    have hcos : Real.cos (Real.pi - Real.arccos (1 - c)) < Real.cos (rdist (I := I) (M := M) q y) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hy0.le hρπ hyρ
    rw [hρcos] at hcos
    exact hcos
  have hgf : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y
      = (-Real.sin (rdist (I := I) (M := M) q y))
        • rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y :=
    Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) hsm
  have hg := hgrad q y hfcos_gt
  rw [hgf] at hg
  simp only [real_inner_smul_left, real_inner_smul_right] at hg
  have hsin : Real.sin (rdist (I := I) (M := M) q y) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ)
  have hfcosval : fcos (I := I) (M := M) q y = Real.cos (rdist (I := I) (M := M) q y) := rfl
  rw [hfcosval] at hg
  have hg' : Real.sin (rdist (I := I) (M := M) q y) ^ 2
      * Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
      = 1 - Real.cos (rdist (I := I) (M := M) q y) ^ 2 := by
    nlinarith [hg]
  have hkey : Real.sin (rdist (I := I) (M := M) q y) ^ 2
      * Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
      = Real.sin (rdist (I := I) (M := M) q y) ^ 2 := by
    rw [hg', Real.sin_sq]
  have hss : 0 < Real.sin (rdist (I := I) (M := M) q y) ^ 2 := pow_pos (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ) 2
  nlinarith [hkey, hss]

/-! ## The derivative of `C` along the ray -/

/-- **The derivative of the pairing `C`.**  Along the unit ray `γ t = GExp q (t • ξ)`, the function
`C t = ⟪∇(rdist q)(γ t), γ'(t)⟫` is differentiable at `t` with derivative
`Hess(rdist q)(γ t)(γ'(t), γ'(t))`, whenever `0 < rdist q (γ t) < π - arccos (1-c)`.

(This is the `hCderiv` step isolated out of `deriv_psi_le'`, so that the Grönwall assembly can use
the differentiability and continuity of `C` on its own.) -/
theorem hasDerivAt_C'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {q : M} {ξ : TangentSpace I q} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht0 : 0 < t)
    (hrd0 : 0 < rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
    (hrd : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) < Real.pi - Real.arccos (1 - c)) :
    HasDerivAt (fun τ : ℝ => Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (τ • ξ)))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) τ))
      (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) t)
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) t)) t := by
  classical
  have hξ' : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ'; norm_num at hξ'
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ) with hγ
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    rdist_smooth_ball (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad q (γ t) hrd0 hrd
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξ0
  have hnorm : ‖Submission.Geodesic.curveVelocity (I := I) γ t‖ = 1 := by
    have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hξ0
      (s := t) (ne_of_gt ht0)
    rw [hγ]
    rw [h, hξ']
  have hne : Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; norm_num at hnorm
  have hfd : MDiffAt (T% (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)))
      (γ t) :=
    (Work.Diff.C.grad_smoothAt (I := I) (F := fun z : M ↦ rdist (I := I) (M := M) q z) (x := γ t)
      hsm).mdifferentiableAt (by simp)
  have hCderiv : HasDerivAt (fun τ : ℝ => Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
      (Submission.Geodesic.curveVelocity (I := I) γ τ))
      (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)) t := by
    have h := Work.Diff.C.hasDerivAt_secondDeriv_along_geodesic (cov := cov) hmet
      (V := Set.univ) isOpen_univ (t := t) (by simp) hγsm
      (fun τ _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hξ0 τ)
      hne hfd
    have hfun : (fun τ : ℝ => mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ)
        (Submission.Geodesic.curveVelocity (I := I) γ τ))
        = fun τ : ℝ => Inner.inner ℝ
            (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
            (Submission.Geodesic.curveVelocity (I := I) γ τ) := by
      funext τ
      rw [Work.Diff.C.inner_rgrad_mvfderiv_local]
    rw [hfun] at h
    exact h
  exact hCderiv

/-! ## Step 1: the `Ψ`-derivative bound along the ray -/

/-- **The `1 - C²` derivative bound.**  Along the unit ray `γ t = GExp q (t • ξ)`, with
`C t = ⟪∇(rdist q)(γ t), γ'(t)⟫` and at a time `t` where `0 < rdist q (γ t) < π - arccos (1-c)`,

`(1 - C²)'(t) ≤ (2 (1+ε₁) / sin (rdist q (γ t))) · (1 - C t²)`.

This is the analytic input of the Grönwall step: `C' = Hess(rdist q)(γ',γ')`, the orthogonal part
`γ'⊥ = γ' - C • ∇(rdist q)` (so `rhess_eq_rhess_sub_smul` replaces `γ'` by `γ'⊥` and its squared
length is `1 - C²`), the shape-operator bound on `γ'⊥ ⊥ ∇(rdist q)`, and `|cot| ≤ 1/sin`. -/
theorem deriv_psi_le'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {q : M} {ξ : TangentSpace I q} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht0 : 0 < t)
    (hrd0 : 0 < rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
    (hrd : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) < Real.pi - Real.arccos (1 - c)) :
    deriv (fun s : ℝ => 1 - (Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)))
        (Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) s)) ^ 2) t
      ≤ (2 * (1 + ε₁) / Real.sin (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))))
        * (1 - (Inner.inner ℝ
            (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
              (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
            (Submission.Geodesic.curveVelocity (I := I)
              (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (u • ξ)) t)) ^ 2) := by
  classical
  have hξ' : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ'; norm_num at hξ'
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ) with hγ
  set d : ℝ := rdist (I := I) (M := M) q (γ t) with hd
  set g : TangentSpace I (γ t) := rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
    with hg
  set w : TangentSpace I (γ t) := Submission.Geodesic.curveVelocity (I := I) γ t with hw
  -- basic facts
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) :=
    rdist_smooth_ball (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad q (γ t) hrd0 hrd
  have heik : Inner.inner ℝ g g = 1 := by
    have h := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (x := γ t) (ne_of_gt hrd0) hsm
    rw [hg]; exact h
  have heik' : ∀ᶠ y in 𝓝 (γ t), Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y)
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) y) = 1 :=
    eventually_eikonal_rdist' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
      hsmC hHess hcont hgrad (q := q) (x := γ t) hrd0 hrd
  have hw_unit : Inner.inner ℝ w w = 1 := by
    have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hξ0
      (s := t) (ne_of_gt ht0)
    rw [hw, hγ, real_inner_self_eq_norm_sq, h, hξ']
    norm_num
  have hgt0 : 0 < d := by rw [hd]; exact hrd0
  have hdπ : d < Real.pi := by
    have h : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
      have := Real.arccos_nonneg (1 - c); linarith
    rw [hd]; exact lt_of_lt_of_le hrd h
  -- the derivative of `C`
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξ0
  have hne : Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := by
    rw [hw] at hw_unit
    intro h0; rw [h0] at hw_unit; norm_num at hw_unit
  have hfd : MDiffAt (T% (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)))
      (γ t) :=
    (Work.Diff.C.grad_smoothAt (I := I) (F := fun z : M ↦ rdist (I := I) (M := M) q z) (x := γ t)
      hsm).mdifferentiableAt (by simp)
  have hCderiv : HasDerivAt (fun τ : ℝ => Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
      (Submission.Geodesic.curveVelocity (I := I) γ τ))
      (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)
        (Submission.Geodesic.curveVelocity (I := I) γ t)) t := by
    have h := Work.Diff.C.hasDerivAt_secondDeriv_along_geodesic (cov := cov) hmet
      (V := Set.univ) isOpen_univ (t := t) (by simp) hγsm
      (fun τ _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hξ0 τ)
      hne hfd
    have hfun : (fun τ : ℝ => mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ)
        (Submission.Geodesic.curveVelocity (I := I) γ τ))
        = fun τ : ℝ => Inner.inner ℝ
            (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ τ))
            (Submission.Geodesic.curveVelocity (I := I) γ τ) := by
      funext τ
      rw [Work.Diff.C.inner_rgrad_mvfderiv_local]
    rw [hfun] at h
    exact h
  -- the shape-operator bound on the orthogonal part
  have hperp_self : Inner.inner ℝ (w - (Inner.inner ℝ g w) • g) (w - (Inner.inner ℝ g w) • g)
      = 1 - (Inner.inner ℝ g w) ^ 2 :=
    inner_perp_self g w _ heik hw_unit rfl
  have hperp_orth : Inner.inner ℝ g (w - (Inner.inner ℝ g w) • g) = 0 :=
    inner_perp_eq_zero g w _ heik rfl
  have hgf : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) (γ t)
      = (-Real.sin d) • g := by
    have h := Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) hsm
    rw [hg, hd]
    exact h
  have hVorth : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) (γ t))
      (w - (Inner.inner ℝ g w) • g) = 0 := by
    rw [hgf, real_inner_smul_left, hperp_orth, mul_zero]
  have hshape := Work.Diff.C.rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov)
    (c := c) (ε := ε₁) (q := q) (hHess q)
    (x := γ t) (by
      -- -1 + c < fcos q (γ t)
      have hρcos : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
        rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]; ring
      have hcos : Real.cos (Real.pi - Real.arccos (1 - c)) < Real.cos d :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hgt0.le (by
          have h : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
            have := Real.arccos_nonneg (1 - c); linarith
          exact h) (by rw [hd]; exact hrd)
      rw [hρcos] at hcos
      exact hcos)
    hsm hgt0 hdπ (w - (Inner.inner ℝ g w) • g) hVorth
  -- the decomposition
  have hdecomp : Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w
      = Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t)
          (w - (Inner.inner ℝ g w) • g) (w - (Inner.inner ℝ g w) • g) := by
    have h := Work.Diff.C.GeoCrux.rhess_eq_rhess_sub_smul (I := I) (M := M) (cov := cov) hmet htor
      (F := fun z : M ↦ rdist (I := I) (M := M) q z) (x := γ t) hsm heik' w
    simpa only [hg] using h
  -- the two-sided bound on `C'`
  have hbound : |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w
      - Real.cot d * (1 - (Inner.inner ℝ g w) ^ 2)|
      ≤ (ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
    rw [hdecomp, ← hperp_self]
    exact hshape
  have hsinpos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hgt0 hdπ
  have hgn : ‖g‖ = 1 := by
    have h : ‖g‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact heik
    nlinarith [norm_nonneg g]
  have hwn : ‖w‖ = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hw_unit
    nlinarith [norm_nonneg w]
  have hCabs : |Inner.inner ℝ g w| ≤ 1 := by
    have h := abs_real_inner_le_norm g w
    rw [hgn, hwn, mul_one] at h
    exact h
  have hPsi_nn : 0 ≤ 1 - (Inner.inner ℝ g w) ^ 2 := by
    nlinarith [abs_le.mp hCabs]
  -- assemble
  have hPsi' : HasDerivAt (fun s : ℝ => 1 - (Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) (γ s))
      (Submission.Geodesic.curveVelocity (I := I) γ s)) ^ 2)
      (-(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
        (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)) t := by
    have h := hCderiv.pow 2
    have h2 := h.const_sub 1
    simpa [hg, hw, mul_comm, mul_left_comm, mul_assoc] using h2
  rw [hPsi'.deriv]
  have hC'b : |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w|
      ≤ (|Real.cot d| + ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
    have h := hbound
    have := abs_le.mp h
    have hA : Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w
        ≤ Real.cot d * (1 - (Inner.inner ℝ g w) ^ 2)
          + (ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by linarith [this.2]
    have hB : Real.cot d * (1 - (Inner.inner ℝ g w) ^ 2)
          - (ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2)
        ≤ Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w := by
      linarith [this.1]
    have hcot : |Real.cot d| ≤ 1 / Real.sin d := by
      rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos]
      rw [div_le_div_iff_of_pos_right hsinpos]
      exact Real.abs_cos_le_one d
    rw [abs_le]
    constructor
    · have hc : -(Real.cot d) ≤ |Real.cot d| := neg_le_abs _
      nlinarith [hB, hPsi_nn, hsinpos, hc]
    · have hc : Real.cot d ≤ |Real.cot d| := le_abs_self _
      nlinarith [hA, hPsi_nn, hc, hε₁, hsinpos]
  have hkey : -(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
      (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)
      ≤ (2 * (1 + ε₁) / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
    have h1 : -(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
        (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)
        ≤ |2 * Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w| := by
      have h := le_abs_self (-(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
        (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w))
      rwa [abs_mul, abs_neg] at h
    have h2 : |2 * Inner.inner ℝ g w| = 2 * |Inner.inner ℝ g w| := by
      rw [abs_mul]; norm_num
    have h3 : |Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
          (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w|
        ≤ 1 * ((|Real.cot d| + ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2)) :=
      mul_le_mul hCabs hC'b (abs_nonneg _) (by norm_num)
    have hcot' : |Real.cot d| * Real.sin d ≤ 1 := by
      rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos,
        div_mul_cancel₀ _ (ne_of_gt hsinpos)]
      exact Real.abs_cos_le_one d
    have hkey2 : 2 * (|Real.cot d| + ε₁ / Real.sin d) ≤ 2 * (1 + ε₁) / Real.sin d := by
      have hdiv : ε₁ / Real.sin d * Real.sin d = ε₁ := by
        field_simp
      rw [le_div_iff₀ hsinpos]
      nlinarith [hcot', hdiv]
    have hlast : 2 * (1 * ((|Real.cot d| + ε₁ / Real.sin d)
          * (1 - (Inner.inner ℝ g w) ^ 2)))
        ≤ (2 * (1 + ε₁) / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hkey2 hPsi_nn
      linarith [h]
    calc -(2 * Inner.inner ℝ g w) * (Work.Diff.C.rhess cov
          (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w)
        ≤ |2 * Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w| := h1
      _ = 2 * |Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w| := by rw [h2]
      _ = 2 * (|Inner.inner ℝ g w| * |Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) q z) (γ t) w w|) := by ring
      _ ≤ 2 * (1 * ((|Real.cot d| + ε₁ / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2))) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ (2 * (1 + ε₁) / Real.sin d) * (1 - (Inner.inner ℝ g w) ^ 2) := hlast
  rw [hd, hg, hw] at hkey
  exact hkey


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The pointwise facts along the ray.**  At a time `t > 0` where the ray is at distance
`0 < rayD t < π - arccos (1-c)` from `x`:

* `|rayC t| ≤ 1` (Cauchy–Schwarz with the unit eikonal gradient and the unit-speed ray),
* `rayC` is differentiable at `t`,
* `rayD` is differentiable at `t` with derivative `rayC t`. -/
lemma ray_pointwise'
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) {t : ℝ} (ht : 0 < t)
    (hrd0 : 0 < rayD hmet x ξ t) (hrd : rayD hmet x ξ t < Real.pi - Real.arccos (1 - c)) :
    |rayC hmet x ξ t| ≤ 1 ∧ DifferentiableAt ℝ (rayC hmet x ξ) t ∧
      HasDerivAt (rayD hmet x ξ) (rayC hmet x ξ t) t := by
  have hξn : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξn
    norm_num at hξn
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) x z)
      (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)) :=
    rdist_smooth_ball (I := I) (M := M) (cov := cov) hmet htor hc hc1
      hε₁ hnum2 hsmC hHess hcont hgrad x _ hrd0 hrd
  have heik : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))) = 1 :=
    rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor (q := x) (x := _)
      (ne_of_gt hrd0) hsm
  have hvn : ‖Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ ↦
      Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) t‖ = 1 := by
    rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet x hξ0
      (ne_of_gt ht), hξn]
  have hgn : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
      (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))‖ = 1 := by
    have h : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact heik
    nlinarith [norm_nonneg (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
      (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)))]
  refine ⟨?_, ?_, ?_⟩
  · have h := abs_real_inner_le_norm
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) x z)
        (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)))
      (Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ ↦
        Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) t)
    rwa [hgn, hvn, one_mul] at h
  · exact (hasDerivAt_C' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
      hcont hgrad hξ ht hrd0 hrd).differentiableAt
  · exact hasDerivAt_rdist_ray' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
      hHess hcont hgrad hξ ht hrd0 hrd

/-- `rayC` is continuous at every point of a window on which the ray is at distance in `(0, ρ)`. -/
lemma continuousOn_rayC'
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) {a b : ℝ} (ha : 0 < a)
    (hwin : ∀ t ∈ Set.Icc a b,
      0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < Real.pi - Real.arccos (1 - c)) :
    ContinuousOn (rayC hmet x ξ) (Set.Icc a b) := by
  intro t ht
  exact ((ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
    hcont hgrad hξ (lt_of_lt_of_le ha ht.1) (hwin t ht).1
    (hwin t ht).2).2.1.continuousAt).continuousWithinAt

/-- **The Grönwall endpoint step.**  If `rayC ≡ 1` on `[a,b]`, the ray is at distance in `(0,ρ)`
on that window and `rayD a = a`, then `rayD b = b`.

The mean value theorem applied to `f := rayD - id` (with `f' = 0` on `[a,b]`, from the
differentiability at every point of the window and `rayC ≡ 1`) gives `f b = f a = 0`. -/
lemma rayD_eq_of_rayC_eq_one'
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b)
    (hwin : ∀ t ∈ Set.Icc a b,
      0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < Real.pi - Real.arccos (1 - c))
    (haD : rayD hmet x ξ a = a)
    (hC1 : ∀ t ∈ Set.Icc a b, rayC hmet x ξ t = 1) :
    rayD hmet x ξ b = b := by
  have hfderiv : ∀ t ∈ Set.Icc a b,
      HasFDerivWithinAt (fun s : ℝ ↦ rayD hmet x ξ s - s) (0 : ℝ →L[ℝ] ℝ) (Set.Icc a b) t := by
    intro t ht
    have h1 : HasDerivAt (rayD hmet x ξ) (rayC hmet x ξ t) t :=
      (ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont
        hgrad hξ (lt_of_lt_of_le ha ht.1) (hwin t ht).1 (hwin t ht).2).2.2
    have h2 : HasDerivAt (fun s : ℝ ↦ rayD hmet x ξ s - s) (rayC hmet x ξ t - 1) t :=
      h1.sub (hasDerivAt_id t)
    have h3 : rayC hmet x ξ t - 1 = 0 := by rw [hC1 t ht]; ring
    rw [h3] at h2
    simpa using h2.hasFDerivAt.hasFDerivWithinAt
  have hmvt : ‖(rayD hmet x ξ b - b) - (rayD hmet x ξ a - a)‖ ≤ (0 : ℝ) * ‖b - a‖ :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ)
      (s := Set.Icc a b) (f := fun s : ℝ ↦ rayD hmet x ξ s - s)
      (f' := fun _ : ℝ ↦ (0 : ℝ →L[ℝ] ℝ)) (C := 0) (x := a) (y := b)
      hfderiv (fun _ _ => by simp) (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rw [zero_mul] at hmvt
  have hzero : (rayD hmet x ξ b - b) - (rayD hmet x ξ a - a) = 0 :=
    norm_eq_zero.mp (le_antisymm hmvt (norm_nonneg _))
  have ha0 : rayD hmet x ξ a - a = 0 := by rw [haD]; ring
  rw [ha0, sub_zero] at hzero
  linarith


/-- **Every ray of length at most `π - arccos (1-c)` is minimising.**

This is the geometric core of `InjectivityProp`: under the C-area hypotheses, for a unit vector
`ξ` at `x` and every `t ∈ [0, π - arccos (1-c)]` one has `rdist x (GExp x (t • ξ)) = t`.

The proof is the closed-and-open argument on the set
`S := {T | T ≤ ρ ∧ ∀ t ∈ [0,T], rdist x (GExp x (t • ξ)) = t}`:

* `S` contains a small interval by `Work.Diff.C.ray_minimising`;
* if `T := sSup S < ρ`, then `T ∈ S` (closedness: `rdist x` is continuous, so `{t | rayD t = t}`
  is closed), and the Grönwall step at `T` produces `T + δ ∈ S` with
  `δ = min (T/2) ((ρ-T)/2) > 0`, contradicting the definition of `T`. -/
theorem ray_minimising_upto'
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁
      (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    {x : M} {ξ : TangentSpace I x} (hξ : Inner.inner ℝ ξ ξ = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi - Real.arccos (1 - c)), rayD hmet x ξ t = t := by
  classical
  haveI : RegularSpace M := inferInstance
  haveI : ConnectedSpace M := inferInstance
  have hξn : ‖ξ‖ = 1 := by
    have h : ‖ξ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hξ
    nlinarith [norm_nonneg ξ]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξn
    norm_num at hξn
  set ρ : ℝ := Real.pi - Real.arccos (1 - c) with hρdef
  have hρπ : ρ ≤ Real.pi := by
    rw [hρdef]; linarith [Real.arccos_nonneg (1 - c)]
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    have h : Real.arccos (1 - c) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    linarith
  -- continuity of the ray and of `rayD`
  have hγcont : Continuous (fun s : ℝ ↦
      Submission.GlobalExp.GExp (cov := cov) hmet x (s • ξ)) :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hξ0).continuous
  have hDcont : Continuous (rayD hmet x ξ) :=
    (rdist_continuous (I := I) (M := M) x).comp hγcont
  -- small times are minimising
  obtain ⟨t₁, ht₁pos, ht₁ρ, ht₁⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ ρ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) t₁, rayD hmet x ξ t = t := by
    obtain ⟨ε, hε0, hε⟩ := ray_minimising (I := I) (M := M) (cov := cov) hmet htor x ξ hξ0
    refine ⟨min (ε / 2) ρ, lt_min (by linarith) hρ0, min_le_right _ _, ?_⟩
    intro t ht
    have hlt : |t| < ε := by
      have h2 : t ≤ ε / 2 := le_trans ht.2 (min_le_left _ _)
      rw [abs_of_nonneg ht.1]; linarith
    have h := hε t hlt
    show rdist (I := I) (M := M) x (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)) = t
    rw [rdist, h, hξn, mul_one, abs_of_nonneg ht.1, ENNReal.toReal_ofReal ht.1]
  -- the good set
  set S : Set ℝ := {T : ℝ | T ≤ ρ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, rayD hmet x ξ t = t} with hSdef
  have hSne : S.Nonempty := ⟨t₁, ht₁ρ, ht₁⟩
  have hbdd : BddAbove S := ⟨ρ, fun T hT => hT.1⟩
  set T : ℝ := sSup S with hTdef
  have hTρ : T ≤ ρ := csSup_le hSne fun t ht => ht.1
  have hTpos : 0 < T := lt_of_lt_of_le ht₁pos (le_csSup hbdd ⟨ht₁ρ, ht₁⟩)
  have hltS : ∀ t : ℝ, t < T → t ∈ S := by
    intro t ht
    obtain ⟨T', hT'S, htT'⟩ := exists_lt_of_lt_csSup hSne ht
    exact ⟨le_trans htT'.le hT'S.1, fun s hs => hT'S.2 s ⟨hs.1, le_trans hs.2 htT'.le⟩⟩
  have hTS : T ∈ S := by
    refine ⟨hTρ, fun t ht => ?_⟩
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact (hltS t h).2 t ⟨ht.1, le_rfl⟩
    · have hZcl : IsClosed {s : ℝ | rayD hmet x ξ s = s} :=
        isClosed_eq hDcont continuous_id
      have hsub : Set.Ioo (0 : ℝ) T ⊆ {s : ℝ | rayD hmet x ξ s = s} := by
        intro s hs
        exact (hltS s hs.2).2 s ⟨hs.1.le, le_rfl⟩
      have hmem : T ∈ closure (Set.Ioo (0 : ℝ) T) := by
        rw [closure_Ioo (a := (0 : ℝ)) (b := T) (ne_of_lt hTpos)]
        exact ⟨le_of_lt hTpos, le_rfl⟩
      have hTZ : rayD hmet x ξ T = T := (hZcl.closure_subset_iff).mpr hsub hmem
      rw [h]
      exact hTZ
  -- the main claim
  have hTeq : T = ρ := by
    rcases lt_or_eq_of_le hTρ with hlt | heq
    · exfalso
      set δ : ℝ := min (T / 2) ((ρ - T) / 2) with hδdef
      have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
      have hδT : δ ≤ T / 2 := by rw [hδdef]; exact min_le_left _ _
      have hδρ : δ ≤ (ρ - T) / 2 := by rw [hδdef]; exact min_le_right _ _
      have hTδρ : T + δ < ρ := by linarith
      have hTa : rayD hmet x ξ T = T := hTS.2 T ⟨le_of_lt hTpos, le_rfl⟩
      -- the window `[T, T+δ]` stays in `(0,ρ)`
      have hwin : ∀ t ∈ Set.Icc T (T + δ),
          0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < ρ := by
        intro t ht
        have htT : T ≤ t := ht.1
        have htδ : t ≤ T + δ := ht.2
        have hle : rayD hmet x ξ t ≤ t :=
          rayD_le (I := I) (M := M) (cov := cov) hmet hξn (le_of_lt (lt_of_lt_of_le hTpos htT))
        constructor
        · have htri : rayD hmet x ξ T ≤ rayD hmet x ξ t
              + rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))
                (Submission.GlobalExp.GExp (cov := cov) hmet x (T • ξ)) :=
            eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor x
              (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))
              (Submission.GlobalExp.GExp (cov := cov) hmet x (T • ξ))
          have hsub : rdist (I := I) (M := M)
              (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ))
              (Submission.GlobalExp.GExp (cov := cov) hmet x (T • ξ)) ≤ t - T := by
            rw [rdist_comm_aux]
            exact eik_rdist_GExp_ray_sub_le (I := I) (M := M) (cov := cov) hmet x hξn
              (le_of_lt hTpos) htT
          have h3 : t ≤ T + T / 2 := by linarith
          linarith
        · linarith
      -- `rayC T = 1`, from `rayC ≡ 1` on `[T/2, T]`
      have hwin2 : ∀ t ∈ Set.Icc (T / 2) T,
          0 < rayD hmet x ξ t ∧ rayD hmet x ξ t < ρ := by
        intro t ht
        have hd : rayD hmet x ξ t = t :=
          hTS.2 t ⟨le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1, ht.2⟩
        rw [hd]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hs0 : 0 < T / 2 := by linarith
      have h25 : T / 2 < T := by linarith
      have hCT : rayC hmet x ξ T = 1 := by
        have hev : (rayD hmet x ξ) =ᶠ[𝓝 (T / 2)] (fun t : ℝ ↦ t) := by
          filter_upwards [Ioo_mem_nhds hs0 h25] with t ht
          exact hTS.2 t ⟨ht.1.le, le_of_lt ht.2⟩
        have h1 : HasDerivAt (rayD hmet x ξ) 1 (T / 2) :=
          (hasDerivAt_id (T / 2)).congr_of_eventuallyEq hev
        have h2 : HasDerivAt (rayD hmet x ξ) (rayC hmet x ξ (T / 2)) (T / 2) :=
          (ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
            hcont hgrad hξ hs0 (hwin2 (T / 2) ⟨le_rfl, le_of_lt h25⟩).1
            (hwin2 (T / 2) ⟨le_rfl, le_of_lt h25⟩).2).2.2
        have hd1 : deriv (rayD hmet x ξ) (T / 2) = 1 := h1.deriv
        have hd2 : deriv (rayD hmet x ξ) (T / 2) = rayC hmet x ξ (T / 2) := h2.deriv
        rw [hd2] at hd1
        have hCs : rayC hmet x ξ (T / 2) = 1 := hd1
        have hkey := RayCore.C_eq_one_of_deriv_bound (A := rayD hmet x ξ) (C := rayC hmet x ξ)
          (ε := ε₁) (t₁ := T / 2) (T := T) hε₁ (by linarith)
          hDcont.continuousOn
          (continuousOn_rayC' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hξ hs0 hwin2)
          (fun t ht => (hwin2 t ht).1)
          (fun t ht => by
            have hd : rayD hmet x ξ t = t :=
              hTS.2 t ⟨le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1, ht.2⟩
            rw [hd]; linarith [ht.2, hlt, hρπ])
          (fun t ht => (ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
            hsmC hHess hcont hgrad hξ (lt_of_lt_of_le hs0 ht.1) (hwin2 t ht).1
            (hwin2 t ht).2).1)
          hCs
          (fun t ht => (ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
            hsmC hHess hcont hgrad hξ (lt_of_lt_of_le hs0 (le_of_lt ht.1))
            (hwin2 t ⟨ht.1.le, ht.2.le⟩).1 (hwin2 t ⟨ht.1.le, ht.2.le⟩).2).2.1)
          (fun t ht => deriv_psi_le' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
            hsmC hHess hcont hgrad hξ (lt_of_lt_of_le hs0 (le_of_lt ht.1))
            (hwin2 t ⟨ht.1.le, ht.2.le⟩).1 (hwin2 t ⟨ht.1.le, ht.2.le⟩).2)
        exact hkey T ⟨by linarith, le_rfl⟩
      -- `rayC = 1` on the whole window `[T, T+δ]`
      have hC1 : ∀ t ∈ Set.Icc T (T + δ), rayC hmet x ξ t = 1 := by
        refine RayCore.C_eq_one_of_deriv_bound (A := rayD hmet x ξ) (C := rayC hmet x ξ) (ε := ε₁)
          (t₁ := T) (T := T + δ) hε₁ (by linarith) hDcont.continuousOn ?_ ?_ ?_ ?_ hCT ?_ ?_
        · exact continuousOn_rayC' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hξ hTpos hwin
        · intro t ht
          exact (hwin t ht).1
        · intro t ht
          have hle : rayD hmet x ξ t ≤ t :=
            rayD_le (I := I) (M := M) (cov := cov) hmet hξn (le_trans (le_of_lt hTpos) ht.1)
          linarith [ht.2, hTδρ, hρπ]
        · intro t ht
          exact (ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hξ (lt_of_lt_of_le hTpos ht.1) (hwin t ht).1
            (hwin t ht).2).1
        · intro t ht
          exact (ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
            hHess hcont hgrad hξ (lt_of_lt_of_le hTpos (le_of_lt ht.1))
            (hwin t ⟨ht.1.le, ht.2.le⟩).1 (hwin t ⟨ht.1.le, ht.2.le⟩).2).2.1
        · intro t ht
          exact deriv_psi_le' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
            hcont hgrad hξ (lt_of_lt_of_le hTpos (le_of_lt ht.1))
            (hwin t ⟨ht.1.le, ht.2.le⟩).1 (hwin t ⟨ht.1.le, ht.2.le⟩).2
      -- the endpoint
      have hDb : rayD hmet x ξ (T + δ) = T + δ :=
        rayD_eq_of_rayC_eq_one' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
          hHess hcont hgrad hξ hTpos (by linarith) hwin hTa hC1
      -- hence `T + δ ∈ S`, contradicting the definition of `T`
      have hed : Manifold.riemannianEDist I x
          (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))
          = ENNReal.ofReal (T + δ) := by
        have hfin : Manifold.riemannianEDist I x
            (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ)) ≠ ⊤ :=
          (Submission.HopfRinow.riemannianEDist_lt_top hmet htor x _).ne
        have htr : (Manifold.riemannianEDist I x
            (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))).toReal = T + δ := hDb
        calc Manifold.riemannianEDist I x
              (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))
            = ENNReal.ofReal ((Manifold.riemannianEDist I x
                (Submission.GlobalExp.GExp (cov := cov) hmet x ((T + δ) • ξ))).toReal) :=
              (ENNReal.ofReal_toReal hfin).symm
          _ = ENNReal.ofReal (T + δ) := by rw [htr]
      have hTδS : T + δ ∈ S := by
        refine ⟨le_of_lt hTδρ, fun t ht => ?_⟩
        by_cases h : t ≤ T
        · exact hTS.2 t ⟨ht.1, h⟩
        · have hgt : T < t := lt_of_not_ge h
          have hmem : (T + δ) ∈ Submission.CutTime.minimisingSet (I := I) hmet x ξ :=
            ⟨le_of_lt (by linarith), hed⟩
          have hmem' := Submission.CutTime.minimisingSet_of_le (I := I) (cov := cov) hmet htor
            hξn hmem (le_of_lt (lt_of_lt_of_le hTpos (le_of_lt hgt))) ht.2
          show rdist (I := I) (M := M) x
            (Submission.GlobalExp.GExp (cov := cov) hmet x (t • ξ)) = t
          rw [rdist, hmem'.2, ENNReal.toReal_ofReal (le_of_lt (lt_of_lt_of_le hTpos (le_of_lt hgt)))]
      have hle : T + δ ≤ T := le_csSup hbdd hTδS
      linarith
    · exact heq
  -- conclusion
  intro t ht
  rcases lt_or_eq_of_le ht.2 with h | h
  · exact (hltS t (by rw [hTeq]; exact h)).2 t ⟨ht.1, le_rfl⟩
  · subst h
    rw [← hTeq]
    exact hTS.2 T ⟨hTpos.le, le_rfl⟩


end InjCore

/-- **`Work.Diff.C.geoCrux.Port.InjRadiusCoreProp`**: under the C-area hypotheses the exponential map
at every point is injective on the ball of radius `π - arccos (1-c)` — with **no** global diameter
bound.

This is `Work.Diff.C.geoCrux.injectivity_radius` (`InjectivityProp`) with its `hdiam` hypothesis
removed: by `InjCore.ray_minimising_upto'` every ray of length `≤ ρ` is minimising (the
smoothness of `rdist x` along it being supplied inside the ball by
`Work.Diff.C.fbcap_rdist_smooth`, never by a global bound on `rdist`),
`Submission.CutTime.mem_minimisingSet_iff` converts this into `ρ ≤ cutTime x ξ`, and
`Submission.InjRadiusCut.injAtLeast_of_forall_cutTime_le` into the injectivity statement. -/
theorem inj_radius_core : Work.Diff.C.geoCrux.Port.InjRadiusCoreProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad x
  haveI : RegularSpace M := inferInstance
  refine Submission.InjRadiusCut.injAtLeast_of_forall_cutTime_le (I := I) (cov := cov) hmet htor ?_
  intro ξ hξn
  have hξi : Inner.inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξn, one_pow]
  have hρpos : 0 < Real.pi - Real.arccos (1 - c) := by
    have h : Real.arccos (1 - c) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
    linarith
  have hmin : rayD hmet x ξ (Real.pi - Real.arccos (1 - c)) = Real.pi - Real.arccos (1 - c) :=
    InjCore.ray_minimising_upto' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC
      hHess hcont hgrad hξi _ ⟨le_of_lt hρpos, le_rfl⟩
  have hed : Manifold.riemannianEDist I x
      (Submission.GlobalExp.GExp (cov := cov) hmet x ((Real.pi - Real.arccos (1 - c)) • ξ))
      = ENNReal.ofReal (Real.pi - Real.arccos (1 - c)) := by
    have hfin : Manifold.riemannianEDist I x
        (Submission.GlobalExp.GExp (cov := cov) hmet x ((Real.pi - Real.arccos (1 - c)) • ξ))
        ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top hmet htor x _).ne
    have htr : (Manifold.riemannianEDist I x
        (Submission.GlobalExp.GExp (cov := cov) hmet x
          ((Real.pi - Real.arccos (1 - c)) • ξ))).toReal
        = Real.pi - Real.arccos (1 - c) := hmin
    calc Manifold.riemannianEDist I x
          (Submission.GlobalExp.GExp (cov := cov) hmet x ((Real.pi - Real.arccos (1 - c)) • ξ))
        = ENNReal.ofReal ((Manifold.riemannianEDist I x
            (Submission.GlobalExp.GExp (cov := cov) hmet x
              ((Real.pi - Real.arccos (1 - c)) • ξ))).toReal) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ = ENNReal.ofReal (Real.pi - Real.arccos (1 - c)) := by rw [htr]
  have hmem : (Real.pi - Real.arccos (1 - c))
      ∈ Submission.CutTime.minimisingSet (I := I) hmet x ξ := ⟨le_of_lt hρpos, hed⟩
  exact ((Submission.CutTime.mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξn).mp hmem).2

end Work.Diff.C.geoCrux.Port
