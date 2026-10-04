import Mathlib
import Submission.Work.Diff.C.geoCrux.VariationBase
import Submission.Work.Diff.C.geoCrux.shape_polarized
import Submission.Work.Diff.C.geoCrux.radial_modulus
import Submission.Work.Diff.C.geoCrux.hmod.NBound

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-centre assembly: the sharp modulus of the radial variation field

`Submission/Work/Diff/C/geoCrux/VariationBase.lean` (a namespace-isolated copy of the proved
lemmas of `Submission.Work.Diff.C.geoCrux.twoCentreCore`) provides the Jacobi-field machinery of the
two-centre argument: the forward/backward variation families `tcFwd`/`tcPrayFld`, the shape
operators `tcShape`/`tcC`, the backward identification `tcBackwardID` and the Wronskian identity
`tcWronskian_twoCentre`.

Here we add

* `twoCentreB` — the shape-sum bound `𝔅 = twoK σ τ · g + O(twoD ε₁ σ τ)` on `γ'(σ)^⊥`;
* `twoCentreC` — the shape-difference bound `ℭ = twoL σ τ · g + O(twoE ε₁ σ τ)` on `v^⊥`;
* `twoCentre_N_pair` — the two-centre modulus inequality at the pair `(σ, 2σ)`: the existence of an
  operator-norm bound `N` for `ξ ↦ Z_ξ(σ)` with the Wronskian coefficient inequality
  `(κλ - κη - λδ - δη)·N² ≤ 1` (`κ = twoK σ (2σ)`, `λ = twoL σ (2σ)`, `δ = twoD ε₁ σ (2σ)`,
  `η = twoE ε₁ σ (2σ)`).

The last is the geometric core of `Work.Diff.C.geoCrux.VariationModulusProp`: it is consumed by
`Work.Diff.C.geoCrux.anchor_from_core` (in `variation_modulus.lean`) together with the pure
real-analysis extraction `Work.Diff.C.geoCrux.hmod.NBound`.

## The route of `twoCentre_N_pair`

Let `T ξ = tcFwd hmet q v ξ σ = Z_ξ(σ)`, a linear map.  From `tcPrayFld_surj_base` (every `W ⊥ v`
is the value at `q` of a backward field from `γ(2σ)`), `tcBackwardID` (`J(σ) = T(ℭ J(0))`) and
`tcWronskian_twoCentre` one gets the key identity

`𝔅(Tξ, T(ℭW)) = ⟪ξ, W⟫`  for all `ξ, W ⊥ v`.   (★)

Let now `ξ₀` maximise `‖T ·‖` on the unit sphere of `v^⊥` and `N := ‖Tξ₀‖` (the degenerate case
`v^⊥ = 0` is trivial).  From (★) with `ξ = W = ξ₀`, writing `ℭξ₀ = λξ₀ + e` with `‖e‖ ≤ η`
(immediate from `twoCentreC`), the linearity of `T` and `twoCentreB` give

`1 = 𝔅(Tξ₀, Tℭξ₀) ≥ κ·⟪Tξ₀, Tℭξ₀⟫ - δ‖Tξ₀‖‖Tℭξ₀‖ ≥ [κλ - κη - λδ - δη] N²`,

using `⟪Tξ₀,Tℭξ₀⟫ ≥ λN² - N‖Te‖`, `‖Te‖ ≤ ηN`, `‖Tℭξ₀‖ ≤ (λ+η)N` and `‖Te‖ ≤ N‖e‖ ≤ Nη` (the last
from the maximality of `ξ₀`).  This is exactly the hypothesis of `Work.Diff.C.geoCrux.hmod.NBound`
(and of `Work.Diff.C.geoCrux.twoCentre_N_bound`); the maximality of `ξ₀` converts `‖Tξ₀‖ = N` into
the bound `‖Tξ‖ ≤ N‖ξ‖` for all `ξ ⊥ v` by homogeneity (`tcFwd_smul`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C.geoCrux.variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## The shape-sum bound on `γ'(σ)^⊥` -/

/-- **The two-centre bound for the shape-sum bilinear form**

`𝔅(V,W) = Hess (rdist q)(γσ)(V,W) + Hess (rdist (γτ))(γσ)(V,W)`,

on `γ'(σ)^⊥`: `|𝔅(V,W) - κ⟪V,W⟫| ≤ δ‖V‖‖W‖` with `κ = twoK σ τ`, `δ = twoD ε₁ σ τ`. -/
lemma twoCentreB (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (V W : TangentSpace I (tcGam (cov := cov) hmet q v σ))
    (hV : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V
      (tcVel (cov := cov) hmet q v σ) = 0)
    (hW : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) W
      (tcVel (cov := cov) hmet q v σ) = 0) :
    |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) V W
      + Work.Diff.C.rhess cov
          (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
          (tcGam (cov := cov) hmet q v σ) V W
      - twoK σ τ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W|
      ≤ twoD ε₁ σ τ * ‖V‖ * ‖W‖ := by
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hvn; exact one_ne_zero hvn.symm
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hσπ : σ < Real.pi := lt_trans hστ hτπ
  have hτ0 : 0 < τ := lt_trans hσ0 hστ
  have hd0 : 0 < τ - σ := sub_pos.mpr hστ
  have hdπ : τ - σ < Real.pi := by linarith
  have hσle : σ ≤ rho0 c := le_of_lt (lt_trans hστ hτ)
  -- distances
  have hrdσ : rdist (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ) = σ :=
    tc_rdist_gam (cov := cov) hmet htor hcut hvn hσ0 hσle
  have hrdd : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
      (tcGam (cov := cov) hmet q v σ) = τ - σ :=
    tc_rdist_bwd (cov := cov) hmet htor hcut hvn hτ.le hτ0 hσ0.le hστ
  -- smoothness
  have hsmσ : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v σ) :=
    tc_sm_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hσle
  have hsmd : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v τ) z) (tcGam (cov := cov) hmet q v σ) :=
    tc_sm_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hτ.le hτ0 hσ0 hστ
  -- gradients
  have hgσ : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v σ) = tcVel (cov := cov) hmet q v σ :=
    tc_grad_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hσle
  have hgd : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v τ) z) (tcGam (cov := cov) hmet q v σ)
      = -(tcVel (cov := cov) hmet q v σ) :=
    tc_grad_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ.le
  -- the strict region conditions
  have hxσ : -1 + c < fcos (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ) := by
    have h1 : fcos (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ) = Real.cos σ := by
      show Real.cos (rdist (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ)) = Real.cos σ
      rw [hrdσ]
    rw [h1, ← cos_rho0 hc0 hc1]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hσ0.le (rho0_le_pi c) (lt_trans hστ hτ)
  have hxd : -1 + c < fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
      (tcGam (cov := cov) hmet q v σ) := by
    have h1 : fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
        (tcGam (cov := cov) hmet q v σ) = Real.cos (τ - σ) := by
      show Real.cos (rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
        (tcGam (cov := cov) hmet q v σ)) = Real.cos (τ - σ)
      rw [hrdd]
    rw [h1, ← cos_rho0 hc0 hc1]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hd0.le (rho0_le_pi c) (by linarith [hτ])
  -- the orthogonality hypotheses of `shape_polarized`
  have hVel : Inner.inner ℝ (tcVel (cov := cov) hmet q v σ) V = 0 := by
    rw [← tcIn_eq (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
      (tcVel (cov := cov) hmet q v σ) V, tcIn_symm]
    exact hV
  have hWel : Inner.inner ℝ (tcVel (cov := cov) hmet q v σ) W = 0 := by
    rw [← tcIn_eq (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
      (tcVel (cov := cov) hmet q v σ) W, tcIn_symm]
    exact hW
  have hVσ : Inner.inner ℝ (rgrad (I := I) (M := M)
      (fcos (I := I) (M := M) q) (tcGam (cov := cov) hmet q v σ)) V = 0 := by
    have hg : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
        (tcGam (cov := cov) hmet q v σ) = (-Real.sin σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := q) hsmσ, hrdσ, hgσ]
    rw [hg, real_inner_smul_left, hVel, mul_zero]
  have hWσ : Inner.inner ℝ (rgrad (I := I) (M := M)
      (fcos (I := I) (M := M) q) (tcGam (cov := cov) hmet q v σ)) W = 0 := by
    have hg : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
        (tcGam (cov := cov) hmet q v σ) = (-Real.sin σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := q) hsmσ, hrdσ, hgσ]
    rw [hg, real_inner_smul_left, hWel, mul_zero]
  have hVd : Inner.inner ℝ (rgrad (I := I) (M := M)
      (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
      (tcGam (cov := cov) hmet q v σ)) V = 0 := by
    have hg : rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
        (tcGam (cov := cov) hmet q v σ) = Real.sin (τ - σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := tcGam (cov := cov) hmet q v τ) hsmd, hrdd, hgd,
        neg_smul_neg]
    rw [hg, real_inner_smul_left, hVel, mul_zero]
  have hWd : Inner.inner ℝ (rgrad (I := I) (M := M)
      (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
      (tcGam (cov := cov) hmet q v σ)) W = 0 := by
    have hg : rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
        (tcGam (cov := cov) hmet q v σ) = Real.sin (τ - σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := tcGam (cov := cov) hmet q v τ) hsmd, hrdd, hgd,
        neg_smul_neg]
    rw [hg, real_inner_smul_left, hWel, mul_zero]
  -- the two applications of `shape_polarized`
  have hb1 := shape_polarized (I := I) (M := M) (cov := cov) hmet htor (hHess q) hxσ hsmσ
    (by rw [hrdσ]; exact hσ0) (by rw [hrdσ]; exact hσπ) V W hVσ hWσ
  rw [hrdσ] at hb1
  have hb1' : |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) V W
      - Real.cot σ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W|
      ≤ (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ := by
    rw [tcIn_eq (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W]
    exact hb1
  have hb2 := shape_polarized (I := I) (M := M) (cov := cov) hmet htor
    (hHess (tcGam (cov := cov) hmet q v τ)) hxd hsmd
    (by rw [hrdd]; exact hd0) (by rw [hrdd]; exact hdπ) V W hVd hWd
  rw [hrdd] at hb2
  have hb2' : |Work.Diff.C.rhess cov
        (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
        (tcGam (cov := cov) hmet q v σ) V W
      - Real.cot (τ - σ) * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W|
      ≤ (ε₁ / Real.sin (τ - σ)) * ‖V‖ * ‖W‖ := by
    rw [tcIn_eq (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W]
    exact hb2
  -- arithmetic
  rw [twoK, twoD]
  have harg : (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v σ) V W
        + Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
            (tcGam (cov := cov) hmet q v σ) V W)
        - (Real.cot σ + Real.cot (τ - σ))
            * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W
      = (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
            (tcGam (cov := cov) hmet q v σ) V W
          - Real.cot σ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W)
        + (Work.Diff.C.rhess cov
              (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
              (tcGam (cov := cov) hmet q v σ) V W
          - Real.cot (τ - σ) * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W) := by
    ring
  rw [harg]
  refine le_trans (le_trans (abs_add_le _ _) (add_le_add hb1' hb2')) ?_
  have harith : (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ + (ε₁ / Real.sin (τ - σ)) * ‖V‖ * ‖W‖
      = ε₁ * (1 / Real.sin σ + 1 / Real.sin (τ - σ)) * ‖V‖ * ‖W‖ := by
    ring
  rw [harith]

/-! ## The shape-difference bound on `v^⊥` -/

/-- **The two-centre bound for `ℭ = 𝔎(τ) - 𝔎(σ)`**, on `v^⊥`:
`|⟪ℭV,W⟫ - λ⟪V,W⟫| ≤ η‖V‖‖W‖` with `λ = twoL σ τ`, `η = twoE ε₁ σ τ`. -/
lemma twoCentreC (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (V W : TangentSpace I q)
    (hV : tcIn (M := M) (I := I) q v V = 0) (hW : tcIn (M := M) (I := I) q v W = 0) :
    |tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ τ V) W
        - twoL σ τ * tcIn (M := M) (I := I) q V W|
      ≤ twoE ε₁ σ τ * ‖V‖ * ‖W‖ := by
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hvn; exact one_ne_zero hvn.symm
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hτ0 : 0 < τ := lt_trans hσ0 hστ
  -- the shape bound at an arbitrary radius `t ∈ (0, rho0 c)`
  have hshape : ∀ t : ℝ, 0 < t → t < rho0 c →
      |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
          (tcGam (cov := cov) hmet q v t) z) q V W
        - Real.cot t * Inner.inner ℝ V W| ≤ (ε₁ / Real.sin t) * ‖V‖ * ‖W‖ := by
    intro t ht0 htl
    have htπ : t < Real.pi := lt_of_lt_of_le htl (rho0_le_pi c)
    have hrd : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = t :=
      rdist_gam_q (cov := cov) hmet htor hcut hvn ht0 htl.le
    have hcos : fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = Real.cos t := by
      show Real.cos (rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q) = Real.cos t
      rw [hrd]
    have hx : -1 + c < fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q := by
      rw [hcos, ← cos_rho0 hc0 hc1]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi ht0.le (rho0_le_pi c) htl
    have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v t) z) q :=
      csm_rdist_of_le_rho hc0 hc1 hsmC (by rw [hrd]; exact ht0) (by rw [hrd]; exact htl.le)
    have hgf : rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q = Real.sin t • v :=
      rgrad_fcos_gam_at_q (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 htl
    have hV' : Inner.inner ℝ (rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q) V = 0 := by
      rw [hgf, real_inner_smul_left]
      have h := hV
      rw [tcIn_eq (M := M) (I := I) q v V] at h
      rw [h, mul_zero]
    have hW' : Inner.inner ℝ (rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q) W = 0 := by
      rw [hgf, real_inner_smul_left]
      have h := hW
      rw [tcIn_eq (M := M) (I := I) q v W] at h
      rw [h, mul_zero]
    have h := shape_polarized (I := I) (M := M) (cov := cov) hmet htor
      (hHess (tcGam (cov := cov) hmet q v t)) hx hsm
      (by rw [hrd]; exact ht0) (by rw [hrd]; exact htπ) V W hV' hW'
    rwa [hrd] at h
  have h1 := hshape τ hτ0 hτ
  have h2 := hshape σ hσ0 (lt_trans hστ hτ)
  have h1' : |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v τ) z) q V W - Real.cot τ * tcIn (M := M) (I := I) q V W|
      ≤ (ε₁ / Real.sin τ) * ‖V‖ * ‖W‖ := by
    rw [tcIn_eq (M := M) (I := I) q V W]
    exact h1
  have h2' : |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v σ) z) q V W - Real.cot σ * tcIn (M := M) (I := I) q V W|
      ≤ (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ := by
    rw [tcIn_eq (M := M) (I := I) q V W]
    exact h2
  rw [tcC_spec, twoL, twoE]
  have harg : (-Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
          (tcGam (cov := cov) hmet q v τ) z) q V W
        + Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
          (tcGam (cov := cov) hmet q v σ) z) q V W)
        - (Real.cot σ - Real.cot τ) * tcIn (M := M) (I := I) q V W
      = (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
            (tcGam (cov := cov) hmet q v σ) z) q V W - Real.cot σ * tcIn (M := M) (I := I) q V W)
        - (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
            (tcGam (cov := cov) hmet q v τ) z) q V W - Real.cot τ * tcIn (M := M) (I := I) q V W) := by
    ring
  rw [harg]
  refine le_trans (le_trans (abs_sub _ _) (add_le_add h2' h1')) ?_
  have harith : (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ + (ε₁ / Real.sin τ) * ‖V‖ * ‖W‖
      = ε₁ * (1 / Real.sin σ + 1 / Real.sin τ) * ‖V‖ * ‖W‖ := by
    ring
  rw [harith]

/-! ## The two-centre modulus inequality at the pair `(σ, 2σ)` -/

/-- `twoE ε₁ σ τ ≥ 0`. -/
lemma twoE_nonneg {ε₁ σ τ : ℝ} (hε₁ : 0 ≤ ε₁) (hσ0 : 0 < σ) (hστ : σ < τ)
    (hτπ : τ < Real.pi) : 0 ≤ twoE ε₁ σ τ := by
  rw [twoE]
  refine mul_nonneg hε₁ (add_nonneg (one_div_nonneg.mpr ?_) (one_div_nonneg.mpr ?_))
  · exact (Real.sin_pos_of_pos_of_lt_pi hσ0 (by linarith)).le
  · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) hτπ).le

/-- `twoD ε₁ σ τ ≥ 0`. -/
lemma twoD_nonneg {ε₁ σ τ : ℝ} (hε₁ : 0 ≤ ε₁) (hσ0 : 0 < σ) (hστ : σ < τ)
    (hτπ : τ < Real.pi) : 0 ≤ twoD ε₁ σ τ := by
  rw [twoD]
  refine mul_nonneg hε₁ (add_nonneg (one_div_nonneg.mpr ?_) (one_div_nonneg.mpr ?_))
  · exact (Real.sin_pos_of_pos_of_lt_pi hσ0 (by linarith)).le
  · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le

/-- **The two-centre modulus inequality.**  For a unit `v ∈ T_qM` and `0 < σ` with
`2σ < rho0 c = π - arccos (1-c)` there is `N ≥ 0` with

* `‖Z_η(σ)‖ ≤ N‖η‖` for every `η ⊥ v`, where `Z_η(s) = ∂_r GExp q (s(v + rη))|_0 = tcFwd q v η s`;
* `(κ-δ)(λ-η)N² ≤ 1` with `κ = twoK σ (2σ)`, `λ = twoL σ (2σ)`,
  `δ = twoD ε₁ σ (2σ)`, `η = twoE ε₁ σ (2σ)`.

Degenerate case `v^⊥ = 0`: `N := 0` works.  Otherwise `N := ‖Tξ₀‖` for `ξ₀` a maximiser of
`‖T·‖` on the unit sphere of `v^⊥`. -/
theorem twoCentre_N_pair (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁) (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (σ : ℝ) (hσ0 : 0 < σ) (h2σ : 2 * σ < Real.pi - Real.arccos (1 - c)) :
    ∃ N : ℝ, 0 ≤ N ∧
      (∀ η : TangentSpace I q, Inner.inner ℝ v η = 0 →
        ‖tcFwd (cov := cov) hmet q v η σ‖ ≤ N * ‖η‖) ∧
      0 < twoK σ (2 * σ) ∧ 0 < twoL σ (2 * σ) ∧
      (twoK σ (2 * σ) * twoL σ (2 * σ) - twoK σ (2 * σ) * twoE ε₁ σ (2 * σ)
        - twoL σ (2 * σ) * twoD ε₁ σ (2 * σ) - twoD ε₁ σ (2 * σ) * twoE ε₁ σ (2 * σ)) * N ^ 2
        ≤ 1 := by
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  have hvn : ‖v‖ = 1 := by
    have h2 : ‖v‖ ^ 2 = 1 := by
      rw [norm_sq_eq_tcIn (M := M) (I := I) q v, tcIn_eq (M := M) (I := I) q v v]
      exact hv
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact h
    · nlinarith [norm_nonneg v, h]
  have h2σ0 : 0 < 2 * σ := by linarith
  have hσ2σ : σ < 2 * σ := by linarith
  have h2σρ : 2 * σ < rho0 c := h2σ
  have h2σπ : 2 * σ < Real.pi := lt_of_lt_of_le h2σρ (rho0_le_pi c)
  have hKpos : 0 < twoK σ (2 * σ) := twoK_pos hσ0 hσ2σ h2σπ
  have hLpos : 0 < twoL σ (2 * σ) := twoL_pos hσ0 hσ2σ h2σπ
  have hκδ : 0 < twoK σ (2 * σ) - twoD ε₁ σ (2 * σ) :=
    twoK_sub_twoD_pos hc0 hc1 hε₁ hnum2 hσ0 hσ2σ h2σρ
  have hη0 : 0 ≤ twoE ε₁ σ (2 * σ) := twoE_nonneg hε₁ hσ0 hσ2σ h2σπ
  have hδ0 : 0 ≤ twoD ε₁ σ (2 * σ) :=
    twoD_nonneg hε₁ hσ0 hσ2σ (by linarith [h2σπ])
  -- the key identity `𝔅(Tξ, T(ℭW)) = ⟪ξ,W⟫`
  have hstar : ∀ ξ W : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 →
      tcIn (M := M) (I := I) q v W = 0 →
      (Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
          (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) W) σ)
        + Work.Diff.C.rhess cov
            (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v (2 * σ)) z)
            (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
            (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) W) σ))
      = tcIn (M := M) (I := I) q ξ W := by
    intro ξ W hξ hW
    obtain ⟨η, hηorth, hηval⟩ :=
      tcPrayFld_surj_base (cov := cov) hmet htor hcut hvn hv0 h2σ0 h2σρ hW
    have hback := tcBackwardID (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hσ2σ
      h2σρ η hηorth
    rw [hηval] at hback
    have hwr := tcWronskian_twoCentre (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0
      hσ2σ h2σρ ξ hξ η hηorth
    rw [hηval, hback] at hwr
    exact hwr
  -- the degenerate case
  let S : Set (TangentSpace I q) :=
    {x | tcIn (M := M) (I := I) q v x = 0} ∩ Metric.sphere (0 : TangentSpace I q) 1
  have hSclosed : IsClosed {x : TangentSpace I q | tcIn (M := M) (I := I) q v x = 0} := by
    refine isClosed_eq ?_ continuous_const
    show Continuous fun x : TangentSpace I q => tcIn (M := M) (I := I) q v x
    simp only [tcIn_eq]
    exact continuous_const.inner continuous_id
  have hScomp : IsCompact S := (isCompact_sphere (0 : TangentSpace I q) 1).inter_left hSclosed
  by_cases hne : S.Nonempty
  · -- the generic case: maximise `‖T ·‖` on the unit sphere of `v^⊥`
    have hcont : Continuous fun x : TangentSpace I q => ‖tcFwd (cov := cov) hmet q v x σ‖ := by
      simp only [tcFwd_eq_mfderiv]
      exact continuous_norm.comp
        (((mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q w)
          (σ • v)).continuous).comp (continuous_const_smul σ))
    obtain ⟨ξ₀, hξ₀S, hmax⟩ := hScomp.exists_isMaxOn hne hcont.continuousOn
    have hξ₀v : tcIn (M := M) (I := I) q v ξ₀ = 0 := hξ₀S.1
    have hξ₀n : ‖ξ₀‖ = 1 := by
      have h := hξ₀S.2
      rwa [Metric.mem_sphere, dist_zero_right] at h
    have hξ₀sq : tcIn (M := M) (I := I) q ξ₀ ξ₀ = 1 := by
      rw [← norm_sq_eq_tcIn (M := M) (I := I) q ξ₀, hξ₀n]
      norm_num
    have hmax' : ∀ y ∈ S, ‖tcFwd (cov := cov) hmet q v y σ‖
        ≤ ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ := fun y hy => hmax hy
    -- the operator-norm bound
    have hbound : ∀ ξ : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 →
        ‖tcFwd (cov := cov) hmet q v ξ σ‖ ≤ ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ * ‖ξ‖ := by
      intro ξ hξ
      rcases eq_or_ne ξ 0 with h0 | h0
      · rw [h0]
        simp [tcFwd_zero']
      · have hnpos : 0 < ‖ξ‖ := norm_pos_iff.mpr h0
        have hmem : (‖ξ‖)⁻¹ • ξ ∈ S := by
          refine ⟨?_, ?_⟩
          · show tcIn (M := M) (I := I) q v ((‖ξ‖)⁻¹ • ξ) = 0
            rw [tcIn_smul_right, hξ, mul_zero]
          · rw [Metric.mem_sphere, dist_zero_right, norm_smul,
              Real.norm_of_nonneg (inv_nonneg.mpr hnpos.le), inv_mul_cancel₀ (ne_of_gt hnpos)]
        have h1 := hmax' _ hmem
        rw [tcFwd_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnpos.le)] at h1
        have h2 : ‖tcFwd (cov := cov) hmet q v ξ σ‖
            ≤ ‖ξ‖ * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ := by
          have h3 := mul_le_mul_of_nonneg_left h1 hnpos.le
          rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at h3
        rw [mul_comm]
        exact h2
    -- the two-centre inequality
    set e : TangentSpace I q := tcC (cov := cov) hmet q v σ (2 * σ) ξ₀ - twoL σ (2 * σ) • ξ₀
      with hedef
    have hev : tcIn (M := M) (I := I) q v e = 0 := by
      rw [hedef, tcIn_sub_right, tcIn_smul_right, hξ₀v, mul_zero, sub_zero]
      rw [tcIn_symm]
      exact tcC_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hσ2σ h2σρ ξ₀
    have hCe : tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) e
        - twoL σ (2 * σ) * tcIn (M := M) (I := I) q ξ₀ e = tcIn (M := M) (I := I) q e e := by
      rw [hedef, tcIn_sub_left, tcIn_smul_left]
    have hebound : ‖e‖ ≤ twoE ε₁ σ (2 * σ) := by
      have hCw := twoCentreC (cov := cov) hmet htor hc0 hc1 hε₁ hcut hsmC hHess hvn hσ0
        hσ2σ h2σρ ξ₀ e hξ₀v hev
      have h1 : tcIn (M := M) (I := I) q e e ≤ twoE ε₁ σ (2 * σ) * ‖e‖ := by
        have h := hCw
        rw [hCe, hξ₀n, mul_one] at h
        exact le_trans (le_abs_self _) h
      have h2 : ‖e‖ ^ 2 ≤ twoE ε₁ σ (2 * σ) * ‖e‖ := by
        rw [norm_sq_eq_tcIn (M := M) (I := I) q e]
        exact h1
      rcases eq_or_lt_of_le (norm_nonneg e) with h | h
      · rw [← h]
        exact hη0
      · have h3 : ‖e‖ * (‖e‖ - twoE ε₁ σ (2 * σ)) ≤ ‖e‖ * 0 := by nlinarith [h2]
        have h4 := le_of_mul_le_mul_left h3 h
        linarith
    have hTlin : tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ
        = twoL σ (2 * σ) • tcFwd (cov := cov) hmet q v ξ₀ σ
          + tcFwd (cov := cov) hmet q v e σ := by
      have hCe' : tcC (cov := cov) hmet q v σ (2 * σ) ξ₀ = twoL σ (2 * σ) • ξ₀ + e := by
        rw [hedef]; abel
      rw [hCe', tcFwd_add, tcFwd_smul]
    -- orthogonality of the arguments of `𝔅`
    have hTorth : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v ξ₀ σ) (tcVel (cov := cov) hmet q v σ) = 0 := by
      rw [tcFwd_gauss (cov := cov) hmet htor (q := q) (v := v) ξ₀ σ, tcIn_symm, hξ₀v, mul_zero]
    have horthC : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ)
        (tcVel (cov := cov) hmet q v σ) = 0 := by
      rw [tcFwd_gauss (cov := cov) hmet htor (q := q) (v := v)
          (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ,
        show tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) v = 0 from
          tcC_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hσ2σ h2σρ ξ₀,
        mul_zero]
    have hB := twoCentreB (cov := cov) hmet htor hc0 hc1 hε₁ hcut hsmC hHess hvn hσ0 hσ2σ
      h2σρ (tcFwd (cov := cov) hmet q v ξ₀ σ)
      (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ) hTorth horthC
    have hone := hstar ξ₀ ξ₀ hξ₀v hξ₀v
    rw [hξ₀sq] at hone
    have hinnerTe : -(‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ * ‖tcFwd (cov := cov) hmet q v e σ‖)
        ≤ tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
            (tcFwd (cov := cov) hmet q v ξ₀ σ) (tcFwd (cov := cov) hmet q v e σ) := by
      have h3 := abs_real_inner_le_norm (tcFwd (cov := cov) hmet q v ξ₀ σ)
        (tcFwd (cov := cov) hmet q v e σ)
      rw [show Inner.inner ℝ (tcFwd (cov := cov) hmet q v ξ₀ σ)
            (tcFwd (cov := cov) hmet q v e σ)
          = tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
              (tcFwd (cov := cov) hmet q v ξ₀ σ) (tcFwd (cov := cov) hmet q v e σ)
          from (tcIn_eq (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
              (tcFwd (cov := cov) hmet q v ξ₀ σ) (tcFwd (cov := cov) hmet q v e σ)).symm] at h3
      linarith [(abs_le.mp h3).1]
    have hinner_pa : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v ξ₀ σ)
        (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ)
        = twoL σ (2 * σ) * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ ^ 2
          + tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
              (tcFwd (cov := cov) hmet q v ξ₀ σ) (tcFwd (cov := cov) hmet q v e σ) := by
      rw [hTlin, tcIn_add_right, tcIn_smul_right]
      rw [← norm_sq_eq_tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v ξ₀ σ)]
    -- the bound `‖Te‖ ≤ ηN` from the maximality of `ξ₀`
    have hTe : ‖tcFwd (cov := cov) hmet q v e σ‖ ≤ twoE ε₁ σ (2 * σ)
        * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ := by
      have h := hbound e hev
      rw [mul_comm] at h
      have h2 : ‖e‖ * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖
          ≤ twoE ε₁ σ (2 * σ) * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ :=
        mul_le_mul_of_nonneg_right hebound (norm_nonneg _)
      linarith [h, h2]
    have hN0 : 0 ≤ ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ := norm_nonneg _
    -- the final assembly: `1 = 𝔅(Tξ₀, T(ℭξ₀)) ≥ [κλ - κη - λδ - δη]·N²`
    have hXlow : twoL σ (2 * σ) * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ ^ 2
        - ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ * ‖tcFwd (cov := cov) hmet q v e σ‖
        ≤ tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
            (tcFwd (cov := cov) hmet q v ξ₀ σ)
            (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ) := by
      rw [hinner_pa]
      linarith [hinnerTe]
    have hTCL : ‖tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ‖
        ≤ (twoL σ (2 * σ) + twoE ε₁ σ (2 * σ)) * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ := by
      rw [hTlin]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hLpos.le]
      linarith [hTe]
    have hmain : (twoK σ (2 * σ) * twoL σ (2 * σ) - twoK σ (2 * σ) * twoE ε₁ σ (2 * σ)
          - twoL σ (2 * σ) * twoD ε₁ σ (2 * σ) - twoD ε₁ σ (2 * σ) * twoE ε₁ σ (2 * σ))
        * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ ^ 2 ≤ 1 := by
      have h2 := (abs_le.mp hB).1
      have h3 : twoD ε₁ σ (2 * σ) * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖
            * ‖tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ‖
          ≤ twoD ε₁ σ (2 * σ)
            * ((twoL σ (2 * σ) + twoE ε₁ σ (2 * σ))
              * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖)
            * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ := by
        have h5 := mul_le_mul_of_nonneg_left hTCL (mul_nonneg hδ0 hN0)
        nlinarith [h5]
      have h6 : twoK σ (2 * σ) * (twoL σ (2 * σ) * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ ^ 2
            - ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ * ‖tcFwd (cov := cov) hmet q v e σ‖)
          ≤ twoK σ (2 * σ)
            * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
                (tcFwd (cov := cov) hmet q v ξ₀ σ)
                (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ (2 * σ) ξ₀) σ) :=
        mul_le_mul_of_nonneg_left hXlow hKpos.le
      have h4 : ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ * ‖tcFwd (cov := cov) hmet q v e σ‖
          ≤ twoE ε₁ σ (2 * σ) * ‖tcFwd (cov := cov) hmet q v ξ₀ σ‖ ^ 2 := by
        have h5 := mul_le_mul_of_nonneg_left hTe hN0
        nlinarith [h5]
      nlinarith [h2, h3, h6, h4, hone]
    refine ⟨‖tcFwd (cov := cov) hmet q v ξ₀ σ‖, norm_nonneg _, ?_, hKpos, hLpos, hmain⟩
    intro η hη
    have hη' : tcIn (M := M) (I := I) q v η = 0 := by
      rwa [tcIn_eq (M := M) (I := I) q v η]
    exact hbound η hη'
  · -- the degenerate case `v^⊥ = {0}`
    have hzero : ∀ ξ : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 → ξ = 0 := by
      intro ξ hξ
      by_contra hξ0
      have hnpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
      have hmem : (‖ξ‖)⁻¹ • ξ ∈ S := by
        refine ⟨?_, ?_⟩
        · show tcIn (M := M) (I := I) q v ((‖ξ‖)⁻¹ • ξ) = 0
          rw [tcIn_smul_right, hξ, mul_zero]
        · rw [Metric.mem_sphere, dist_zero_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.mpr hnpos.le), inv_mul_cancel₀ (ne_of_gt hnpos)]
      exact hne ⟨_, hmem⟩
    refine ⟨0, le_refl 0, ?_, hKpos, hLpos, ?_⟩
    · intro η hη
      have hη' : tcIn (M := M) (I := I) q v η = 0 := by
        rwa [tcIn_eq (M := M) (I := I) q v η]
      rw [hzero η hη', tcFwd_zero', norm_zero, zero_mul]
    · rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      norm_num

end Work.Diff.C.geoCrux.variation
