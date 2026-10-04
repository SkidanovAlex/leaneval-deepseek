import Mathlib
import Submission.Work.Diff.C.geoCrux.Port.Families

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The operator side of the two-centre argument

This module contains the pieces of `Work.Diff.C.geoCrux.Port.TwoCentreCoreProp` that do **not** need
Jacobi uniqueness: the trigonometry (`twoK > 0`, `twoL > 0`, `twoK - twoD ≥ 0`), the shape operator
`𝔎(t)w = - Hess (rdist (γ t)) (q) w` of the geodesic sphere of radius `t` around `γ t` at the base
point `q`, and the associated quadratic-form bound for `ℭ := 𝔎(τ) - 𝔎(σ)`.

## The mathematics

The ray is `gam s = GExp q (s • v)`, `q = gam 0`, and `p := gam τ`.  For `w ⊥ v` (at `q`) put

* `shapeOp τ w := - Hess (rdist (gam τ)) (q) w` (a tangent vector at `q`),

so that `⟨𝔎(t) w, w'⟩ = - rhess (rdist (gam t)) q w w'`.  The shape-operator bound `hHess` (through
`Work.Diff.C.GeoCrux.shape_polarized`, applied to the centre `gam t` at the point `q`) says that
`Hess (rdist (gam t)) (q)` differs from `cot t • g` by at most `ε₁ / sin t` in operator norm, hence

`(twoL - twoE) ‖w‖² ≤ ⟨(𝔎 τ - 𝔎 σ) w, w⟩`

for `w ⊥ v`, where `twoL = cot σ - cot τ` and `twoE = ε₁(1/sin σ + 1/sin τ)`.

This is the `(κ-δ)`-free half of condition (c)/(d) of the target: it is the quadratic-form bound for
the *inverse* of `𝔄 := T^* 𝔅 T` (the two-centre identity identifies `𝔄` with `ℭ^{-1}`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux.Port

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## Elementary trigonometry -/

lemma sin_sub_eq (τ σ : ℝ) :
    Real.sin (τ - σ) = Real.sin τ * Real.cos σ - Real.cos τ * Real.sin σ :=
  Real.sin_sub τ σ

theorem twoK_pos {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) (hτπ : τ < Real.pi) :
    0 < twoK σ τ := by
  have h1 : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)
  have h2 : 0 < Real.sin (τ - σ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h3 : 0 < Real.sin τ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hτπ
  have key : twoK σ τ = Real.sin τ / (Real.sin σ * Real.sin (τ - σ)) := by
    rw [twoK, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
      div_add_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
    congr 1
    have hs : Real.sin ((τ - σ) + σ)
        = Real.sin (τ - σ) * Real.cos σ + Real.cos (τ - σ) * Real.sin σ :=
      Real.sin_add _ _
    rw [show (τ - σ) + σ = τ from by ring] at hs
    rw [hs]; ring
  rw [key]; positivity

theorem twoL_pos {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) (hτπ : τ < Real.pi) :
    0 < twoL σ τ := by
  have h1 : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)
  have h2 : 0 < Real.sin τ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hτπ
  have h3 : 0 < Real.sin (τ - σ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have key : twoL σ τ = Real.sin (τ - σ) / (Real.sin σ * Real.sin τ) := by
    rw [twoL, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
      div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
    congr 1
    rw [sin_sub_eq]; ring
  rw [key]; positivity

/-! ## The shape operator of the spheres around `gam t`, at the base point `q` -/

/-- `𝔎(t) w = - Hess (rdist (gam t)) (q) w`: the negative shape operator, at the base point `q`, of
the geodesic sphere of radius `t` around `gam t`. -/
noncomputable def tcShape (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q)
    (t : ℝ) (w : TangentSpace I q) : TangentSpace I q :=
  - (cov (fun y : M ↦ rgrad (I := I) (M := M)
      (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z) y) q w)

/-- The defining property: `⟨𝔎(t) w, w'⟩ = - rhess (rdist (gam t)) q w w'`. -/
lemma tcShape_spec (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t : ℝ)
    (w w' : TangentSpace I q) :
    tcIn (M := M) (I := I) q (tcShape (cov := cov) hmet q v t w) w'
      = - rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          q w w' := by
  rw [tcShape, tcIn_eq, rhess, inner_neg_left]

lemma tcShape_add (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t : ℝ)
    (w w' : TangentSpace I q) :
    tcShape (cov := cov) hmet q v t (w + w')
      = tcShape (cov := cov) hmet q v t w + tcShape (cov := cov) hmet q v t w' := by
  rw [tcShape, tcShape, tcShape, map_add, neg_add]

lemma tcShape_smul (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t a : ℝ)
    (w : TangentSpace I q) :
    tcShape (cov := cov) hmet q v t (a • w)
      = a • tcShape (cov := cov) hmet q v t w := by
  rw [tcShape, tcShape, map_smul, smul_neg]

@[simp] lemma tcShape_zero (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t : ℝ) :
    tcShape (cov := cov) hmet q v t (0 : TangentSpace I q) = 0 := by
  rw [tcShape, map_zero, neg_zero]

lemma tcIn_sub_left (X : M) (a a' b : TangentSpace I X) :
    tcIn (M := M) (I := I) X (a - a') b = tcIn (M := M) (I := I) X a b
      - tcIn (M := M) (I := I) X a' b := by
  rw [tcIn_eq, tcIn_eq, tcIn_eq, inner_sub_left]

lemma tcIn_sub_right (X : M) (a b b' : TangentSpace I X) :
    tcIn (M := M) (I := I) X a (b - b') = tcIn (M := M) (I := I) X a b
      - tcIn (M := M) (I := I) X a b' := by
  rw [tcIn_eq, tcIn_eq, tcIn_eq, inner_sub_right]

/-! ## The gradient of `rdist (gam t)` at `q`

The reversed ray out of `gam t` in the direction `-γ'(t)` retraces `gam` and arrives at `q` with
unit velocity `-v`, so the gradient of the distance to `gam t` at `q` is `-v`. -/

lemma rgrad_rdist_back (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c) :
    rgrad (I := I) (M := M)
        (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z) q
      = -v := by
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0 : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; norm_num at hwn
  have hgrad := tc_grad_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC
    (q := tcGam (cov := cov) hmet q v t) (v := -(tcVel (cov := cov) hmet q v t)) hwn hw0
    ht0 ht.le
  -- the point at parameter `t` of the reversed ray is `gam 0`
  have hpt : Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
      (t • (-(tcVel (cov := cov) hmet q v t))) = tcGam (cov := cov) hmet q v 0 := by
    have h := tc_rev_point (cov := cov) hmet hvn t 0
    rwa [show t - 0 = t from by ring] at h
  have hgam0 : tcGam (cov := cov) hmet q v 0 = q := by simp [tcGam, zero_smul]
  -- and the velocity there is `-v`
  have hvel : tcVel (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
      (-(tcVel (cov := cov) hmet q v t)) t = -v := by
    have h := tc_rev_vel (cov := cov) hmet hvn hv0 t 0
    rw [tcVel_zero (cov := cov) hmet hv0] at h
    rw [show t - 0 = t from by ring] at h
    exact h
  rw [tcGam_eq] at hgrad
  rw [hvel] at hgrad
  rw [hpt] at hgrad
  rwa [hgam0] at hgrad

/-! ## The quadratic form bound for `𝔎(τ) - 𝔎(σ)` -/

lemma cos_rho0 {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) : Real.cos (rho0 c) = -1 + c := by
  rw [rho0, Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
  ring

lemma rho0_le_pi (c : ℝ) : rho0 c ≤ Real.pi := by
  have h : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg (1 - c)
  rw [rho0]; linarith

lemma rho0_lt_pi {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) : rho0 c < Real.pi := by
  have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
  rw [rho0]; linarith

/-- The distance from `gam t` to `q`. -/
lemma rdist_gam_q (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ rho0 c) :
    rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = t := by
  have hgam0 : tcGam (cov := cov) hmet q v 0 = q := by simp [tcGam, zero_smul]
  have h := tc_rdist_bwd (cov := cov) hmet htor hcut hvn ht ht0 (le_refl (0 : ℝ)) ht0
  rw [sub_zero] at h
  rwa [hgam0] at h

/-- The gradient of `fcos (gam t)` at the base point `q` is `sin t • v`. -/
lemma rgrad_fcos_gam_at_q (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c) :
    rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q
      = Real.sin t • v := by
  have htle : t ≤ rho0 c := le_of_lt ht
  have hrd := rdist_gam_q (cov := cov) hmet htor hcut hvn ht0 htle
  have hcos : fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = Real.cos t := by
    show Real.cos (rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q) = Real.cos t
    rw [hrd]
  have hge : -1 + c ≤ fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q := by
    rw [hcos]
    have h5 : Real.cos (rho0 c) < Real.cos t :=
      Real.cos_lt_cos_of_nonneg_of_le_pi ht0.le (rho0_le_pi c) ht
    rw [cos_rho0 hc0 hc1] at h5
    linarith
  have hsm : CMDiffAt ∞ (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q :=
    hsmC _ _ hge
  have hsmr : CMDiffAt ∞
      (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z) q :=
    csm_rdist_of_le_rho hc0 hc1 hsmC (by rw [hrd]; exact ht0) (by rw [hrd]; exact htle)
  rw [rgrad_fcos (I := I) (M := M) (q := tcGam (cov := cov) hmet q v t) hsmr, hrd]
  rw [rgrad_rdist_back (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht]
  rw [smul_neg]
  simp

/-- **The quadratic-form bound for `ℭ = 𝔎(τ) - 𝔎(σ)`.** -/
theorem tcC_quadratic (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (w : TangentSpace I q) (hw : tcIn (M := M) (I := I) q v w = 0) :
    (twoL σ τ - twoE ε₁ σ τ) * tcIn (M := M) (I := I) q w w
      ≤ tcIn (M := M) (I := I) q
          (tcShape (cov := cov) hmet q v τ w - tcShape (cov := cov) hmet q v σ w) w := by
  have hτυ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hσπ : σ < Real.pi := lt_trans hστ hτυ
  have ht0 : 0 < τ := lt_trans hσ hστ
  have hτle : τ ≤ rho0 c := le_of_lt hτ
  have hσle : σ ≤ rho0 c := le_of_lt (lt_trans hστ hτ)
  have hshape : ∀ t : ℝ, 0 < t → t < rho0 c → t < Real.pi →
      |rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z) q w w
          - Real.cot t * tcIn (M := M) (I := I) q w w|
        ≤ (ε₁ / Real.sin t) * ‖w‖ * ‖w‖ := by
    intro t ht0' htl' htpi'
    have hrd := rdist_gam_q (cov := cov) hmet htor hcut hvn ht0' (le_of_lt htl')
    have hcos : fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = Real.cos t := by
      show Real.cos (rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q) = Real.cos t
      rw [hrd]
    have hx : -1 + c < fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q := by
      rw [hcos]
      have h5 : Real.cos (rho0 c) < Real.cos t :=
        Real.cos_lt_cos_of_nonneg_of_le_pi ht0'.le (rho0_le_pi c) htl'
      rw [cos_rho0 hc hc1] at h5
      linarith
    have hsm : CMDiffAt ∞
        (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z) q :=
      csm_rdist_of_le_rho hc hc1 hsmC (by rw [hrd]; exact ht0') (by rw [hrd]; exact le_of_lt htl')
    have hgf : rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q = Real.sin t • v :=
      rgrad_fcos_gam_at_q (cov := cov) hmet htor hc hc1 hcut hsmC hvn hv0 ht0' htl'
    have hV : Inner.inner ℝ
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q) w
        = 0 := by
      rw [hgf, real_inner_smul_left, ← tcIn_eq (M := M) (I := I) q v w, hw, mul_zero]
    have h := Work.Diff.C.geoCrux.shape_polarized (cov := cov) hmet htor
      (hHess (tcGam (cov := cov) hmet q v t)) hx hsm (by rw [hrd]; exact ht0')
      (by rw [hrd]; exact htpi') w w hV hV
    rwa [hrd, ← tcIn_eq (M := M) (I := I) q w w] at h
  have h1 := hshape τ ht0 hτ hτυ
  have h2 := hshape σ hσ (lt_trans hστ hτ) hσπ
  rw [abs_le] at h1 h2
  have hpair : tcIn (M := M) (I := I) q
      (tcShape (cov := cov) hmet q v τ w - tcShape (cov := cov) hmet q v σ w) w
      = - rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z) q w w
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) z) q w w := by
    rw [tcIn_sub_left, tcShape_spec, tcShape_spec]
    ring
  rw [hpair]
  have hsinτ : 0 < Real.sin τ := Real.sin_pos_of_pos_of_lt_pi ht0 hτυ
  have hsinσ : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ hσπ
  have hn : ‖w‖ ^ 2 = tcIn (M := M) (I := I) q w w := norm_sq_eq_tcIn (M := M) (I := I) q w
  have e1 : ε₁ / Real.sin τ * ‖w‖ * ‖w‖ = ε₁ * (1 / Real.sin τ) * ‖w‖ ^ 2 := by ring
  have e2 : ε₁ / Real.sin σ * ‖w‖ * ‖w‖ = ε₁ * (1 / Real.sin σ) * ‖w‖ ^ 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hnτ : ε₁ * (1 / Real.sin τ) * ‖w‖ ^ 2
      = ε₁ * (1 / Real.sin τ) * tcIn (M := M) (I := I) q w w := by rw [hn]
  have hnσ : ε₁ * (1 / Real.sin σ) * ‖w‖ ^ 2
      = ε₁ * (1 / Real.sin σ) * tcIn (M := M) (I := I) q w w := by rw [hn]
  have hA : Real.cot τ * tcIn (M := M) (I := I) q w w
      - ε₁ * (1 / Real.sin τ) * tcIn (M := M) (I := I) q w w
      ≤ rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z) q w w := by
    linarith [h1.1, hnτ]
  have hB : Real.cot σ * tcIn (M := M) (I := I) q w w
      - ε₁ * (1 / Real.sin σ) * tcIn (M := M) (I := I) q w w
      ≤ rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) z) q w w := by
    linarith [h2.1, hnσ]
  have hX0 : 0 ≤ tcIn (M := M) (I := I) q w w := tcIn_nonneg (M := M) (I := I) q w
  rw [twoL, twoE]
  nlinarith [hA, hB, hX0, hε₁, hsinσ, hsinτ,
    inv_nonneg.mpr hsinσ.le, inv_nonneg.mpr hsinτ.le]

end Work.Diff.C.geoCrux.Port
