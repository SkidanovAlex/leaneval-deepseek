import Mathlib
import Submission.Work.Diff.C.geoCrux.Port.CoreStmts
import Submission.Work.Diff.C.geoCrux.Port.AuxProps
import Submission.Work.Diff.C.geoCrux.Port.JacobiUniq
import Submission.Work.Diff.C.hess_lower_v2
import Submission.Work.Diff.C.rgrad_fcos_eikonal

set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-centre core: `Work.Diff.C.geoCrux.Port.TwoCentreCoreProp`

This file proves the two-centre inequality `Work.Diff.C.geoCrux.Port.TwoCentreCoreProp`
(`Submission/Work/Diff/C/geoCrux/CoreStmts.lean`), the geometric core of the sharp radial modulus
bound.

## The mathematics

Let `γ(t) = GExp q (t v)` be a unit-speed ray, `0 < σ < τ < ρ₀ = π - arccos (1-c)`, and
`Z_ξ(s) = ∂_r GExp q (s (v + r ξ))|_0` the forward variation field (a Jacobi field along `γ` with
`Z_ξ(0) = 0`, `∇Z_ξ(0) = ξ`, `ξ ⊥ v`).  Write `T ξ := Z_ξ(σ)` for the differential of `GExp q` at
`σ v`, restricted to `v^⊥`.

The two-centre argument produces the sharp bound `‖T‖² ≤ 1/((κ-δ)(λ-η))` with

`κ = cot σ + cot(τ-σ)`, `λ = cot σ - cot τ`, `δ = ε₁(1/sin σ + 1/sin(τ-σ))`,
`η = ε₁(1/sin σ + 1/sin τ)`.

Its ingredients are

* the two shape identities at the intermediate point `γ(σ)` (`tcFwd_shape_all` here and the
  workspace's `tcBwd_shape_gam`), together with the workspace bound `shape_polarized`: these give
  `|𝔅(V,W) - κ⟪V,W⟫| ≤ δ‖V‖‖W‖` for `𝔅 := Hess (rdist q)(γσ) + Hess (rdist (γτ))(γσ)` on `γ'(σ)^⊥`,
  and the analogous two-sided bound for `ℭ = 𝔎(τ) - 𝔎(σ)` with `𝔎(t) = - Hess (rdist (γ t))(q)`;
* the Wronskian identity `tcWronskian_twoCentre`: `𝔅(T ξ, J_η(σ)) = ⟪ξ, J_η(0)⟫`;
* the identification `tcBackwardID`: `J_η(σ) = T(ℭ (J_η(0)))`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

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

/-! ## 1. Elementary trigonometry of `κ = twoK`, `λ = twoL`, `δ = twoD`, `η = twoE` -/

/-- `twoK σ τ = sin τ/(sin σ · sin (τ-σ))`. -/
lemma twoK_eq {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ < Real.pi) :
    twoK σ τ = Real.sin τ / (Real.sin σ * Real.sin (τ - σ)) := by
  have h1 : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)
  have h2 : 0 < Real.sin (τ - σ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [twoK, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    div_add_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
  congr 1
  have hs : Real.sin ((τ - σ) + σ)
      = Real.sin (τ - σ) * Real.cos σ + Real.cos (τ - σ) * Real.sin σ :=
    Real.sin_add _ _
  rw [show (τ - σ) + σ = τ from by ring] at hs
  rw [hs]; ring

/-- `twoL σ τ = sin (τ-σ)/(sin σ · sin τ)`. -/
lemma twoL_eq {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ < Real.pi) :
    twoL σ τ = Real.sin (τ - σ) / (Real.sin σ * Real.sin τ) := by
  have h1 : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)
  have h2 : 0 < Real.sin τ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hτ
  rw [twoL, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
  congr 1
  have hs : Real.sin (τ - σ) = Real.sin τ * Real.cos σ - Real.cos τ * Real.sin σ :=
    Real.sin_sub τ σ
  rw [hs]; ring

/-- `twoD ε₁ σ τ · (sin σ sin (τ-σ)) = ε₁ (sin σ + sin (τ-σ))`. -/
lemma twoD_mul {ε₁ σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ < Real.pi) :
    twoD ε₁ σ τ * (Real.sin σ * Real.sin (τ - σ))
      = ε₁ * (Real.sin σ + Real.sin (τ - σ)) := by
  have h1 : Real.sin σ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hσ (by linarith))
  have h2 : Real.sin (τ - σ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  rw [twoD]
  field_simp
  ring

/-- `κ - δ` as a quotient. -/
lemma twoK_sub_twoD_eq {ε₁ σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ < Real.pi) :
    twoK σ τ - twoD ε₁ σ τ
      = (Real.sin τ - ε₁ * (Real.sin σ + Real.sin (τ - σ)))
          / (Real.sin σ * Real.sin (τ - σ)) := by
  have hp : Real.sin σ * Real.sin (τ - σ) ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)))
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)))
  have h1 : twoD ε₁ σ τ
      = ε₁ * (Real.sin σ + Real.sin (τ - σ)) / (Real.sin σ * Real.sin (τ - σ)) := by
    rw [eq_div_iff hp, twoD_mul (ε₁ := ε₁) hσ hστ hτ]
  rw [twoK_eq hσ hστ hτ, h1, sub_div]

/-- **`κ > δ`**: the shape-sum error is smaller than the shape sum. -/
lemma twoK_sub_twoD_pos {c ε₁ σ τ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (hσ : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c) :
    0 < twoK σ τ - twoD ε₁ σ τ := by
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)
  have hdpos : 0 < τ - σ := sub_pos.mpr hστ
  have hsdpos : 0 < Real.sin (τ - σ) := Real.sin_pos_of_pos_of_lt_pi hdpos (by linarith)
  have htp : 0 < τ / 2 := by linarith
  have htlt : τ / 2 < Real.pi := by linarith
  have hsinh : 0 < Real.sin (τ / 2) := Real.sin_pos_of_pos_of_lt_pi htp htlt
  have hcosτ : -1 + c < Real.cos τ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := τ) (y := rho0 c)
      (le_of_lt (lt_trans hσ hστ)) (rho0_le_pi c) hτ
    rw [cos_rho0 hc hc1] at h
    exact h
  have hhalf : Real.cos (τ / 2) ^ 2 = (1 + Real.cos τ) / 2 := by
    have h := Real.cos_two_mul (τ / 2)
    rw [show 2 * (τ / 2) = τ from by ring] at h
    linarith [h]
  have hεcos : ε₁ < Real.cos (τ / 2) := by
    have hcpos : 0 < Real.cos (τ / 2) := by
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith [Real.pi_pos]
    have hεle : ε₁ < c / (4 * Real.pi) := by
      have h : ε₁ * (4 * Real.pi) < c := by nlinarith [hnum2]
      exact (lt_div_iff₀ (by positivity)).mpr h
    have hcle : c / (4 * Real.pi) < Real.sqrt (c / 2) := by
      have hsq : (c / (4 * Real.pi)) ^ 2 = c ^ 2 / (16 * Real.pi ^ 2) := by ring
      have hkey : (c / (4 * Real.pi)) ^ 2 < c / 2 := by
        rw [hsq, div_lt_div_iff₀ (by positivity) (by norm_num)]
        have h2 : c ^ 2 ≤ c / 4 := by
          have := mul_le_mul_of_nonneg_left hc1 hc.le
          nlinarith [this]
        have h3 : c * 144 ≤ c * (16 * Real.pi ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hc.le
          nlinarith [Real.pi_gt_three]
        have h4 : c / 4 < c * 144 := by nlinarith [hc]
        nlinarith [h2, h3, h4]
      exact (Real.lt_sqrt (by positivity)).mpr hkey
    have hsqrt : Real.sqrt (c / 2) < Real.cos (τ / 2) := by
      rw [Real.sqrt_lt' hcpos, hhalf]
      linarith
    linarith
  have hsum : Real.sin σ + Real.sin (τ - σ) ≤ 2 * Real.sin (τ / 2) := by
    have h := Real.sin_add_sin σ (τ - σ)
    rw [show σ + (τ - σ) = τ from by ring,
      show σ - (τ - σ) = 2 * σ - τ from by ring] at h
    rw [h]
    have hcos_le : Real.cos ((2 * σ - τ) / 2) ≤ 1 := Real.cos_le_one _
    have h2 : 2 * Real.sin (τ / 2) * Real.cos ((2 * σ - τ) / 2)
        ≤ 2 * Real.sin (τ / 2) * 1 :=
      mul_le_mul_of_nonneg_left hcos_le (by positivity)
    linarith
  have hkey : ε₁ * (Real.sin σ + Real.sin (τ - σ)) < Real.sin τ := by
    have h1 : ε₁ * (Real.sin σ + Real.sin (τ - σ)) ≤ ε₁ * (2 * Real.sin (τ / 2)) :=
      mul_le_mul_of_nonneg_left hsum hε₁
    have h2 : ε₁ * (2 * Real.sin (τ / 2)) < Real.cos (τ / 2) * (2 * Real.sin (τ / 2)) := by
      have h3 : 0 < 2 * Real.sin (τ / 2) := by positivity
      nlinarith [hεcos]
    have h4 : Real.cos (τ / 2) * (2 * Real.sin (τ / 2)) = Real.sin τ := by
      have h := Real.sin_two_mul (τ / 2)
      rw [show 2 * (τ / 2) = τ from by ring] at h
      linarith [h]
    linarith [h1, h2, h4]
  rw [twoK_sub_twoD_eq hσ hστ hτπ]
  exact div_pos (by linarith) (by positivity)

/-! ## 2. Jacobi fields under time reversal, and the surjectivity of the two families -/

/-- `IsJacobiAt` only depends on the germ of the curve and of the field. -/
lemma isJacobiAt_congr {γ γ' : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    {J' : (t : ℝ) → TangentSpace I (γ' t)} {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] γ') (hJ : ∀ᶠ s in 𝓝 t, (show E from J s) = (show E from J' s))
    (h : Submission.RauchGlobal.IsJacobiAt cov γ J t) :
    Submission.RauchGlobal.IsJacobiAt cov γ' J' t := by
  obtain ⟨x₀, u, w, y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨x₀, u, w, y, h1, h2, ?_, ?_, h5, h6, h7, h8⟩
  · filter_upwards [h3, hγ] with s hs hs'
    rw [← hs', hs]
  · filter_upwards [h4, hJ, hγ] with s hs hsJ hsγ
    have hA : (show E from Submission.Geodesic.frameVector (I := I) x₀ (γ' s) (y s))
        = (show E from Submission.Geodesic.frameVector (I := I) x₀ (γ s) (y s)) :=
      congrArg
        (fun p : M => (show E from Submission.Geodesic.frameVector (I := I) x₀ p (y s)))
        hsγ.symm
    exact hA.trans (hs.trans hsJ)

/-- The backward family from `γ(τ)`, read backwards along `γ`, is a Jacobi field along `γ`. -/
lemma tcPrayFld_isJacobiAt_gam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) (τ : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v τ)) :
    ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v)
      (fun s : ℝ => tcPrayFld (cov := cov) hmet q v τ η (τ - s)) s := by
  intro s
  have h1 : Submission.RauchGlobal.IsJacobiAt cov
      (fun r : ℝ => tcPray (cov := cov) hmet q v τ (τ - r))
      (fun r : ℝ => tcPrayFld (cov := cov) hmet q v τ η (τ - r)) s :=
    Work.OddBound.polygon.isJacobiAt_comp_sub (cov := cov)
      (γ := tcPray (cov := cov) hmet q v τ)
      (J := tcPrayFld (cov := cov) hmet q v τ η) (t := τ) (s := s)
      (tcPrayFld_isJacobiAt (cov := cov) hmet htor hvn hv0 τ η (τ - s))
  refine isJacobiAt_congr (cov := cov) (t := s) ?_ ?_ h1
  · filter_upwards with r
    exact tc_rev_point (cov := cov) hmet hvn τ r
  · filter_upwards with r
    rfl

/-- **Surjectivity of the forward family at `σ`**: every `X ⊥ γ'(σ)` is `Z_ξ(σ)`. -/
lemma tcFwd_surj (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < rho0 c)
    {X : TangentSpace I (tcGam (cov := cov) hmet q v σ)}
    (hX : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) X
      (tcVel (cov := cov) hmet q v σ) = 0) :
    ∃ ξ : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 ∧
      tcFwd (cov := cov) hmet q v ξ σ = X := by
  obtain ⟨e, he⟩ := Work.OddBound.sqDistChart.isInvertible_mfderiv_GExp_of_norm_lt
    (I := I) (cov := cov) hmet htor (hcut q) (w := σ • v)
    (by rw [norm_smul, Real.norm_of_nonneg hσ0.le, hvn, mul_one]; exact hσ)
  have hval : tcFwd (cov := cov) hmet q v ((1 / σ) • (e.symm X)) σ = X := by
    have h1 : tcFwd (cov := cov) hmet q v ((1 / σ) • (e.symm X)) σ
        = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q w)
            (σ • v)) (e.symm X) := by
      rw [tcFwd_eq_mfderiv]
      congr 1
      rw [smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt hσ0), one_smul]
    rw [h1, ← he]
    exact ContinuousLinearEquiv.apply_symm_apply e X
  have hξ : tcIn (M := M) (I := I) q v ((1 / σ) • (e.symm X)) = 0 := by
    have hG := tcFwd_gauss (cov := cov) hmet htor (q := q) (v := v)
      ((1 / σ) • (e.symm X)) σ
    rw [hval, hX] at hG
    rw [tcIn_symm]
    exact (mul_eq_zero.mp hG.symm).resolve_left (ne_of_gt hσ0)
  exact ⟨_, hξ, hval⟩

/-- **Surjectivity of the backward family at the base point** (the `u = t` case of
`tcPrayFld_surj`): every `W ⊥ v` is the value at `q` of the backward field from `γ(t)`. -/
lemma tcPrayFld_surj_base (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht : t < rho0 c)
    {W : TangentSpace I q} (hW : tcIn (M := M) (I := I) q v W = 0) :
    ∃ η : TangentSpace I (tcGam (cov := cov) hmet q v t),
      tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t) η
          (-(tcVel (cov := cov) hmet q v t)) = 0 ∧
      tcPrayFld (cov := cov) hmet q v t η t = W := by
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  obtain ⟨e, he⟩ := Work.OddBound.sqDistChart.isInvertible_mfderiv_GExp_of_norm_lt
    (I := I) (cov := cov) hmet htor (hcut (tcGam (cov := cov) hmet q v t))
    (w := t • (-(tcVel (cov := cov) hmet q v t)))
    (by rw [norm_smul, Real.norm_of_nonneg ht0.le, hwn, mul_one]; exact ht)
  have hval : tcPrayFld (cov := cov) hmet q v t ((1 / t) • (e.symm W)) t = W := by
    have h1 : tcPrayFld (cov := cov) hmet q v t ((1 / t) • (e.symm W)) t
        = (mfderiv 𝓘(ℝ, E) I
            (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet
              (tcGam (cov := cov) hmet q v t) w)
            (t • (-(tcVel (cov := cov) hmet q v t)))) (e.symm W) := by
      rw [tcPrayFld_eq_mfderiv]
      congr 1
      rw [smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
    rw [h1, ← he]
    exact ContinuousLinearEquiv.apply_symm_apply e W
  refine ⟨(1 / t) • (e.symm W), ?_, hval⟩
  have hpt : tcPray (cov := cov) hmet q v t t = q := by
    have h := tc_rev_point (cov := cov) hmet hvn t 0
    rw [sub_zero] at h
    show Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
      (t • (-(tcVel (cov := cov) hmet q v t))) = q
    rw [h]
    simp [tcGam, zero_smul]
  have hvel : Submission.Geodesic.curveVelocity (I := I)
      (tcPray (cov := cov) hmet q v t) t = -v := by
    have h := tc_rev_vel (cov := cov) hmet hvn hv0 t 0
    rw [sub_zero, tcVel_zero (cov := cov) hmet hv0] at h
    exact h
  have hG := tcPrayFld_gauss (cov := cov) (q := q) (v := v) hmet htor t
    ((1 / t) • (e.symm W)) t
  rw [hval, hpt, hvel] at hG
  have hWv : tcIn (M := M) (I := I) q W (-v) = 0 := by
    rw [tcIn_eq, inner_neg_right, neg_eq_zero, real_inner_comm, ← tcIn_eq]
    exact hW
  rw [hWv] at hG
  exact (mul_eq_zero.mp hG.symm).resolve_left (ne_of_gt ht0)

/-- **The forward shape identity, with an arbitrary second argument.** -/
lemma tcFwd_shape_all (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < rho0 c)
    (ξ : TangentSpace I q) (hξ : tcIn (M := M) (I := I) q v ξ = 0)
    (X : TangentSpace I (tcGam (cov := cov) hmet q v σ))
    (hX : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) X
      (tcVel (cov := cov) hmet q v σ) = 0) :
    tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (tcFwd (cov := cov) hmet q v ξ) σ) X
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ) X := by
  obtain ⟨ξ', hξ', hval⟩ := tcFwd_surj (cov := cov) hmet htor hcut hvn hv0 hσ0 hσ hX
  rw [← hval]
  exact tcFwd_bridge_bilin (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hξ hξ' hσ0 hσ

/-! ## 3. The shape relation at the base point -/

/-- The `u = t` case of `tcPrayFld_bridge`: the radial variation field of the family of rays out of
`γ(t)` realises the shape operator of the sphere around `γ(t)` **at the base point `q`**. -/
lemma tcPrayFld_bridge_base (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c) (η : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t) η
      (-(tcVel (cov := cov) hmet q v t)) = 0) :
    tcIn (M := M) (I := I) (tcPray (cov := cov) hmet q v t t)
        (Submission.JacobiGlobal.covAlong cov (γ := tcPray (cov := cov) hmet q v t)
          (tcPrayFld (cov := cov) hmet q v t η) t)
        (tcPrayFld (cov := cov) hmet q v t η t)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η t)
          (tcPrayFld (cov := cov) hmet q v t η t) := by
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0 : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; norm_num at hwn
  by_cases hz : tcPrayFld (cov := cov) hmet q v t η t = 0
  · rw [hz, tcIn_zero_right]
    simp [rhess]
  · have hu' : Inner.inner ℝ (-(tcVel (cov := cov) hmet q v t))
        (-(tcVel (cov := cov) hmet q v t)) = 1 := by
      rw [real_inner_self_eq_norm_sq, hwn]; norm_num
    have horth' : Inner.inner ℝ (-(tcVel (cov := cov) hmet q v t)) η = 0 := by
      have hη' : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t)
          (-(tcVel (cov := cov) hmet q v t)) η = 0 := by
        rw [tcIn_symm]; exact hη
      rw [← tcIn_eq]; exact hη'
    -- the base point is `q`
    have hpt' : Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
        (t • (-(tcVel (cov := cov) hmet q v t))) = q := by
      have h := tc_rev_point (cov := cov) hmet hvn t 0
      rw [sub_zero] at h
      rw [h]
      simp [tcGam, zero_smul]
    have hrd : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = t := by
      have h := tc_rdist_bwd (cov := cov) hmet htor hcut hvn ht.le ht0 (s := 0) le_rfl ht0
      rw [sub_zero] at h
      rwa [show tcGam (cov := cov) hmet q v 0 = q from by simp [tcGam, zero_smul]] at h
    have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v t) z)
        (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          (t • (-(tcVel (cov := cov) hmet q v t)))) := by
      rw [hpt']
      exact csm_rdist_of_le_rho hc0 hc1 hsmC (q := tcGam (cov := cov) hmet q v t) (y := q)
        (by rw [hrd]; exact ht0) (by rw [hrd]; exact ht.le)
    have hvelrev : Submission.Geodesic.curveVelocity (I := I)
        (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          (u • (-(tcVel (cov := cov) hmet q v t)))) t = -v := by
      have h := tc_rev_vel (cov := cov) hmet hvn hv0 t 0
      rw [sub_zero, tcVel_zero (cov := cov) hmet hv0] at h
      exact h
    have hrgrad : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
          (tcGam (cov := cov) hmet q v t) z)
        (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          (t • (-(tcVel (cov := cov) hmet q v t))))
        = Submission.Geodesic.curveVelocity (I := I)
          (fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
            (u • (-(tcVel (cov := cov) hmet q v t)))) t := by
      rw [hvelrev, hpt']
      exact rgrad_rdist_back (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht
    have hcsm : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          (t • (-(tcVel (cov := cov) hmet q v t) + s • η))) := by
      intro s
      have hfam := Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet
        (p := tcGam (cov := cov) hmet q v t) (u := -(tcVel (cov := cov) hmet q v t)) (η := η) t s
      have hpair : ContMDiffAt (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
          (fun s' : ℝ => (t, s')) s := by
        rw [contMDiffAt_iff_contDiffAt]; fun_prop
      exact (hfam.comp s hpair).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s' => rfl)
    have hne : Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          (t • (-(tcVel (cov := cov) hmet q v t) + s • η))) 0 ≠ 0 := hz
    have hminW := tc_minW_bwd (cov := cov) hmet htor hcut hvn hv0 ht0 ht η
    exact Work.Diff.C.dmRadialBridge (I := I) (M := M) (cov := cov) hmet htor
      (p := tcGam (cov := cov) hmet q v t) (d := t) ht0 hu' horth' hsm hrgrad hcsm hne hminW

/-- The `u = t` case of `tcPrayFld_bridge_bilin`. -/
lemma tcPrayFld_bridge_bilin_base (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c)
    (η η' : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (tcGam (cov := cov) hmet q v t) η (-(tcVel (cov := cov) hmet q v t)) = 0)
    (hη' : tcIn (tcGam (cov := cov) hmet q v t) η' (-(tcVel (cov := cov) hmet q v t)) = 0) :
    tcIn (tcPray (cov := cov) hmet q v t t)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) t)
        (tcPrayFld (cov := cov) hmet q v t η' t)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η t)
          (tcPrayFld (cov := cov) hmet q v t η' t) := by
  have hsum0 : tcIn (tcGam (cov := cov) hmet q v t) (η + η')
      (-(tcVel (cov := cov) hmet q v t)) = 0 := by
    rw [tcIn_add_left]; simp [hη, hη']
  have hsum := tcPrayFld_bridge_base (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht
    (η + η') hsum0
  have h1 := tcPrayFld_bridge_base (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht η hη
  have h2 := tcPrayFld_bridge_base (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht η' hη'
  have hwn0 : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0' : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn0; norm_num at hwn0
  have hγfull : ContMDiff 𝓘(ℝ) I ∞ (tcPray (cov := cov) hmet q v t) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet
      (tcGam (cov := cov) hmet q v t) hw0'
  have hγ : ContMDiffOn 𝓘(ℝ) I ∞ (tcPray (cov := cov) hmet q v t) (Set.Ioo (t - 1) (t + 1)) :=
    hγfull.contMDiffOn
  have hnefull : ∀ r : ℝ, Submission.Geodesic.curveVelocity (I := I)
      (tcPray (cov := cov) hmet q v t) r ≠ 0 := fun r =>
    Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hw0' r
  have hJη := tcPrayFld_isJacobiAt (cov := cov) hmet htor hvn hv0 t η
  have hJη' := tcPrayFld_isJacobiAt (cov := cov) hmet htor hvn hv0 t η'
  have hsmη := Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJη hγ
  have hsmη' := Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJη' hγ
  have hW := tc_wronskian_const (cov := cov) hmet htor hγfull hnefull hJη hJη' 0 t
  have hW0 : tcIn (tcPray (cov := cov) hmet q v t 0)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) 0)
        (tcPrayFld (cov := cov) hmet q v t η' 0)
      - tcIn (tcPray (cov := cov) hmet q v t 0) (tcPrayFld (cov := cov) hmet q v t η 0)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') 0) = 0 := by
    rw [tcPrayFld_zero, tcPrayFld_zero]
    simp only [tcIn_zero_left, tcIn_zero_right, sub_zero]
  rw [hW0] at hW
  have hW' : tcIn (tcPray (cov := cov) hmet q v t t)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) t)
      (tcPrayFld (cov := cov) hmet q v t η' t)
      = tcIn (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η t)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') t) := by
    linarith [hW]
  have hsym : tcIn (tcPray (cov := cov) hmet q v t t)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) t)
      (tcPrayFld (cov := cov) hmet q v t η' t)
      = tcIn (tcPray (cov := cov) hmet q v t t)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') t)
        (tcPrayFld (cov := cov) hmet q v t η t) := by
    rw [tcIn_symm (tcPray (cov := cov) hmet q v t t)
      (tcPrayFld (cov := cov) hmet q v t η t)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') t)] at hW'
    exact hW'
  have hfun : tcPrayFld (cov := cov) hmet q v t (η + η')
      = fun r : ℝ => tcPrayFld (cov := cov) hmet q v t η r
          + tcPrayFld (cov := cov) hmet q v t η' r := by
    funext r; exact tcPrayFld_add (cov := cov) (q := q) (v := v) hmet t η η' r
  have hexp : tcIn (tcPray (cov := cov) hmet q v t t)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t (η + η')) t)
      (tcPrayFld (cov := cov) hmet q v t (η + η') t)
      = tcIn (tcPray (cov := cov) hmet q v t t)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) t)
          (tcPrayFld (cov := cov) hmet q v t η t)
        + tcIn (tcPray (cov := cov) hmet q v t t)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) t)
          (tcPrayFld (cov := cov) hmet q v t η' t)
        + tcIn (tcPray (cov := cov) hmet q v t t)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') t)
          (tcPrayFld (cov := cov) hmet q v t η t)
        + tcIn (tcPray (cov := cov) hmet q v t t)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') t)
          (tcPrayFld (cov := cov) hmet q v t η' t) := by
    rw [hfun, Submission.ConjEnergy.covAlong_add (cov := cov) htor hsmη hsmη']
    simp only [tcIn_add_left, tcIn_add_right]
    abel
  have hexpR : rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
      (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t (η + η') t)
      (tcPrayFld (cov := cov) hmet q v t (η + η') t)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η t)
          (tcPrayFld (cov := cov) hmet q v t η t)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η t)
          (tcPrayFld (cov := cov) hmet q v t η' t)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η' t)
          (tcPrayFld (cov := cov) hmet q v t η t)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η' t)
          (tcPrayFld (cov := cov) hmet q v t η' t) := by
    rw [hfun]
    simp only [Work.Diff.C.GeoCrux.rhess_add_left, Work.Diff.C.GeoCrux.rhess_add_right]
    abel
  rw [hexp, hexpR, h1, h2] at hsum
  have hRsym : rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
      (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η t)
      (tcPrayFld (cov := cov) hmet q v t η' t)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
        (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η' t)
        (tcPrayFld (cov := cov) hmet q v t η t) := by
    refine Work.Diff.C.rhess_symm (I := I) (M := M) (cov := cov) hmet htor ?_
      (tcPrayFld (cov := cov) hmet q v t η t) (tcPrayFld (cov := cov) hmet q v t η' t)
    have hpt : tcPray (cov := cov) hmet q v t t = q := by
      have h := tc_rev_point (cov := cov) hmet hvn t 0
      rw [sub_zero] at h
      show Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
        (t • (-(tcVel (cov := cov) hmet q v t))) = q
      rw [h]
      simp [tcGam, zero_smul]
    rw [hpt]
    have hrd : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = t := by
      have h := tc_rdist_bwd (cov := cov) hmet htor hcut hvn ht.le ht0 (s := 0) le_rfl ht0
      rw [sub_zero] at h
      rwa [show tcGam (cov := cov) hmet q v 0 = q from by simp [tcGam, zero_smul]] at h
    exact csm_rdist_of_le_rho hc0 hc1 hsmC (q := tcGam (cov := cov) hmet q v t) (y := q)
      (by rw [hrd]; exact ht0) (by rw [hrd]; exact ht.le)
  linarith [hsum, hsym, hRsym]

/-- The `u = t` case of `tcPrayFld_shape_all`. -/
lemma tcPrayFld_shape_all_base (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (tcGam (cov := cov) hmet q v t) η (-(tcVel (cov := cov) hmet q v t)) = 0)
    (X : TangentSpace I q) (hX : tcIn (M := M) (I := I) q v X = 0) :
    tcIn (M := M) (I := I) (tcPray (cov := cov) hmet q v t t)
        (Submission.JacobiGlobal.covAlong cov (γ := tcPray (cov := cov) hmet q v t)
          (tcPrayFld (cov := cov) hmet q v t η) t) X
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t t) (tcPrayFld (cov := cov) hmet q v t η t) X := by
  obtain ⟨η', hη', hval⟩ := tcPrayFld_surj_base (cov := cov) hmet htor hcut hvn hv0 ht0 ht
    (W := X) hX
  rw [← hval]
  exact tcPrayFld_bridge_bilin_base (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht
    η η' hη hη'

/-- **The shape relation at the base point `q`** (the `σ → 0` case of `tcBwd_shape_gam`), in the
form used by the two-centre argument: the covariant derivative at `q` of the backward field
`s ↦ tcPrayFld hmet q v t η (t - s)` is `- Hess (rdist (γ t))(q)` applied to its value at `q`. -/
lemma tcBaseShape (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t) η
      (-(tcVel (cov := cov) hmet q v t)) = 0)
    (X : TangentSpace I q) (hX : tcIn (M := M) (I := I) q v X = 0) :
    tcIn (M := M) (I := I) q
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) 0) X
      = - rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          q (tcPrayFld (cov := cov) hmet q v t η t) X := by
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0' : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; norm_num at hwn
  have hγfull : ContMDiff 𝓘(ℝ) I ∞ (tcPray (cov := cov) hmet q v t) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet
      (tcGam (cov := cov) hmet q v t) hw0'
  have hpt : ∀ s : ℝ, tcPray (cov := cov) hmet q v t (t - s) = tcGam (cov := cov) hmet q v s :=
    fun s => tc_rev_point (cov := cov) hmet hvn t s
  have hshape := tcPrayFld_shape_all_base (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht
    η hη X hX
  have htr := covAlong_comp_sub (cov := cov) htor
    (γ := tcPray (cov := cov) hmet q v t)
    (V := tcPrayFld (cov := cov) hmet q v t η) (T := t) (t := 0)
    (by exact hγfull.contMDiffOn)
    (by
      show Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t) (t - 0) ≠ 0
      rw [sub_zero]
      exact Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hw0' t)
    (by
      show Submission.JacobiGlobal.SmoothAlongAt (I := I) (tcPray (cov := cov) hmet q v t)
        (tcPrayFld (cov := cov) hmet q v t η) (t - 0)
      rw [sub_zero]
      exact Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor
        (tcPrayFld_isJacobiAt (cov := cov) hmet htor hvn hv0 t η) hγfull.contMDiffOn)
  rw [covAlong_congr_curve
    (γ₁ := fun s : ℝ => tcPray (cov := cov) hmet q v t (t - s))
    (γ₂ := tcGam (cov := cov) hmet q v)
    (by funext s; exact hpt s)
    (fun s => rfl) 0] at htr
  rw [sub_zero] at htr
  rw [show tcPray (cov := cov) hmet q v t t = q from by
      have h := tc_rev_point (cov := cov) hmet hvn t 0
      rw [sub_zero] at h
      show Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
        (t • (-(tcVel (cov := cov) hmet q v t))) = q
      rw [h]
      simp [tcGam, zero_smul]] at hshape
  have htr' : Submission.JacobiGlobal.covAlong cov (γ := tcPray (cov := cov) hmet q v t)
        (tcPrayFld (cov := cov) hmet q v t η) t
      = - Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) 0 := by
    rw [htr, neg_neg]
  rw [htr'] at hshape
  rw [show (-(Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) 0))
      = (-1 : ℝ) • (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) 0) from
    (neg_one_smul ℝ _).symm, tcIn_smul_left] at hshape
  have hspec' : rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
        q (tcPrayFld (cov := cov) hmet q v t η t) X
      = - tcIn (M := M) (I := I) q
          (tcShape (cov := cov) hmet q v t (tcPrayFld (cov := cov) hmet q v t η t)) X := by
    rw [tcShape_spec (cov := cov) hmet q v t (tcPrayFld (cov := cov) hmet q v t η t) X]
    ring
  rw [hspec'] at hshape
  rw [neg_one_mul] at hshape
  rw [hspec']
  linarith [hshape]


/-! ## 3b. The operator `ℭ = 𝔎(τ) - 𝔎(σ)` -/

/-- `ℭ = 𝔎(τ) - 𝔎(σ)`, the difference of the two shape operators of the geodesic spheres through
`q`: `𝔎(t) W = - Hess (rdist (γ t))(q) W = tcShape hmet q v t W`. -/
noncomputable def tcC (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q)
    (σ τ : ℝ) (W : TangentSpace I q) : TangentSpace I q :=
  tcShape (cov := cov) hmet q v τ W - tcShape (cov := cov) hmet q v σ W

lemma tcC_add (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (σ τ : ℝ)
    (W W' : TangentSpace I q) :
    tcC (cov := cov) hmet q v σ τ (W + W')
      = tcC (cov := cov) hmet q v σ τ W + tcC (cov := cov) hmet q v σ τ W' := by
  rw [tcC, tcShape_add, tcShape_add, tcC, tcC, add_sub_add_comm]

lemma tcC_smul (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (σ τ : ℝ)
    (a : ℝ) (W : TangentSpace I q) :
    tcC (cov := cov) hmet q v σ τ (a • W) = a • tcC (cov := cov) hmet q v σ τ W := by
  rw [tcC, tcShape_smul, tcShape_smul, tcC, smul_sub]

/-- The bilinear form of `ℭ`: `⟪ℭW, W'⟫ = - Hess (rdist (γ τ))(q)(W,W') + Hess (rdist (γ σ))(q)(W,W')`. -/
lemma tcC_spec (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (σ τ : ℝ)
    (W W' : TangentSpace I q) :
    tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ τ W) W'
      = - rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
          q W W'
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) z)
          q W W' := by
  rw [tcC, tcIn_sub_left, tcShape_spec, tcShape_spec]
  ring

/-! ## 4. The shape operators kill the radial direction -/

/-- **The shape operators kill the radial direction**: `𝔎(t) W ⊥ γ'(0)` for every `W`.

This is `rhess_radial_eq_zero` (`Hess F (W, ∇F) = 0` for the distance function `F = rdist (γ t)` at
the base point `q`, where `∇F(q) = -v`), together with `tcShape_spec`. -/
lemma tcShape_orth_v (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht : t < rho0 c)
    (W : TangentSpace I q) :
    tcIn (M := M) (I := I) q (tcShape (cov := cov) hmet q v t W) v = 0 := by
  have hv0 : v ≠ 0 := by intro h0; rw [h0, norm_zero] at hvn; norm_num at hvn
  have hrd : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = t := by
    have h := tc_rdist_bwd (cov := cov) hmet htor hcut hvn ht.le ht0 (s := 0) le_rfl ht0
    rw [sub_zero] at h
    rwa [show tcGam (cov := cov) hmet q v 0 = q from by simp [tcGam, zero_smul]] at h
  have hFsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z) q :=
    csm_rdist_of_le_rho hc0 hc1 hsmC (q := tcGam (cov := cov) hmet q v t) (y := q)
      (by rw [hrd]; exact ht0) (by rw [hrd]; exact ht.le)
  have hgrad : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z) q = -v :=
    rgrad_rdist_back (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 ht
  have hunit : Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z) q)
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z) q) = 1 := by
    rw [hgrad, inner_neg_neg, real_inner_self_eq_norm_sq, hvn]; norm_num
  have hlip : ∀ y : M, Inner.inner ℝ (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z) y)
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z) y) ≤ 1 := by
    intro y
    refine Work.Diff.C.inner_rgrad_self_le_one (I := I) (cov := cov) hmet htor ?_ y
    intro y' z'
    have hcomm : ∀ a b : M, rdist (I := I) (M := M) a b = rdist (I := I) (M := M) b a := by
      intro a b
      rw [Work.Diff.C.rdist, Work.Diff.C.rdist, Manifold.riemannianEDist_comm]
    have h1 : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) y'
        ≤ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z'
          + rdist (I := I) (M := M) z' y' :=
      eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor
        (tcGam (cov := cov) hmet q v t) z' y'
    have h2 : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z'
        ≤ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) y'
          + rdist (I := I) (M := M) y' z' :=
      eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor
        (tcGam (cov := cov) hmet q v t) y' z'
    rw [hcomm z' y'] at h1
    rw [abs_le]
    constructor <;> linarith
  have hrad := Work.Diff.C.rhess_radial_eq_zero (I := I) (cov := cov) hmet htor
    (F := fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
    hFsm hunit hlip W
  rw [hgrad,
    show (-v : TangentSpace I q) = (-1 : ℝ) • v from (neg_one_smul ℝ v).symm,
    Work.Diff.C.GeoCrux.rhess_smul_right] at hrad
  have hrv : rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
      q W v = 0 := by linarith [hrad]
  rw [tcShape_spec (cov := cov) hmet q v t W v, hrv, neg_zero]

/-- `ℭ W ⊥ v` for every `W`. -/
lemma tcC_orth_v (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ)
    (hτ : τ < rho0 c) (W : TangentSpace I q) :
    tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ τ W) v = 0 := by
  rw [tcC, tcIn_sub_left,
    tcShape_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn (lt_trans hσ0 hστ) hτ W,
    tcShape_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 (lt_of_lt_of_le hστ hτ.le) W,
    sub_zero]

/-! ## 5. The identification of the backward field -/

/-- The forward field with zero direction vanishes identically. -/
lemma tcFwd_zero' (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (s : ℝ) :
    tcFwd (cov := cov) hmet q v 0 s = 0 := by
  rw [tcFwd_eq_mfderiv, smul_zero, map_zero]

/-- **The identification of the backward field.** -/
lemma tcBackwardID (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v τ))
    (hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v τ) η
      (-(tcVel (cov := cov) hmet q v τ)) = 0) :
    tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
      = tcFwd (cov := cov) hmet q v
          (tcC (cov := cov) hmet q v σ τ (tcPrayFld (cov := cov) hmet q v τ η τ)) σ := by
  classical
  have hτ0 : 0 < τ := lt_trans hσ0 hστ
  let W : E := tcPrayFld (cov := cov) hmet q v τ η τ
  let ξ₀ : E := tcC (cov := cov) hmet q v σ τ W
  have hWdef : W = tcPrayFld (cov := cov) hmet q v τ η τ := rfl
  have hξ0def : ξ₀ = tcC (cov := cov) hmet q v σ τ W := rfl
  -- `W ⊥ v`
  have hW : tcIn (M := M) (I := I) q v W = 0 := by
    have hg := tcPrayFld_gauss (cov := cov) (q := q) (v := v) hmet htor τ η τ
    rw [hη, mul_zero] at hg
    have hpt : tcPray (cov := cov) hmet q v τ τ = q := by
      have h := tc_rev_point (cov := cov) hmet hvn τ 0
      rw [sub_zero] at h
      show Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v τ)
        (τ • (-(tcVel (cov := cov) hmet q v τ))) = q
      rw [h]
      simp [tcGam, zero_smul]
    rw [tcIn_pt (X := tcPray (cov := cov) hmet q v τ τ) (Y := q) hpt
      (show E from W)
      (show E from Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v τ) τ)] at hg
    have hvelrev : Submission.Geodesic.curveVelocity (I := I)
        (tcPray (cov := cov) hmet q v τ) τ = -v := by
      have h := tc_rev_vel (cov := cov) hmet hvn hv0 τ 0
      rw [sub_zero, tcVel_zero (cov := cov) hmet hv0] at h
      exact h
    rw [hvelrev, show (-v : TangentSpace I q) = (-1 : ℝ) • v from (neg_one_smul ℝ v).symm,
      tcIn_smul_right] at hg
    have h1 : tcIn (M := M) (I := I) q W v = 0 := by linarith [hg]
    rwa [tcIn_symm] at h1
  obtain ⟨η', hη', hval'⟩ := tcPrayFld_surj_base (cov := cov) hmet htor hcut hvn hv0 hσ0
    (lt_trans hστ hτ) (W := W) hW
  -- the three fields, as functions into `E`
  let Jf : ℝ → E := fun s => tcPrayFld (cov := cov) hmet q v τ η (τ - s)
  let Zf : ℝ → E := fun s => tcFwd (cov := cov) hmet q v ξ₀ s
  let Pf : ℝ → E := fun s => tcPrayFld (cov := cov) hmet q v σ η' (σ - s)
  have hγ : ContMDiff 𝓘(ℝ) I ∞ (tcGam (cov := cov) hmet q v) :=
    tcGam_contMDiff (cov := cov) hmet hv0
  have hne : ∀ s : ℝ, Submission.Geodesic.curveVelocity (I := I) (tcGam (cov := cov) hmet q v) s
      ≠ 0 := fun s => tcVel_ne_zero (cov := cov) hmet hv0 s
  have hJX : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v) Jf s :=
    tcPrayFld_isJacobiAt_gam (cov := cov) hmet htor hvn hv0 τ η
  have hJZ : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v) Zf s :=
    fun s => tcFwd_isJacobiAt (cov := cov) hmet htor hv0 hvn ξ₀ s
  have hJP : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v) Pf s :=
    tcPrayFld_isJacobiAt_gam (cov := cov) hmet htor hvn hv0 σ η'
  have hJK0 : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v)
      (fun r : ℝ => Jf r - Zf r) s :=
    fun s => TwoCentre.isJacobiAt_sub_field (cov := cov) htor (hJX s) (hJZ s)
  have hJK : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v)
      (fun r : ℝ => (Jf r - Zf r) - Pf r) s :=
    fun s => TwoCentre.isJacobiAt_sub_field (cov := cov) htor (hJK0 s) (hJP s)
  have hK0 : (fun r : ℝ => (Jf r - Zf r) - Pf r) 0 = 0 := by
    have hJ0 : Jf 0 = W := by
      have h1 : Jf 0 = tcPrayFld (cov := cov) hmet q v τ η (τ - 0) := rfl
      rw [h1, sub_zero]
    have hZ0 : Zf 0 = 0 := tcFwd_zero (cov := cov) (hmet := hmet) (q := q) (v := v) (ξ := ξ₀)
    have hP0 : Pf 0 = W := by
      have h1 : Pf 0 = tcPrayFld (cov := cov) hmet q v σ η' (σ - 0) := rfl
      rw [h1, sub_zero]
      exact hval'
    simp only [hJ0, hZ0, hP0]
    abel
  have hcov1 : Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
      (fun r : ℝ => (Jf r - Zf r) - Pf r) 0
      = Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun r : ℝ => Jf r - Zf r) 0
        - Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v) Pf 0 :=
    Work.Diff.C.covAlong_sub (cov := cov) htor hγ hJK0 hJP 0
  have hcov2 : Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
      (fun r : ℝ => Jf r - Zf r) 0
      = Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v) Jf 0
        - Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v) Zf 0 :=
    Work.Diff.C.covAlong_sub (cov := cov) htor hγ hJX hJZ 0
  have hZder : Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v) Zf 0 = ξ₀ := by
    show Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
      (fun s : ℝ => tcFwd (cov := cov) hmet q v ξ₀ s) 0 = ξ₀
    exact tcFwd_covAlong_zero (cov := cov) hmet htor hv0 ξ₀
  have hpair : ∀ X : E, tcIn (M := M) (I := I) q v X = 0 →
      tcIn (M := M) (I := I) q (Submission.JacobiGlobal.covAlong cov
        (γ := tcGam (cov := cov) hmet q v) (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) X = 0 := by
    intro X hX
    rw [hcov1, tcIn_sub_left, hcov2, tcIn_sub_left, hZder, hξ0def,
      tcBaseShape (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hτ0 hτ η hη X hX,
      tcC_spec (cov := cov) hmet q v σ τ W X,
      tcBaseShape (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 (lt_trans hστ hτ) η' hη' X hX]
    rw [show tcPrayFld (cov := cov) hmet q v σ η' σ = W from hval']
    ring
  have hKdecomp : ∀ s : ℝ, (fun r : ℝ => (Jf r - Zf r) - Pf r) s
      = tcFwd (cov := cov) hmet q v (show E from Submission.JacobiGlobal.covAlong cov
          (γ := tcGam (cov := cov) hmet q v) (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) s := by
    intro s
    exact Work.Diff.C.geoCrux.Port.TwoCentre.jacobi_uniq (cov := cov) htor hγ hne hJK
      (fun r => tcFwd_isJacobiAt (cov := cov) hmet htor hv0 hvn _ r)
      (by rw [tcFwd_zero]; exact hK0)
      (by rw [tcFwd_covAlong_zero (cov := cov) hmet htor hv0]) s
  have hKσv : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
      ((fun r : ℝ => (Jf r - Zf r) - Pf r) σ) (tcVel (cov := cov) hmet q v σ) = 0 := by
    have hJv : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (Jf σ) (tcVel (cov := cov) hmet q v σ) = 0 := by
      show tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)) (tcVel (cov := cov) hmet q v σ) = 0
      have h := tcPrayFld_gauss (cov := cov) (q := q) (v := v) hmet htor τ η (τ - σ)
      rw [hη, mul_zero] at h
      have hvel : Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v τ)
          (τ - σ) = -(tcVel (cov := cov) hmet q v σ) :=
        tc_rev_vel (cov := cov) hmet hvn hv0 τ σ
      rw [tcIn_pt (X := tcPray (cov := cov) hmet q v τ (τ - σ))
        (Y := tcGam (cov := cov) hmet q v σ) (tc_rev_point (cov := cov) hmet hvn τ σ)
        (show E from tcPrayFld (cov := cov) hmet q v τ η (τ - σ))
        (show E from Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v τ)
          (τ - σ))] at h
      rw [hvel, show (-(tcVel (cov := cov) hmet q v σ))
          = (-1 : ℝ) • (tcVel (cov := cov) hmet q v σ) from (neg_one_smul ℝ _).symm,
        tcIn_smul_right] at h
      linarith [h]
    have hZv : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (Zf σ) (tcVel (cov := cov) hmet q v σ) = 0 := by
      show tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v ξ₀ σ) (tcVel (cov := cov) hmet q v σ) = 0
      rw [tcFwd_gauss (cov := cov) hmet htor (q := q) (v := v) ξ₀ σ, hξ0def,
        tcC_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hστ hτ W, mul_zero]
    have hPv : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (Pf σ) (tcVel (cov := cov) hmet q v σ) = 0 := by
      show tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcPrayFld (cov := cov) hmet q v σ η' (σ - σ)) (tcVel (cov := cov) hmet q v σ) = 0
      rw [sub_self, tcPrayFld_zero (cov := cov) hmet σ η', tcIn_zero_left]
    show tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
      ((Jf σ - Zf σ) - Pf σ) (tcVel (cov := cov) hmet q v σ) = 0
    rw [tcIn_sub_left, tcIn_sub_left, hJv, hZv, hPv]
    ring
  have hgrad : (show TangentSpace I q from Submission.JacobiGlobal.covAlong cov
      (γ := tcGam (cov := cov) hmet q v) (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) = 0 := by
    rw [hKdecomp σ,
      tcFwd_gauss (cov := cov) hmet htor (q := q) (v := v)
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) σ] at hKσv
    have hv1 : tcIn (M := M) (I := I) q (Submission.JacobiGlobal.covAlong cov
        (γ := tcGam (cov := cov) hmet q v) (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) v = 0 := by
      have h0 : σ * tcIn (M := M) (I := I) q (Submission.JacobiGlobal.covAlong cov
          (γ := tcGam (cov := cov) hmet q v) (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) v = 0 := by
        linarith [hKσv]
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt hσ0)
      · exact h
    have hv2 : tcIn (M := M) (I := I) q v (Submission.JacobiGlobal.covAlong cov
        (γ := tcGam (cov := cov) hmet q v) (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) = 0 := by
      rw [tcIn_symm]; exact hv1
    have hself := hpair (show E from Submission.JacobiGlobal.covAlong cov
      (γ := tcGam (cov := cov) hmet q v) (fun r : ℝ => (Jf r - Zf r) - Pf r) 0) hv2
    have h := hself
    rw [tcIn_eq] at h
    exact inner_self_eq_zero.mp h
  have hKall := Work.Diff.C.eq_of_dual_zero (cov := cov) htor hγ hne hJK hK0 hgrad
  have hσ' : tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
      = tcFwd (cov := cov) hmet q v ξ₀ σ := by
    have h := hKall σ
    have hPσ : Pf σ = 0 := by
      show tcPrayFld (cov := cov) hmet q v σ η' (σ - σ) = 0
      rw [sub_self]; exact tcPrayFld_zero (cov := cov) hmet σ η'
    have hJσ : Jf σ = tcPrayFld (cov := cov) hmet q v τ η (τ - σ) := rfl
    have hZσ : Zf σ = tcFwd (cov := cov) hmet q v ξ₀ σ := rfl
    rw [hJσ, hZσ, hPσ, sub_zero] at h
    exact sub_eq_zero.mp h
  calc tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
      = tcFwd (cov := cov) hmet q v ξ₀ σ := hσ'
    _ = tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ
          (tcPrayFld (cov := cov) hmet q v τ η τ)) σ := by rw [hξ0def, hWdef]

/-! ## 6. The Wronskian identity of the two-centre argument -/

lemma tcFwd_orth (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (ξ : TangentSpace I q) (hξ : tcIn (M := M) (I := I) q v ξ = 0)
    {σ : ℝ} :
    tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
      (tcVel (cov := cov) hmet q v σ) = 0 := by
  rw [tcFwd_gauss (cov := cov) hmet htor (q := q) (v := v) ξ σ]
  rw [show tcIn (M := M) (I := I) q ξ v = 0 from by rw [tcIn_symm]; exact hξ, mul_zero]

lemma tcPrayFld_orth (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {τ : ℝ}
    (η : TangentSpace I (tcGam (cov := cov) hmet q v τ))
    (hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v τ) η
      (-(tcVel (cov := cov) hmet q v τ)) = 0) {σ : ℝ} :
    tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
      (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)) (tcVel (cov := cov) hmet q v σ) = 0 := by
  have h := tcPrayFld_gauss (cov := cov) (q := q) (v := v) hmet htor τ η (τ - σ)
  rw [hη, mul_zero] at h
  have hvel : Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v τ)
      (τ - σ) = -(tcVel (cov := cov) hmet q v σ) :=
    tc_rev_vel (cov := cov) hmet hvn hv0 τ σ
  rw [tcIn_pt (X := tcPray (cov := cov) hmet q v τ (τ - σ)) (Y := tcGam (cov := cov) hmet q v σ)
    (tc_rev_point (cov := cov) hmet hvn τ σ)
    (show E from tcPrayFld (cov := cov) hmet q v τ η (τ - σ))
    (show E from Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v τ)
      (τ - σ))] at h
  rw [hvel, show (-(tcVel (cov := cov) hmet q v σ))
      = (-1 : ℝ) • (tcVel (cov := cov) hmet q v σ) from (neg_one_smul ℝ _).symm,
    tcIn_smul_right] at h
  linarith [h]

/-- **The Wronskian identity of the two-centre argument.** -/
lemma tcWronskian_twoCentre (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (ξ : TangentSpace I q) (hξ : tcIn (M := M) (I := I) q v ξ = 0)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v τ))
    (hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v τ) η
      (-(tcVel (cov := cov) hmet q v τ)) = 0) :
    rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
        (tcPrayFld (cov := cov) hmet q v τ η (τ - σ))
      + rhess cov (fun z : M ↦ rdist (I := I) (M := M)
            (tcGam (cov := cov) hmet q v τ) z)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
          (tcPrayFld (cov := cov) hmet q v τ η (τ - σ))
      = tcIn (M := M) (I := I) q ξ (tcPrayFld (cov := cov) hmet q v τ η τ) := by
  have hτ0 : 0 < τ := lt_trans hσ0 hστ
  have hγ : ContMDiff 𝓘(ℝ) I ∞ (tcGam (cov := cov) hmet q v) :=
    tcGam_contMDiff (cov := cov) hmet hv0
  have hne : ∀ s : ℝ, Submission.Geodesic.curveVelocity (I := I) (tcGam (cov := cov) hmet q v) s
      ≠ 0 := fun s => tcVel_ne_zero (cov := cov) hmet hv0 s
  have hJ : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v)
      (tcFwd (cov := cov) hmet q v ξ) s := tcFwd_isJacobiAt (cov := cov) hmet htor hv0 hvn ξ
  have hK : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v)
      (fun s : ℝ => tcPrayFld (cov := cov) hmet q v τ η (τ - s)) s :=
    tcPrayFld_isJacobiAt_gam (cov := cov) hmet htor hvn hv0 τ η
  have hW := tc_wronskian_const (cov := cov) hmet htor hγ hne hJ hK 0 σ
  have hW0 : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v 0)
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (tcFwd (cov := cov) hmet q v ξ) 0)
        (tcPrayFld (cov := cov) hmet q v τ η (τ - 0))
      - tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v 0)
        (tcFwd (cov := cov) hmet q v ξ 0)
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v τ η (τ - s)) 0)
      = tcIn (M := M) (I := I) q ξ (tcPrayFld (cov := cov) hmet q v τ η τ) := by
    rw [tcFwd_zero, tcFwd_covAlong_zero (cov := cov) hmet htor hv0 ξ, tcIn_zero_left,
      sub_zero, sub_zero]
    exact tcIn_pt (X := tcGam (cov := cov) hmet q v 0) (Y := q)
      (by simp [tcGam, zero_smul]) (show E from ξ)
      (show E from tcPrayFld (cov := cov) hmet q v τ η τ)
  have hWσ : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (tcFwd (cov := cov) hmet q v ξ) σ)
        (tcPrayFld (cov := cov) hmet q v τ η (τ - σ))
      - tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v ξ σ)
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v τ η (τ - s)) σ)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
          (tcPrayFld (cov := cov) hmet q v τ η (τ - σ))
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M)
              (tcGam (cov := cov) hmet q v τ) z)
            (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
            (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)) := by
    rw [tcFwd_shape_all (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0
        (lt_trans hστ hτ) ξ hξ
        (tcPrayFld (cov := cov) hmet q v τ η (τ - σ))
        (tcPrayFld_orth (cov := cov) hmet htor hvn hv0 η hη (σ := σ)),
      tcIn_symm (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
        (Submission.JacobiGlobal.covAlong cov (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v τ η (τ - s)) σ),
      tcBwd_shape_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ η hη
        (X := tcFwd (cov := cov) hmet q v ξ σ)
        (tcFwd_orth (cov := cov) hmet htor ξ hξ (σ := σ))]
    rw [Work.Diff.C.rhess_symm (I := I) (M := M) (cov := cov) hmet htor
      (tc_sm_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hτ.le hτ0
        (by linarith) (by linarith))
      (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)) (tcFwd (cov := cov) hmet q v ξ σ)]
    ring
  rw [hWσ, hW0] at hW
  exact hW

/-! ## 7. The two-centre bilinear bounds

`𝔅(V,W) := Hess (rdist q)(γσ)(V,W) + Hess (rdist (γτ))(γσ)(V,W)` on `γ'(σ)^⊥`: the sum of the two
shape operators of `S(q,σ)` and `S(γτ,τ-σ)` at the intermediate point `γσ`.  `shape_polarized` at the
two centres gives `𝔅 = κ·g + O(δ)` with `κ = twoK σ τ`, `δ = twoD ε₁ σ τ`.

Similarly `ℭ = 𝔎(τ) - 𝔎(σ)` (with `𝔎(t) = -Hess (rdist (γt))(q)`) on `v^⊥` satisfies
`ℭ = λ·g + O(η)` with `λ = twoL σ τ`, `η = twoE ε₁ σ τ`. -/

/-- `twoE ε₁ σ τ ≥ 0`. -/
lemma twoE_nonneg {ε₁ σ τ : ℝ} (hε₁ : 0 ≤ ε₁) (hσ0 : 0 < σ) (hστ : σ < τ)
    (hτπ : τ < Real.pi) : 0 ≤ twoE ε₁ σ τ := by
  rw [twoE]
  refine mul_nonneg hε₁ (add_nonneg (one_div_nonneg.mpr ?_) (one_div_nonneg.mpr ?_))
  · exact (Real.sin_pos_of_pos_of_lt_pi hσ0 (by linarith)).le
  · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) hτπ).le

/-! **Cauchy–Schwarz in the `tcIn` notation**, with the square roots exposed (so that the norms
never have to be transported across points that are only *propositionally* equal). -/
lemma tcIn_le_sqrt_mul (X : M) (u a : TangentSpace I X) :
    tcIn (M := M) (I := I) X u a
      ≤ Real.sqrt (tcIn (M := M) (I := I) X a a)
        * Real.sqrt (tcIn (M := M) (I := I) X u u) := by
  rw [tcIn_eq, tcIn_eq, tcIn_eq]
  calc Inner.inner ℝ u a ≤ ‖u‖ * ‖a‖ := real_inner_le_norm u a
    _ = Real.sqrt (‖u‖ ^ 2) * Real.sqrt (‖a‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg a)]
    _ = Real.sqrt (tcIn (M := M) (I := I) X a a)
          * Real.sqrt (tcIn (M := M) (I := I) X u u) := by
        rw [norm_sq_eq_tcIn (M := M) (I := I) X a, norm_sq_eq_tcIn (M := M) (I := I) X u]
        ring

/-- **Transporting a norm across a (propositionally) equal base point.**  The norm of a tangent
vector is defined by the Riemannian-bundle instance *at its base point*, so two only
propositionally equal base points give two non-definitionally-equal norms. -/
lemma norm_pt_congr {X Y : M} (h : X = Y) (a : TangentSpace I X) :
    ‖a‖ = ‖(show TangentSpace I Y from a)‖ := by
  subst h
  rfl

/-- **The norm of `tcFwd` in the syntactic form of the target statement.**  `TwoCentreCoreProp`
writes the norm of the forward variation field with its base point in the un-reduced form
`GExp q (σ • (v + 0 • ξ))`. -/
lemma tcFwd_norm_eq (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (σ : ℝ) :
    ‖tcFwd (cov := cov) hmet q v ξ σ‖
      = ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0‖ := by
  have h := norm_pt_congr (X := tcGam (cov := cov) hmet q v σ)
    (Y := Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + (0 : ℝ) • ξ)))
    (by simp [tcGam]) (tcFwd (cov := cov) hmet q v ξ σ)
  exact h

/-- **The two-centre bound for the shape-sum bilinear form `𝔅`.** -/
lemma twoCentre_B_bound (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (V W : TangentSpace I (tcGam (cov := cov) hmet q v σ))
    (hV : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V
      (tcVel (cov := cov) hmet q v σ) = 0)
    (hW : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) W
      (tcVel (cov := cov) hmet q v σ) = 0) :
    |rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) V W
      + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
          (tcGam (cov := cov) hmet q v σ) V W
      - twoK σ τ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W|
    ≤ twoD ε₁ σ τ * ‖V‖ * ‖W‖ := by
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hσπ : σ < Real.pi := lt_trans hστ hτπ
  have hτ0 : 0 < τ := lt_trans hσ0 hστ
  have hd0 : 0 < τ - σ := sub_pos.mpr hστ
  have hdπ : τ - σ < Real.pi := by linarith
  have hσle : σ ≤ rho0 c := le_of_lt (lt_trans hστ hτ)
  have hrdσ : rdist (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ) = σ :=
    tc_rdist_gam (cov := cov) hmet htor hcut hvn hσ0 hσle
  have hrdd : rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
      (tcGam (cov := cov) hmet q v σ) = τ - σ :=
    tc_rdist_bwd (cov := cov) hmet htor hcut hvn hτ.le hτ0 hσ0.le hστ
  have hsmσ : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v σ) :=
    tc_sm_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hσle
  have hsmd : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v τ) z) (tcGam (cov := cov) hmet q v σ) :=
    tc_sm_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hτ.le hτ0 hσ0 hστ
  have hgσ : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v σ) = tcVel (cov := cov) hmet q v σ :=
    tc_grad_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hσle
  have hgd : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v τ) z) (tcGam (cov := cov) hmet q v σ)
      = -(tcVel (cov := cov) hmet q v σ) :=
    tc_grad_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ.le
  have hcosσ : fcos (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ) = Real.cos σ := by
    show Real.cos (rdist (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ)) = Real.cos σ
    rw [hrdσ]
  have hcosd : fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
      (tcGam (cov := cov) hmet q v σ) = Real.cos (τ - σ) := by
    show Real.cos (rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
      (tcGam (cov := cov) hmet q v σ)) = Real.cos (τ - σ)
    rw [hrdd]
  have hxσ : -1 + c < fcos (I := I) (M := M) q (tcGam (cov := cov) hmet q v σ) := by
    rw [hcosσ, ← cos_rho0 hc0 hc1]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hσ0.le (rho0_le_pi c) (lt_trans hστ hτ)
  have hxd : -1 + c < fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ)
      (tcGam (cov := cov) hmet q v σ) := by
    rw [hcosd, ← cos_rho0 hc0 hc1]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hd0.le (rho0_le_pi c) (by linarith [hτ, rho0_le_pi c])
  have hVσ : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
      (tcGam (cov := cov) hmet q v σ)) V = 0 := by
    have h1 : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
        (tcGam (cov := cov) hmet q v σ)
        = (-Real.sin σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := q) hsmσ, hrdσ, hgσ]
    have h2 : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
          (tcGam (cov := cov) hmet q v σ)) V = 0 := by
      rw [h1, tcIn_smul_left, tcIn_symm, hV, mul_zero]
    exact h2
  have hWσ : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
      (tcGam (cov := cov) hmet q v σ)) W = 0 := by
    have h1 : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
        (tcGam (cov := cov) hmet q v σ)
        = (-Real.sin σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := q) hsmσ, hrdσ, hgσ]
    have h2 : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
          (tcGam (cov := cov) hmet q v σ)) W = 0 := by
      rw [h1, tcIn_smul_left, tcIn_symm, hW, mul_zero]
    exact h2
  have hVd : Inner.inner ℝ (rgrad (I := I) (M := M)
      (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
      (tcGam (cov := cov) hmet q v σ)) V = 0 := by
    have h1 : rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
        (tcGam (cov := cov) hmet q v σ)
        = Real.sin (τ - σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := tcGam (cov := cov) hmet q v τ) hsmd, hrdd, hgd,
        smul_neg, neg_smul, neg_neg]
    have h2 : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
          (tcGam (cov := cov) hmet q v σ)) V = 0 := by
      rw [h1, tcIn_smul_left, tcIn_symm, hV, mul_zero]
    exact h2
  have hWd : Inner.inner ℝ (rgrad (I := I) (M := M)
      (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
      (tcGam (cov := cov) hmet q v σ)) W = 0 := by
    have h1 : rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
        (tcGam (cov := cov) hmet q v σ)
        = Real.sin (τ - σ) • tcVel (cov := cov) hmet q v σ := by
      rw [rgrad_fcos (I := I) (M := M) (q := tcGam (cov := cov) hmet q v τ) hsmd, hrdd, hgd,
        smul_neg, neg_smul, neg_neg]
    have h2 : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v τ))
          (tcGam (cov := cov) hmet q v σ)) W = 0 := by
      rw [h1, tcIn_smul_left, tcIn_symm, hW, mul_zero]
    exact h2
  have hb1 := shape_polarized (I := I) (M := M) (cov := cov) hmet htor (hHess q) hxσ hsmσ
    (by rw [hrdσ]; exact hσ0) (by rw [hrdσ]; exact hσπ) V W hVσ hWσ
  rw [hrdσ] at hb1
  have hb2 := shape_polarized (I := I) (M := M) (cov := cov) hmet htor
    (hHess (tcGam (cov := cov) hmet q v τ)) hxd hsmd
    (by rw [hrdd]; exact hd0) (by rw [hrdd]; exact hdπ) V W hVd hWd
  rw [hrdd] at hb2
  have hb1' : |rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v σ) V W
      - Real.cot σ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W|
      ≤ (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ := hb1
  have hb2' : |rhess cov (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v τ) z) (tcGam (cov := cov) hmet q v σ) V W
      - Real.cot (τ - σ) * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W|
      ≤ (ε₁ / Real.sin (τ - σ)) * ‖V‖ * ‖W‖ := hb2
  rw [twoK, twoD]
  have hsum : |(rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) V W
        - Real.cot σ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W)
      + (rhess cov (fun z : M ↦ rdist (I := I) (M := M)
            (tcGam (cov := cov) hmet q v τ) z) (tcGam (cov := cov) hmet q v σ) V W
        - Real.cot (τ - σ) * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W)|
      ≤ (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ + (ε₁ / Real.sin (τ - σ)) * ‖V‖ * ‖W‖ :=
    le_trans (abs_add_le _ _) (add_le_add hb1' hb2')
  have harg : (rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) V W
      + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
          (tcGam (cov := cov) hmet q v σ) V W)
      - (Real.cot σ + Real.cot (τ - σ)) * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W
      = (rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v σ) V W
          - Real.cot σ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W)
        + (rhess cov (fun z : M ↦ rdist (I := I) (M := M)
            (tcGam (cov := cov) hmet q v τ) z) (tcGam (cov := cov) hmet q v σ) V W
          - Real.cot (τ - σ) * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ) V W) := by
    ring
  rw [harg]
  refine le_trans hsum ?_
  have : (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ + (ε₁ / Real.sin (τ - σ)) * ‖V‖ * ‖W‖
      = ε₁ * (1 / Real.sin σ + 1 / Real.sin (τ - σ)) * ‖V‖ * ‖W‖ := by
    ring
  rw [this]

/-- **The two-centre bound for `ℭ = 𝔎(τ) - 𝔎(σ)`.** -/
lemma twoCentre_C_bound (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (V W : TangentSpace I q) (hV : tcIn (M := M) (I := I) q v V = 0)
    (hW : tcIn (M := M) (I := I) q v W = 0) :
    |tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ τ V) W
      - twoL σ τ * tcIn (M := M) (I := I) q V W|
    ≤ twoE ε₁ σ τ * ‖V‖ * ‖W‖ := by
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hσπ : σ < Real.pi := lt_trans hστ hτπ
  have hτ0 : 0 < τ := lt_trans hσ0 hστ
  have hshape : ∀ t : ℝ, 0 < t → t < rho0 c →
      |rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z) q V W
        - Real.cot t * Inner.inner ℝ V W|
      ≤ (ε₁ / Real.sin t) * ‖V‖ * ‖W‖ := by
    intro t ht0 htl
    have htπ : t < Real.pi := lt_of_lt_of_le htl (rho0_le_pi c)
    have hrd := rdist_gam_q (cov := cov) hmet htor hcut hvn ht0 (le_of_lt htl)
    have hcos : fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q = Real.cos t := by
      show Real.cos (rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q) = Real.cos t
      rw [hrd]
    have hx : -1 + c < fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t) q := by
      rw [hcos, ← cos_rho0 hc0 hc1]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi ht0.le (rho0_le_pi c) htl
    have hsm : CMDiffAt ∞
        (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z) q :=
      csm_rdist_of_le_rho hc0 hc1 hsmC (by rw [hrd]; exact ht0) (by rw [hrd]; exact le_of_lt htl)
    have hgf : rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q = Real.sin t • v :=
      rgrad_fcos_gam_at_q (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 ht0 htl
    have hV' : Inner.inner ℝ
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q) V
        = 0 := by
      rw [hgf, real_inner_smul_left, ← tcIn_eq (M := M) (I := I) q v V, hV, mul_zero]
    have hW' : Inner.inner ℝ
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) (tcGam (cov := cov) hmet q v t)) q) W
        = 0 := by
      rw [hgf, real_inner_smul_left, ← tcIn_eq (M := M) (I := I) q v W, hW, mul_zero]
    have h := shape_polarized (I := I) (M := M) (cov := cov) hmet htor
      (hHess (tcGam (cov := cov) hmet q v t)) hx hsm (by rw [hrd]; exact ht0)
      (by rw [hrd]; exact htπ) V W hV' hW'
    rwa [hrd] at h
  have h1 := hshape τ hτ0 hτ
  have h2 := hshape σ hσ0 (lt_trans hστ hτ)
  rw [tcC_spec, twoL, twoE]
  have h1' : |rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
        q V W - Real.cot τ * tcIn (M := M) (I := I) q V W|
      ≤ (ε₁ / Real.sin τ) * ‖V‖ * ‖W‖ := h1
  have h2' : |rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) z)
        q V W - Real.cot σ * tcIn (M := M) (I := I) q V W|
      ≤ (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ := h2
  have hsum : |(rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) z)
        q V W - Real.cot σ * tcIn (M := M) (I := I) q V W)
      - (rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
        q V W - Real.cot τ * tcIn (M := M) (I := I) q V W)|
      ≤ (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ + (ε₁ / Real.sin τ) * ‖V‖ * ‖W‖ :=
    le_trans (abs_sub _ _) (add_le_add h2' h1')
  have harg : (-rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
        q V W
      + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) z)
        q V W)
      - (Real.cot σ - Real.cot τ) * tcIn (M := M) (I := I) q V W
      = (rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) z)
          q V W - Real.cot σ * tcIn (M := M) (I := I) q V W)
        - (rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
          q V W - Real.cot τ * tcIn (M := M) (I := I) q V W) := by
    ring
  rw [harg]
  refine le_trans hsum ?_
  have : (ε₁ / Real.sin σ) * ‖V‖ * ‖W‖ + (ε₁ / Real.sin τ) * ‖V‖ * ‖W‖
      = ε₁ * (1 / Real.sin σ + 1 / Real.sin τ) * ‖V‖ * ‖W‖ := by
    ring
  rw [this]

/-- **`ℭ` is `λ`-close to the identity, in operator norm, on `v^⊥`.** -/
lemma tcC_op_close (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (V : TangentSpace I q) (hV : tcIn (M := M) (I := I) q v V = 0) :
    ‖tcC (cov := cov) hmet q v σ τ V - twoL σ τ • V‖ ≤ twoE ε₁ σ τ * ‖V‖ := by
  classical
  set U : TangentSpace I q := tcC (cov := cov) hmet q v σ τ V - twoL σ τ • V with hU
  have hUorth : tcIn (M := M) (I := I) q v (U : TangentSpace I q) = 0 := by
    have hc1' : tcIn (M := M) (I := I) q v (tcC (cov := cov) hmet q v σ τ V) = 0 := by
      rw [tcIn_symm]
      exact tcC_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hστ hτ V
    rw [hU, tcIn_sub_right, hc1', tcIn_smul_right, hV, mul_zero, sub_zero]
  rcases eq_or_ne U 0 with h0 | h0
  · rw [h0, norm_zero]
    exact mul_nonneg (twoE_nonneg hε₁ hσ0 hστ (lt_of_lt_of_le hτ (rho0_le_pi c)))
      (norm_nonneg V)
  · set W : TangentSpace I q := (‖U‖)⁻¹ • U with hW
    have hUn : (0 : ℝ) < ‖U‖ := norm_pos_iff.mpr h0
    have hUn' : ‖U‖ ≠ 0 := ne_of_gt hUn
    have hWnorm : ‖W‖ = 1 := by
      rw [hW, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg U)), inv_mul_cancel₀ hUn']
    have hWorth : tcIn (M := M) (I := I) q v W = 0 := by
      rw [hW, tcIn_smul_right, hUorth, mul_zero]
    have hkey := twoCentre_C_bound (cov := cov) hmet htor hc0 hc1 hcut hsmC hHess
      hvn hv0 hσ0 hστ hτ V W hV hWorth
    have hUW : tcIn (M := M) (I := I) q (U : TangentSpace I q) W = ‖U‖ := by
      rw [hW, tcIn_smul_right, ← norm_sq_eq_tcIn (M := M) (I := I) q U, sq,
        ← mul_assoc, inv_mul_cancel₀ hUn', one_mul]
    have hexp : tcIn (M := M) (I := I) q (U : TangentSpace I q) W
        = tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ τ V) W
          - twoL σ τ * tcIn (M := M) (I := I) q V W := by
      rw [hU, tcIn_sub_left, tcIn_smul_left]
    have hUb : |tcIn (M := M) (I := I) q (U : TangentSpace I q) W| ≤ twoE ε₁ σ τ * ‖V‖ := by
      rw [hexp]
      simpa only [hWnorm, mul_one] using hkey
    rw [hUW, abs_of_nonneg (norm_nonneg U)] at hUb
    exact hUb

/-! ## 8. The Wronskian identity with the backward field identified -/

/-- **The two-centre identity, with the backward field written through `ℭ`.**

For the backward field `J_η` vanishing at `γτ` with tangential initial derivative `η`, the Wronskian
of `Tξ = tcFwd q v ξ σ` with `J_η(σ)` is `⟪ξ, J_η(0)⟫`; and `tcBackwardID` identifies
`J_η(σ) = T(ℭ (J_η(0)))`. -/
lemma tcB_backward (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v τ))
    (hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v τ) η
      (-(tcVel (cov := cov) hmet q v τ)) = 0)
    (ξ : TangentSpace I q) (hξ : tcIn (M := M) (I := I) q v ξ = 0) :
    rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
        (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ
          (tcPrayFld (cov := cov) hmet q v τ η τ)) σ)
      + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v ξ σ)
          (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ
            (tcPrayFld (cov := cov) hmet q v τ η τ)) σ)
      = tcIn (M := M) (I := I) q ξ (tcPrayFld (cov := cov) hmet q v τ η τ) := by
  rw [← tcBackwardID (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ η hη]
  exact tcWronskian_twoCentre (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ
    ξ hξ η hη

/-! ## 9. The diagonal two-centre bound -/

/-- **The sharp diagonal two-centre bound.**  `(κ-δ)(λ-η)‖Tξ‖² ≤ ‖ξ‖²` for `ξ ⊥ v`, where
`Tξ = tcFwd q v ξ σ`. -/
lemma tcFwd_axis_bound (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁) (hnum2 : 4 * ε₁ * Real.pi < c)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    (hEL : twoE ε₁ σ τ < twoL σ τ)
    (ξ : TangentSpace I q) (hξ : tcIn (M := M) (I := I) q v ξ = 0) :
    (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ)
        * ‖tcFwd (cov := cov) hmet q v ξ σ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  classical
  have hKD : 0 < twoK σ τ - twoD ε₁ σ τ := twoK_sub_twoD_pos hc0 hc1 hε₁ hnum2 hσ0 hστ hτ
  have hELp : 0 < twoL σ τ - twoE ε₁ σ τ := sub_pos.mpr hEL
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hd0 : 0 < τ - σ := sub_pos.mpr hστ
  have hdt : τ - σ < τ := by linarith
  have hunit : ∀ u : TangentSpace I q, tcIn (M := M) (I := I) q v u = 0 → ‖u‖ = 1 →
      (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ)
        * ‖tcFwd (cov := cov) hmet q v u σ‖ ^ 2 ≤ 1 := by
    intro u hu hu1
    have hXu : tcIn (M := M) (I := I) (tcPray (cov := cov) hmet q v τ (τ - σ))
        (tcFwd (cov := cov) hmet q v u σ)
        (Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v τ)
          (τ - σ)) = 0 := by
      have hpt : tcPray (cov := cov) hmet q v τ (τ - σ) = tcGam (cov := cov) hmet q v σ :=
        tc_rev_point (cov := cov) hmet hvn τ σ
      have hvel : Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v τ)
          (τ - σ) = -(tcVel (cov := cov) hmet q v σ) :=
        tc_rev_vel (cov := cov) hmet hvn hv0 τ σ
      have hstep : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
          (tcFwd (cov := cov) hmet q v u σ) (tcVel (cov := cov) hmet q v σ) = 0 :=
        tcFwd_orth (cov := cov) hmet htor u hu (σ := σ)
      rw [hvel]
      rw [tcIn_pt (X := tcPray (cov := cov) hmet q v τ (τ - σ))
        (Y := tcGam (cov := cov) hmet q v σ) hpt
        (show E from tcFwd (cov := cov) hmet q v u σ)
        (show E from -(tcVel (cov := cov) hmet q v σ))]
      rw [show (-(tcVel (cov := cov) hmet q v σ))
          = (-1 : ℝ) • (tcVel (cov := cov) hmet q v σ) from (neg_one_smul ℝ _).symm,
        tcIn_smul_right]
      rw [hstep, mul_zero]
    obtain ⟨η, hη, hval⟩ := tcPrayFld_surj (cov := cov) hmet htor hcut hvn hv0 hd0 hdt hτ hXu
    have hval' : (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
        : TangentSpace I (tcGam (cov := cov) hmet q v σ)) = tcFwd (cov := cov) hmet q v u σ := hval
    have hback : (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
        : TangentSpace I (tcGam (cov := cov) hmet q v σ))
        = tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ
            (tcPrayFld (cov := cov) hmet q v τ η τ)) σ :=
      tcBackwardID (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ η hη
    have hTeq : tcFwd (cov := cov) hmet q v u σ
        = tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ
            (tcPrayFld (cov := cov) hmet q v τ η τ)) σ := hval'.symm.trans hback
    have hczorth : tcIn (M := M) (I := I) q v (tcC (cov := cov) hmet q v σ τ
        (tcPrayFld (cov := cov) hmet q v τ η τ)) = 0 := by
      rw [tcIn_symm]
      exact tcC_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hστ hτ _
    have hzorth : tcIn (M := M) (I := I) q v (tcPrayFld (cov := cov) hmet q v τ η τ) = 0 := by
      have hg := tcPrayFld_gauss (cov := cov) (q := q) (v := v) hmet htor τ η τ
      rw [hη, mul_zero] at hg
      have hpt : tcPray (cov := cov) hmet q v τ τ = q := by
        have h := tc_rev_point (cov := cov) hmet hvn τ 0
        rw [sub_zero] at h
        show Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v τ)
          (τ • (-(tcVel (cov := cov) hmet q v τ))) = q
        rw [h]
        simp [tcGam, zero_smul]
      rw [tcIn_pt (X := tcPray (cov := cov) hmet q v τ τ) (Y := q) hpt
        (show E from tcPrayFld (cov := cov) hmet q v τ η τ)
        (show E from Submission.Geodesic.curveVelocity (I := I)
          (tcPray (cov := cov) hmet q v τ) τ)] at hg
      have hvelrev : Submission.Geodesic.curveVelocity (I := I)
          (tcPray (cov := cov) hmet q v τ) τ = -v := by
        have h := tc_rev_vel (cov := cov) hmet hvn hv0 τ 0
        rw [sub_zero, tcVel_zero (cov := cov) hmet hv0] at h
        exact h
      rw [hvelrev, show (-v : TangentSpace I q) = (-1 : ℝ) • v from (neg_one_smul ℝ v).symm,
        tcIn_smul_right] at hg
      have h1 : tcIn (M := M) (I := I) q (tcPrayFld (cov := cov) hmet q v τ η τ) v = 0 := by
        linarith [hg]
      rwa [tcIn_symm] at h1
    have hWu : rhess cov (fun y : M ↦ rdist (I := I) (M := M) q y)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v u σ)
          (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
            : TangentSpace I (tcGam (cov := cov) hmet q v σ))
        + rhess cov (fun y : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) y)
            (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v u σ)
            (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
              : TangentSpace I (tcGam (cov := cov) hmet q v σ))
        = tcIn (M := M) (I := I) q u (tcPrayFld (cov := cov) hmet q v τ η τ) :=
      tcWronskian_twoCentre (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ u hu η hη
    have hWc : rhess cov (fun y : M ↦ rdist (I := I) (M := M) q y)
          (tcGam (cov := cov) hmet q v σ)
          (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ
            (tcPrayFld (cov := cov) hmet q v τ η τ)) σ)
          (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
            : TangentSpace I (tcGam (cov := cov) hmet q v σ))
        + rhess cov (fun y : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) y)
            (tcGam (cov := cov) hmet q v σ)
            (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ
              (tcPrayFld (cov := cov) hmet q v τ η τ)) σ)
            (tcPrayFld (cov := cov) hmet q v τ η (τ - σ)
              : TangentSpace I (tcGam (cov := cov) hmet q v σ))
        = tcIn (M := M) (I := I) q (tcC (cov := cov) hmet q v σ τ
            (tcPrayFld (cov := cov) hmet q v τ η τ)) (tcPrayFld (cov := cov) hmet q v τ η τ) :=
      tcWronskian_twoCentre (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ
        (tcC (cov := cov) hmet q v σ τ (tcPrayFld (cov := cov) hmet q v τ η τ)) hczorth η hη
    rw [hval'] at hWu
    rw [hval', hTeq] at hWc
    simp only [tcC] at hTeq hWc
    have hdiag : (twoK σ τ - twoD ε₁ σ τ) * ‖tcFwd (cov := cov) hmet q v u σ‖ ^ 2
        ≤ tcIn (M := M) (I := I) q u (tcPrayFld (cov := cov) hmet q v τ η τ) := by
      rw [← hWu]
      have hB := twoCentre_B_bound (cov := cov) hmet htor hc0 hc1 hcut hsmC hHess hvn hv0
        hσ0 hστ hτ (tcFwd (cov := cov) hmet q v u σ) (tcFwd (cov := cov) hmet q v u σ)
        (tcFwd_orth (cov := cov) hmet htor u hu (σ := σ))
        (tcFwd_orth (cov := cov) hmet htor u hu (σ := σ))
      rw [abs_le] at hB
      have hB2 := hB.1
      rw [← norm_sq_eq_tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v u σ)] at hB2
      nlinarith [hB2]
    have hpq : tcIn (M := M) (I := I) q u (tcPrayFld (cov := cov) hmet q v τ η τ)
        ≤ Real.sqrt (tcIn (M := M) (I := I) q (tcPrayFld (cov := cov) hmet q v τ η τ)
            (tcPrayFld (cov := cov) hmet q v τ η τ)) := by
      have h := tcIn_le_sqrt_mul (M := M) (I := I) q u (tcPrayFld (cov := cov) hmet q v τ η τ)
      have hu2 : tcIn (M := M) (I := I) q u u = 1 := by
        rw [tcIn_eq, real_inner_self_eq_norm_sq, hu1]
        norm_num
      rw [hu2, Real.sqrt_one, mul_one] at h
      exact h
    have hcz : (twoL σ τ - twoE ε₁ σ τ)
        * tcIn (M := M) (I := I) q (tcPrayFld (cov := cov) hmet q v τ η τ)
          (tcPrayFld (cov := cov) hmet q v τ η τ)
        ≤ tcIn (M := M) (I := I) q u (tcPrayFld (cov := cov) hmet q v τ η τ) := by
      have hq := tcC_quadratic (cov := cov) hmet htor hc0 hc1 hε₁ hcut hsmC hHess hvn hv0
        hσ0 hστ hτ (tcPrayFld (cov := cov) hmet q v τ η τ) hzorth
      rw [← hWc, ← hTeq, hWu] at hq
      exact hq
    set s : ℝ := Real.sqrt (tcIn (M := M) (I := I) q (tcPrayFld (cov := cov) hmet q v τ η τ)
      (tcPrayFld (cov := cov) hmet q v τ η τ)) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = tcIn (M := M) (I := I) q (tcPrayFld (cov := cov) hmet q v τ η τ)
        (tcPrayFld (cov := cov) hmet q v τ η τ) :=
      Real.sq_sqrt (tcIn_nonneg (M := M) (I := I) q _)
    have h2' : tcIn (M := M) (I := I) q u (tcPrayFld (cov := cov) hmet q v τ η τ) ≤ s :=
      le_trans hpq (le_of_eq hs)
    by_cases hs3 : s = 0
    · have hp0 : tcIn (M := M) (I := I) q u (tcPrayFld (cov := cov) hmet q v τ η τ) ≤ 0 := by
        rw [hs3] at h2'
        exact h2'
      have hT0 : ‖tcFwd (cov := cov) hmet q v u σ‖ = 0 := by
        have hle : (twoK σ τ - twoD ε₁ σ τ) * ‖tcFwd (cov := cov) hmet q v u σ‖ ^ 2 ≤ 0 :=
          le_trans hdiag hp0
        have hnn : 0 ≤ (twoK σ τ - twoD ε₁ σ τ) * ‖tcFwd (cov := cov) hmet q v u σ‖ ^ 2 :=
          mul_nonneg hKD.le (sq_nonneg _)
        have hsq : ‖tcFwd (cov := cov) hmet q v u σ‖ ^ 2 = 0 := by
          rcases mul_eq_zero.mp (le_antisymm hle hnn) with h | h
          · exact absurd h (ne_of_gt hKD)
          · exact h
        rw [sq] at hsq
        exact mul_self_eq_zero.mp hsq
      rw [hT0]
      norm_num
    · have hs3' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs3)
      have h4 : (twoL σ τ - twoE ε₁ σ τ) * s ≤ 1 := by
        have h5 : (twoL σ τ - twoE ε₁ σ τ) * s * s ≤ 1 * s := by
          rw [one_mul]
          nlinarith [hcz, h2', hs2]
        exact le_of_mul_le_mul_right h5 hs3'
      have h6 : (twoK σ τ - twoD ε₁ σ τ) * ‖tcFwd (cov := cov) hmet q v u σ‖ ^ 2 ≤ s :=
        le_trans hdiag h2'
      have h7 : (twoK σ τ - twoD ε₁ σ τ) * ‖tcFwd (cov := cov) hmet q v u σ‖ ^ 2
          ≤ 1 / (twoL σ τ - twoE ε₁ σ τ) := by
        rw [le_div_iff₀ hELp]
        nlinarith [h6, h4]
      rw [le_div_iff₀ hELp] at h7
      nlinarith [h7]
  by_cases hξ0 : ξ = 0
  · rw [hξ0, tcFwd_zero', norm_zero, norm_zero]
    nlinarith [hKD, hELp, sq_nonneg (‖tcFwd (cov := cov) hmet q v ξ σ‖)]
  · have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
    have hu1 : ‖(1 / ‖ξ‖) • ξ‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), one_div,
        inv_mul_cancel₀ (ne_of_gt hξn)]
    have huorth : tcIn (M := M) (I := I) q v ((1 / ‖ξ‖) • ξ) = 0 := by
      rw [tcIn_smul_right, hξ, mul_zero]
    have hkey := hunit ((1 / ‖ξ‖) • ξ) huorth hu1
    have hscale : tcFwd (cov := cov) hmet q v ξ σ
        = ‖ξ‖ • tcFwd (cov := cov) hmet q v ((1 / ‖ξ‖) • ξ) σ := by
      rw [tcFwd_smul, smul_smul, mul_one_div, div_self (ne_of_gt hξn), one_smul]
    rw [hscale, norm_smul, Real.norm_of_nonneg hξn.le, mul_pow]
    nlinarith [hkey, hKD, hELp, sq_nonneg ‖ξ‖,
      sq_nonneg ‖tcFwd (cov := cov) hmet q v ((1 / ‖ξ‖) • ξ) σ‖]

/-! ## 10. The two monotone consequences -/

/-- **Condition (4a) of the target**: the upper bound for `1` in terms of `y_w = ‖T w‖`. -/
lemma twoCentre_lower (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ ξ : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 →
      ‖tcFwd (cov := cov) hmet q v ξ σ‖ ≤ N * ‖ξ‖)
    (w : TangentSpace I q) (hw : tcIn (M := M) (I := I) q v w = 0) (hw1 : ‖w‖ = 1) :
    1 ≤ (twoK σ τ + twoD ε₁ σ τ) *
      (twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ ^ 2
        + twoE ε₁ σ τ * N * ‖tcFwd (cov := cov) hmet q v w σ‖) := by
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hLpos : 0 < twoL σ τ := twoL_pos hσ0 hστ hτπ
  have hδnn : 0 ≤ twoD ε₁ σ τ := by
    rw [twoD]
    exact mul_nonneg hε₁ (add_nonneg (one_div_nonneg.mpr (Real.sin_pos_of_pos_of_lt_pi hσ0
      (by linarith)).le) (one_div_nonneg.mpr (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith)).le))
  have hτ0 : 0 < τ := lt_trans hσ0 hστ
  obtain ⟨η, hη, hval⟩ := tcPrayFld_surj_base (cov := cov) hmet htor hcut hvn hv0 hτ0 hτ hw
  have hval' : (tcPrayFld (cov := cov) hmet q v τ η τ : TangentSpace I q) = w := hval
  have hwr := tcB_backward (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hσ0 hστ hτ η hη w hw
  rw [hval'] at hwr
  have hBw : rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v w σ)
        (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ)
      + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v τ) z)
          (tcGam (cov := cov) hmet q v σ) (tcFwd (cov := cov) hmet q v w σ)
          (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ) = 1 := by
    rw [← norm_sq_eq_tcIn (M := M) (I := I) q w, hw1] at hwr
    simpa using hwr
  have hB := twoCentre_B_bound (cov := cov) hmet htor hc0 hc1 hcut hsmC hHess hvn hv0 hσ0 hστ hτ
    (tcFwd (cov := cov) hmet q v w σ)
    (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ)
    (tcFwd_orth (cov := cov) hmet htor w hw (σ := σ))
    (tcFwd_orth (cov := cov) hmet htor (tcC (cov := cov) hmet q v σ τ w)
      (by rw [tcIn_symm]
          exact tcC_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hστ hτ w) (σ := σ))
  rw [abs_le] at hB
  have hclose := tcC_op_close (cov := cov) hmet htor hc0 hc1 hε₁ hcut hsmC hHess hvn hv0
    hσ0 hστ hτ w hw
  rw [hw1, mul_one] at hclose
  have hΔorth : tcIn (M := M) (I := I) q v
      (tcC (cov := cov) hmet q v σ τ w - twoL σ τ • w) = 0 := by
    have hcw : tcIn (M := M) (I := I) q v (tcC (cov := cov) hmet q v σ τ w) = 0 := by
      rw [tcIn_symm]
      exact tcC_orth_v (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hσ0 hστ hτ w
    rw [tcIn_sub_right, hcw, tcIn_smul_right, hw, mul_zero, sub_zero]
  have hTΔ : ‖tcFwd (cov := cov) hmet q v
      (tcC (cov := cov) hmet q v σ τ w - twoL σ τ • w) σ‖ ≤ N * twoE ε₁ σ τ :=
    le_trans (hN _ hΔorth) (mul_le_mul_of_nonneg_left hclose hN0)
  have hlin : tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ
      = twoL σ τ • tcFwd (cov := cov) hmet q v w σ
        + tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w - twoL σ τ • w) σ := by
    rw [← tcFwd_smul, ← tcFwd_add]
    congr 1
    abel
  have hy : ‖tcFwd (cov := cov) hmet q v w σ‖ ≤ N := by
    have h := hN w hw
    rwa [hw1, mul_one] at h
  have hj : ‖tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ‖
      ≤ twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ + N * twoE ε₁ σ τ := by
    rw [hlin]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ hTΔ)
    rw [norm_smul, Real.norm_of_nonneg hLpos.le]
  have hp : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v w σ)
        (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ)
      ≤ twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ ^ 2
        + twoE ε₁ σ τ * N * ‖tcFwd (cov := cov) hmet q v w σ‖ := by
    have h2 : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v w σ)
        (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w - twoL σ τ • w) σ)
        ≤ ‖tcFwd (cov := cov) hmet q v w σ‖ * (N * twoE ε₁ σ τ) := by
      rw [tcIn_eq]
      exact le_trans (real_inner_le_norm (tcFwd (cov := cov) hmet q v w σ)
          (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w - twoL σ τ • w) σ))
        (mul_le_mul_of_nonneg_left hTΔ (norm_nonneg _))
    have h1 : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v w σ) (tcFwd (cov := cov) hmet q v w σ)
        = ‖tcFwd (cov := cov) hmet q v w σ‖ ^ 2 := (norm_sq_eq_tcIn _ _).symm
    rw [hlin, tcIn_add_right, tcIn_smul_right, h1]
    nlinarith [h2]
  have hy0 : 0 ≤ ‖tcFwd (cov := cov) hmet q v w σ‖ := norm_nonneg _
  have h1 : 1 ≤ twoK σ τ * (twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ ^ 2
      + twoE ε₁ σ τ * N * ‖tcFwd (cov := cov) hmet q v w σ‖)
      + twoD ε₁ σ τ * (‖tcFwd (cov := cov) hmet q v w σ‖
        * (twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ + N * twoE ε₁ σ τ)) := by
    have h3 := hB.2
    rw [hBw] at h3
    have h4 : twoK σ τ * tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v σ)
        (tcFwd (cov := cov) hmet q v w σ)
        (tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ)
        ≤ twoK σ τ * (twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ ^ 2
          + twoE ε₁ σ τ * N * ‖tcFwd (cov := cov) hmet q v w σ‖) :=
      mul_le_mul_of_nonneg_left hp (le_of_lt (twoK_pos hσ0 hστ hτπ))
    have h5 : twoD ε₁ σ τ * (‖tcFwd (cov := cov) hmet q v w σ‖
        * ‖tcFwd (cov := cov) hmet q v (tcC (cov := cov) hmet q v σ τ w) σ‖)
        ≤ twoD ε₁ σ τ * (‖tcFwd (cov := cov) hmet q v w σ‖
          * (twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ + N * twoE ε₁ σ τ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hj hy0) hδnn
    linarith [h3, h4, h5]
  refine le_trans h1 (le_of_eq ?_)
  ring

/-- **Condition (4b) of the target**: the lower bound for `1`.  It uses only `y_w ≤ N` and the
diagonal bound `(κ-δ)(λ-η)N² ≤ 1`. -/
lemma twoCentre_upper (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c ε₁ : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁) (hnum2 : 4 * ε₁ * Real.pi < c)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M,
      HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hστ : σ < τ) (hτ : τ < rho0 c)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ ξ : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 →
      ‖tcFwd (cov := cov) hmet q v ξ σ‖ ≤ N * ‖ξ‖)
    (h3 : (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) * N ^ 2 ≤ 1)
    (w : TangentSpace I q) (hw : tcIn (M := M) (I := I) q v w = 0) (hw1 : ‖w‖ = 1) :
    (twoK σ τ - twoD ε₁ σ τ) *
      (twoL σ τ * ‖tcFwd (cov := cov) hmet q v w σ‖ ^ 2
        - twoE ε₁ σ τ * N * ‖tcFwd (cov := cov) hmet q v w σ‖) ≤ 1 := by
  have hKD : 0 ≤ twoK σ τ - twoD ε₁ σ τ :=
    (twoK_sub_twoD_pos hc0 hc1 hε₁ hnum2 hσ0 hστ hτ).le
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hLpos : 0 < twoL σ τ := twoL_pos hσ0 hστ hτπ
  have hy : ‖tcFwd (cov := cov) hmet q v w σ‖ ≤ N := by
    have h := hN w hw
    rwa [hw1, mul_one] at h
  have hy0 : 0 ≤ ‖tcFwd (cov := cov) hmet q v w σ‖ := norm_nonneg _
  set y : ℝ := ‖tcFwd (cov := cov) hmet q v w σ‖ with hydef
  by_cases hf : twoL σ τ * y ^ 2 - twoE ε₁ σ τ * N * y ≤ 0
  · calc (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ * y ^ 2 - twoE ε₁ σ τ * N * y)
        ≤ (twoK σ τ - twoD ε₁ σ τ) * 0 := mul_le_mul_of_nonneg_left hf hKD
      _ = 0 := mul_zero _
      _ ≤ 1 := by norm_num
  · have hf' : 0 < twoL σ τ * y ^ 2 - twoE ε₁ σ τ * N * y := not_le.mp hf
    have h1c : twoL σ τ * y - twoE ε₁ σ τ * N ≤ twoL σ τ * N - twoE ε₁ σ τ * N := by
      nlinarith [hy, hLpos]
    have h2c : 0 ≤ twoL σ τ * y - twoE ε₁ σ τ * N := by nlinarith [hf', hy0]
    have hfy0 : y * (twoL σ τ * y - twoE ε₁ σ τ * N) ≤ N * (twoL σ τ * N - twoE ε₁ σ τ * N) :=
      mul_le_mul hy h1c h2c hN0
    have hfy : twoL σ τ * y ^ 2 - twoE ε₁ σ τ * N * y ≤ (twoL σ τ - twoE ε₁ σ τ) * N ^ 2 := by
      nlinarith [hfy0]
    calc (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ * y ^ 2 - twoE ε₁ σ τ * N * y)
        ≤ (twoK σ τ - twoD ε₁ σ τ) * ((twoL σ τ - twoE ε₁ σ τ) * N ^ 2) :=
          mul_le_mul_of_nonneg_left hfy hKD
      _ = (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) * N ^ 2 := by ring
      _ ≤ 1 := h3

end Work.Diff.C.geoCrux.Port

/-!
# STATUS

`Work.Diff.C.geoCrux.Port.TwoCentreCoreProp` is proved by the case split on `λ ≤ η`:
for `η < λ` the optimal `N = ((κ-δ)(λ-η))^{-1/2}` works (condition (1) is `tcFwd_axis_bound`,
(3) is an identity, (4a)/(4b) are `twoCentre_lower`/`twoCentre_upper`), and for `λ ≤ η` the bound
`N = ‖d(GExp q)(σ v)‖ · σ` works for every `N` (condition (3) is vacuous).
-/

namespace Work.Diff.C.geoCrux.Port

theorem twoCentreCore : Work.Diff.C.geoCrux.Port.TwoCentreCoreProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBd iNt iCS iPC cov iCov
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv σ τ hσ hστ hτ2 hτ
  classical
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right] at hv
    exact absurd hv (by norm_num)
  have hvn : ‖v‖ = 1 := by
    have h2 : ‖v‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hv
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  have hτπ : τ < Real.pi := lt_of_lt_of_le hτ (rho0_le_pi c)
  have hκpos : 0 < twoK σ τ := twoK_pos hσ hστ hτπ
  have hLpos : 0 < twoL σ τ := twoL_pos hσ hστ hτπ
  have hKD : 0 < twoK σ τ - twoD ε₁ σ τ := twoK_sub_twoD_pos hc hc1 hε₁ hnum2 hσ hστ hτ
  have hone : ∀ {x : TangentSpace I q}, Inner.inner ℝ x x = 1 → ‖x‖ = 1 := by
    intro x hx
    have h2 : ‖x‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hx
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]
  by_cases hcase : twoE ε₁ σ τ < twoL σ τ
  · have hA : 0 < (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) :=
      mul_pos hKD (sub_pos.mpr hcase)
    set N : ℝ := Real.sqrt (1 / ((twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ))) with hNdef
    have hN0 : 0 ≤ N := Real.sqrt_nonneg _
    have hNsq : N ^ 2 = 1 / ((twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ)) :=
      Real.sq_sqrt (div_nonneg zero_le_one hA.le)
    have hN : ∀ ξ : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 →
        ‖tcFwd (cov := cov) hmet q v ξ σ‖ ≤ N * ‖ξ‖ := by
      intro ξ hξ
      have hax := tcFwd_axis_bound (cov := cov) hmet htor hc hc1 hε₁ hnum2 hcut hsmC hHess
        hvn hv0 hσ hστ hτ hcase ξ hξ
      have h2 : ‖tcFwd (cov := cov) hmet q v ξ σ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * N ^ 2 := by
        rw [hNsq, mul_one_div, le_div_iff₀ hA]
        nlinarith [hax]
      calc ‖tcFwd (cov := cov) hmet q v ξ σ‖
          = Real.sqrt (‖tcFwd (cov := cov) hmet q v ξ σ‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (‖ξ‖ ^ 2 * N ^ 2) := Real.sqrt_le_sqrt h2
        _ = ‖ξ‖ * N := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hN0]
        _ = N * ‖ξ‖ := by ring
    have h3N : (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) * N ^ 2 ≤ 1 := by
      rw [hNsq, mul_one_div, div_self (ne_of_gt hA)]
    have hNraw : ∀ ξ : TangentSpace I q, Inner.inner ℝ v ξ = 0 →
        ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0‖
          ≤ N * ‖ξ‖ := by
      intro ξ hξ
      have h := hN ξ hξ
      rwa [tcFwd_norm_eq (cov := cov) hmet q v ξ σ] at h
    refine ⟨N, hN0, hNraw, hκpos, hLpos, h3N, ?_⟩
    intro w hw hw1
    have hl := twoCentre_lower (cov := cov) hmet htor hc hc1 hε₁ hcut hsmC hHess hvn hv0
      hσ hστ hτ hN0 hN w hw (hone hw1)
    have hu := twoCentre_upper (cov := cov) hmet htor hc hc1 hε₁ hnum2 hcut hsmC hHess hvn hv0
      hσ hστ hτ hN0 hN h3N w hw (hone hw1)
    rw [tcFwd_norm_eq (cov := cov) hmet q v w σ] at hl hu
    exact ⟨hl, hu⟩
  · push_neg at hcase
    set L : TangentSpace I q →L[ℝ] TangentSpace I (tcGam (cov := cov) hmet q v σ) :=
      mfderiv 𝓘(ℝ, E) I (fun z : E ↦ Submission.GlobalExp.GExp (cov := cov) hmet q z) (σ • v)
      with hLdef
    have hN0 : 0 ≤ ‖L‖ * σ := mul_nonneg (norm_nonneg L) hσ.le
    have hN : ∀ ξ : TangentSpace I q, tcIn (M := M) (I := I) q v ξ = 0 →
        ‖tcFwd (cov := cov) hmet q v ξ σ‖ ≤ (‖L‖ * σ) * ‖ξ‖ := by
      intro ξ _
      have h1 : tcFwd (cov := cov) hmet q v ξ σ = L (σ • ξ) := by
        rw [tcFwd_eq_mfderiv]
        rfl
      rw [h1]
      calc ‖L (σ • ξ)‖ ≤ ‖L‖ * ‖σ • ξ‖ := L.le_opNorm _
        _ = ‖L‖ * (σ * ‖ξ‖) := by rw [norm_smul, Real.norm_of_nonneg hσ.le]
        _ = (‖L‖ * σ) * ‖ξ‖ := by ring
    have h3N : (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) * (‖L‖ * σ) ^ 2 ≤ 1 := by
      have h1 : (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hKD.le (sub_nonpos.mpr hcase)
      have h2 : 0 ≤ (‖L‖ * σ) ^ 2 := sq_nonneg _
      nlinarith [h1, h2]
    have hNraw : ∀ ξ : TangentSpace I q, Inner.inner ℝ v ξ = 0 →
        ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0‖
          ≤ (‖L‖ * σ) * ‖ξ‖ := by
      intro ξ hξ
      have h := hN ξ hξ
      rwa [tcFwd_norm_eq (cov := cov) hmet q v ξ σ] at h
    refine ⟨‖L‖ * σ, hN0, hNraw, hκpos, hLpos, h3N, ?_⟩
    intro w hw hw1
    have hl := twoCentre_lower (cov := cov) hmet htor hc hc1 hε₁ hcut hsmC hHess hvn hv0
      hσ hστ hτ hN0 hN w hw (hone hw1)
    have hu := twoCentre_upper (cov := cov) hmet htor hc hc1 hε₁ hnum2 hcut hsmC hHess hvn hv0
      hσ hστ hτ hN0 hN h3N w hw (hone hw1)
    rw [tcFwd_norm_eq (cov := cov) hmet q v w σ] at hl hu
    exact ⟨hl, hu⟩

end Work.Diff.C.geoCrux.Port
