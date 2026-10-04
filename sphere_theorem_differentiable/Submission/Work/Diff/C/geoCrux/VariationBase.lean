import Mathlib
import Submission.Work.Diff.C.geoCrux.CoreStmts
import Submission.Work.Diff.C.geoCrux.TwoCentre.AuxProps
import Submission.Work.Diff.C.geoCrux.TwoCentre.jacobi_uniq
import Submission.Work.Diff.C.hess_lower_v2
import Submission.Work.Diff.C.rgrad_fcos_eikonal

set_option backward.isDefEq.respectTransparency.types false

/-!
# The two-centre core: `Work.Diff.C.geoCrux.TwoCentreCoreProp`

This file proves the two-centre inequality `Work.Diff.C.geoCrux.TwoCentreCoreProp`
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
    exact Work.Diff.C.geoCrux.TwoCentre.jacobi_uniq (cov := cov) htor hγ hne hJK
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

end Work.Diff.C.geoCrux.variation
