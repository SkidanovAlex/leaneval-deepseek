import Mathlib

/-!
# A smooth perturbation family of `ℝ⁴` by invertible operators, jointly surjective

The construction of the family `A : ℝ^{48} → Fin 3 → (ℝ⁴ ≃L ℝ⁴)` requested by the
`L5` chain (see `L5_CHAIN_STATUS.md` §6).

* `eLin : ℝ^{48} ≃ₗ (Fin 3 → (ℝ⁴ →L ℝ⁴))` is any linear isomorphism, which exists because
  `48 = 3 * 16 = 3 * dim (ℝ⁴ →L ℝ⁴)`; `T0 k` is its `k`-th component, rescaled to `T k` with
  `‖T k‖ ≤ 16` (`T_norm_le`).
* the design condition is met because for a non-zero `v` the evaluation `L ↦ L v` is surjective
  (`exists_dual_vector` produces `ℓ` with `ℓ v = 1`, and `ℓ.smulRight y` maps `v` to `y`), so
  `h ↦ ((T k h) (v k))_k` is surjective for *every* tuple of non-zero `v k` (`exists_apply_eq`,
  `exists_apply_eq'`).
* the perturbation `bmp p • T k p` is controlled by a smooth bump `bmp` (`ContDiffBump` with
  `rIn = 1/128`, `rOut = 1/64`) so that it has operator norm `< 1` everywhere
  (`norm_smul_T_lt_one`), whence `1 + bmp p • T k p` is invertible (`isUnit_one_add`,
  `isUnit_one_sub_of_norm_lt_one`, `ContinuousLinearEquiv.ofUnit`); this is `A p k`.
* on the ball `‖p‖ ≤ ε₀ = 1/256 < rIn` the bump equals `1` eventually, so
  `q ↦ ((A q k) (v k))_k` is eventually affine with linear part the surjective `M`, hence a
  submersion there (`surj_fderiv`); injectivity is automatic since `A p k` is an equivalence.
-/

namespace Work.Drive

open Filter
open scoped Topology

/-- The 48-dimensional parameter space. -/
private abbrev E48 := EuclideanSpace ℝ (Fin 48)
/-- The target 4-dimensional space. -/
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- A linear equivalence between the 48-dimensional parameter space and three copies of the
space of endomorphisms of `ℝ⁴` (both spaces have dimension `3 * 16 = 48`). -/
private noncomputable def eLin : E48 ≃ₗ[ℝ] (Fin 3 → (E4 →L[ℝ] E4)) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_pi_fintype]
    have h : Module.finrank ℝ (E4 →L[ℝ] E4) = 16 := by
      rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ)),
        Module.finrank_linearMap, finrank_euclideanSpace, Fintype.card_fin]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, h]
    norm_num)

/-- The `k`-th component of `eLin`, as a continuous linear map. -/
private noncomputable def T0 (k : Fin 3) : E48 →L[ℝ] (E4 →L[ℝ] E4) :=
  (ContinuousLinearMap.proj k).comp eLin.toContinuousLinearEquiv.toContinuousLinearMap

/-- For any tuple of non-zero vectors `v k`, the map `h ↦ ((T0 k h) (v k))_k` is surjective. -/
private lemma exists_apply_eq (v : Fin 3 → E4) (hv : ∀ k, v k ≠ 0) (y : Fin 3 → E4) :
    ∃ h : E48, ∀ k, (T0 k h) (v k) = y k := by
  have hℓ : ∀ k, ∃ ℓ : E4 →L[ℝ] ℝ, ℓ (v k) = 1 := by
    intro k
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ (v k) (by simpa [norm_ne_zero_iff] using hv k)
    exact ⟨(‖v k‖)⁻¹ • g, by
      rw [ContinuousLinearMap.smul_apply, hg, smul_eq_mul]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv k))⟩
  choose ℓ hℓ1 using hℓ
  refine ⟨eLin.symm (fun k => (ℓ k).smulRight (y k)), fun k => ?_⟩
  simp only [T0, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change ((eLin (eLin.symm (fun k => (ℓ k).smulRight (y k)))) k) (v k) = y k
  rw [LinearEquiv.apply_symm_apply, ContinuousLinearMap.smulRight_apply, hℓ1 k, one_smul]

private noncomputable def Tnorm : ℝ := ‖T0 0‖ + ‖T0 1‖ + ‖T0 2‖

/-- The scaling factor making the norm of the perturbation at most `16`. -/
private noncomputable def cc : ℝ := 16 / (1 + Tnorm)

/-- The scaled perturbation map. -/
private noncomputable def T (k : Fin 3) : E48 →L[ℝ] (E4 →L[ℝ] E4) := cc • T0 k

private lemma cc_ne_zero : cc ≠ 0 := by
  rw [cc]
  have : (0:ℝ) < 1 + Tnorm := by
    rw [Tnorm]; linarith [norm_nonneg (T0 0), norm_nonneg (T0 1), norm_nonneg (T0 2)]
  positivity

/-- For any tuple of non-zero vectors `v k`, the map `h ↦ ((T k h) (v k))_k` is surjective. -/
private lemma exists_apply_eq' (v : Fin 3 → E4) (hv : ∀ k, v k ≠ 0) (y : Fin 3 → E4) :
    ∃ h : E48, ∀ k, (T k h) (v k) = y k := by
  obtain ⟨h, hh⟩ := exists_apply_eq v hv (fun k => cc⁻¹ • y k)
  refine ⟨h, fun k => ?_⟩
  rw [T, smul_apply, smul_apply, hh k, smul_smul, mul_inv_cancel₀ cc_ne_zero, one_smul]

private lemma T_norm_le (k : Fin 3) : ‖T k‖ ≤ 16 := by
  have h2 : ‖T0 k‖ ≤ Tnorm := by
    fin_cases k <;> simp [Tnorm] <;>
      linarith [norm_nonneg (T0 0), norm_nonneg (T0 1), norm_nonneg (T0 2)]
  have h3 : (0:ℝ) < 1 + Tnorm := by
    rw [Tnorm]; linarith [norm_nonneg (T0 0), norm_nonneg (T0 1), norm_nonneg (T0 2)]
  rw [T, cc]
  calc ‖(16 / (1 + Tnorm)) • T0 k‖ ≤ ‖(16 / (1 + Tnorm))‖ * ‖T0 k‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ = (16 / (1 + Tnorm)) * ‖T0 k‖ := by rw [Real.norm_of_nonneg (by positivity)]
    _ ≤ (16 / (1 + Tnorm)) * (1 + Tnorm) := by
        have h4 : (0:ℝ) ≤ 16 / (1 + Tnorm) := by positivity
        nlinarith [h2]
    _ = 16 := by rw [div_mul_cancel₀ _ h3.ne']

private lemma T_apply_le (k : Fin 3) (p : E48) : ‖T k p‖ ≤ 16 * ‖p‖ := by
  calc ‖T k p‖ ≤ ‖T k‖ * ‖p‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 16 * ‖p‖ := mul_le_mul_of_nonneg_right (T_norm_le k) (norm_nonneg p)

/-- The smooth bump used to cut the perturbation off outside a small ball. -/
private noncomputable def bmp : ContDiffBump (0 : E48) := ⟨1/128, 1/64, by norm_num, by norm_num⟩

private lemma bmp_apply_eq_zero (p : E48) (hp : bmp.rOut ≤ ‖p‖) : bmp p = 0 := by
  refine bmp.zero_of_le_dist ?_
  rwa [dist_eq_norm, sub_zero]

private lemma bmp_apply_eq_one (p : E48) (hp : ‖p‖ ≤ bmp.rIn) : bmp p = 1 := by
  refine bmp.one_of_mem_closedBall ?_
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero]

private lemma bmp_mul_norm_le (p : E48) : bmp p * ‖p‖ ≤ 1/64 := by
  by_cases hp : ‖p‖ ≤ bmp.rOut
  · have hp64 : ‖p‖ ≤ 1/64 := by simpa [bmp] using hp
    calc bmp p * ‖p‖ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right bmp.le_one (norm_nonneg p)
      _ = ‖p‖ := one_mul _
      _ ≤ 1/64 := hp64
  · have hp' : bmp.rOut ≤ ‖p‖ := le_of_lt (not_le.mp hp)
    rw [bmp_apply_eq_zero p hp', zero_mul]; norm_num

/-- The perturbation is everywhere of operator norm `< 1`. -/
private lemma norm_smul_T_lt_one (p : E48) (k : Fin 3) : ‖bmp p • T k p‖ < 1 := by
  have hle : ‖bmp p • T k p‖ ≤ bmp p * ‖T k p‖ := by
    have h := ContinuousLinearMap.opNorm_smul_le (bmp p) (T k p)
    rwa [Real.norm_of_nonneg bmp.nonneg] at h
  have h1 : bmp p * ‖T k p‖ ≤ bmp p * (16 * ‖p‖) :=
    mul_le_mul_of_nonneg_left (T_apply_le k p) bmp.nonneg
  have h2 : bmp p * (16 * ‖p‖) = 16 * (bmp p * ‖p‖) := by ring
  have h3 : bmp p * ‖p‖ ≤ 1/64 := bmp_mul_norm_le p
  linarith

set_option synthInstance.maxHeartbeats 200000 in
private lemma isUnit_one_add (p : E48) (k : Fin 3) : IsUnit (1 + bmp p • T k p) := by
  have h : ‖-(bmp p • T k p)‖ < 1 := by rw [norm_neg]; exact norm_smul_T_lt_one p k
  have h2 : (1 : E4 →L[ℝ] E4) + bmp p • T k p = 1 - (-(bmp p • T k p)) := by abel
  rw [h2]
  exact isUnit_one_sub_of_norm_lt_one h

/-- The perturbation family: `A p k = 1 + bmp p • (T k p)`, an invertible operator because the
perturbation has operator norm `< 1`. -/
private noncomputable def A (p : E48) (k : Fin 3) : E4 ≃L[ℝ] E4 :=
  ContinuousLinearEquiv.ofUnit (isUnit_one_add p k).unit

private lemma A_apply (p : E48) (k : Fin 3) (w : E4) :
    (A p k : E4 →L[ℝ] E4) w = w + bmp p • ((T k p) w) := by
  rw [show (A p k : E4 →L[ℝ] E4) = ((isUnit_one_add p k).unit : E4 →L[ℝ] E4) from rfl,
    IsUnit.unit_spec (isUnit_one_add p k)]
  simp only [add_apply, one_apply_eq_self, smul_apply]

/-- The radius on which the conclusions hold. -/
private noncomputable def eps0 : ℝ := 1/256

private lemma eps0_pos : 0 < eps0 := by norm_num [eps0]

private lemma A_zero (k : Fin 3) : (A 0 k : E4 →L[ℝ] E4) = 1 := by
  have hb : bmp (0:E48) = 1 := bmp_apply_eq_one 0 (by norm_num [bmp])
  have hunit : ((isUnit_one_add 0 k).unit : E4 →L[ℝ] E4) = 1 := by
    rw [IsUnit.unit_spec (isUnit_one_add 0 k)]
    simp [hb]
  rw [show (A 0 k : E4 →L[ℝ] E4) = ((isUnit_one_add 0 k).unit : E4 →L[ℝ] E4) from rfl, hunit]

private lemma A_sub_one_le (k : Fin 3) (p : E48) :
    ‖(A p k : E4 →L[ℝ] E4) - 1‖ ≤ 16 * ‖p‖ := by
  have h : (A p k : E4 →L[ℝ] E4) - 1 = bmp p • T k p := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [sub_apply, A_apply, one_apply_eq_self, smul_apply]
    abel
  rw [h]
  have hle : ‖bmp p • T k p‖ ≤ bmp p * ‖T k p‖ := by
    have h' := ContinuousLinearMap.opNorm_smul_le (bmp p) (T k p)
    rwa [Real.norm_of_nonneg bmp.nonneg] at h'
  have h1 : bmp p * ‖T k p‖ ≤ 1 * (16 * ‖p‖) := by
    have hTa := T_apply_le k p
    have hb : bmp p ≤ 1 := bmp.le_one
    have hb0 : 0 ≤ bmp p := bmp.nonneg
    nlinarith [hTa, norm_nonneg (T k p), norm_nonneg p]
  linarith

private lemma contDiff_A (k : Fin 3) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : E48 × E4 => (A z.1 k : E4 →L[ℝ] E4) z.2) := by
  have hfun : (fun z : E48 × E4 => (A z.1 k : E4 →L[ℝ] E4) z.2)
      = fun z : E48 × E4 => z.2 + bmp z.1 • ((T k z.1) z.2) := by
    funext z; rw [A_apply]
  rw [hfun]
  refine ContDiff.add contDiff_snd ?_
  exact ((bmp.contDiff (n := ⊤)).comp contDiff_fst).smul
    (((T k).contDiff).comp contDiff_fst |>.clm_apply contDiff_snd)

/-- On the small ball the family `p ↦ ((A p k) (v k))_k` is a submersion: it is eventually equal
to the affine map whose linear part is the surjective map `M`. -/
private lemma surj_fderiv (p : E48) (v : Fin 3 → E4) (hp : ‖p‖ ≤ eps0) (hv : ∀ k, v k ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun q : E48 => fun k : Fin 3 => (A q k : E4 →L[ℝ] E4) (v k)) p) := by
  set M : E48 →L[ℝ] (Fin 3 → E4) :=
    ContinuousLinearMap.pi (fun k => ((ContinuousLinearMap.apply ℝ E4) (v k)).comp (T k)) with hM
  have hpball : p ∈ Metric.ball (0:E48) bmp.rIn := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h2 : eps0 < bmp.rIn := by norm_num [eps0, bmp]
    linarith
  have hb : bmp =ᶠ[𝓝 p] 1 := bmp.eventuallyEq_one_of_mem_ball hpball
  have heq : (fun q : E48 => fun k : Fin 3 => (A q k : E4 →L[ℝ] E4) (v k)) =ᶠ[𝓝 p]
      (fun q : E48 => (fun k : Fin 3 => v k) + M q) := by
    filter_upwards [hb] with q hq
    funext k
    rw [A_apply, hM]
    simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, Pi.add_apply, hq, Pi.one_apply, one_smul]
  have hF0 : HasFDerivAt (fun q : E48 => (fun k : Fin 3 => v k) + M q) M p :=
    M.hasFDerivAt.const_add _
  have hF : HasFDerivAt (fun q : E48 => fun k : Fin 3 => (A q k : E4 →L[ℝ] E4) (v k)) M p :=
    hF0.congr_of_eventuallyEq heq
  intro y
  obtain ⟨h, hh⟩ := exists_apply_eq' v hv y
  refine ⟨h, ?_⟩
  rw [hF.fderiv, hM]
  funext k
  rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  exact hh k

private lemma injective_A (k : Fin 3) (p : E48) (hp : ‖p‖ ≤ eps0) :
    Function.Injective (fun v : E4 => (A p k : E4 →L[ℝ] E4) v) := by
  intro a b hab
  exact (A p k).injective hab

theorem exists_perturbation_family_gl :
    ∃ (A : EuclideanSpace ℝ (Fin 48) → Fin 3 →
        (EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))) (ε₀ : ℝ), 0 < ε₀ ∧
      (∀ k, (A 0 k : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) = 1) ∧
      (∀ k p, ‖(A p k : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) - 1‖ ≤ 16 * ‖p‖) ∧
      (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin 48) × EuclideanSpace ℝ (Fin 4) =>
          (A z.1 k : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) z.2)) ∧
      (∀ (p : EuclideanSpace ℝ (Fin 48)) (v : Fin 3 → EuclideanSpace ℝ (Fin 4)), ‖p‖ ≤ ε₀ →
        (∀ k, v k ≠ 0) → Function.Surjective
          (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 48) => fun k : Fin 3 =>
            (A q k : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (v k)) p)) ∧
      (∀ k p, ‖p‖ ≤ ε₀ → Function.Injective (fun v : EuclideanSpace ℝ (Fin 4) =>
          (A p k : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v)) :=
  ⟨A, eps0, eps0_pos, A_zero, A_sub_one_le, contDiff_A, surj_fderiv, injective_A⟩

end Work.Drive
