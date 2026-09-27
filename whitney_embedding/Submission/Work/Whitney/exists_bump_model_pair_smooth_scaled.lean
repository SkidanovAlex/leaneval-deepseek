import Mathlib
import Submission.Work.Whitney.exists_bump_model_pair_smooth

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

private lemma smul_inclModel_ne (n : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (x : Fin n → ℝ) :
    ρ • inclModel n (ρ⁻¹ • x) = inclModel n x := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_fst, inclModel_fst, smul_smul, mul_inv_cancel₀ hρ, one_smul]
  · simp only [Prod.smul_snd, inclModel_snd, smul_zero]

private lemma smul_inv_smul_ne (n : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (x : Fin n → ℝ) :
    ρ • (ρ⁻¹ • x) = x := by
  rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]

private lemma mirrorFun_snd_ne_zero_of (n : ℕ) [NeZero n] {z : (Fin n → ℝ) × (Fin n → ℝ)}
    (h : z.2 ≠ 0) : (mirrorFun n z).2 ≠ 0 := by
  intro hcon
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  simp only [Pi.zero_apply] at hi
  have h0 : (if i = 0 then -z.2 i else z.2 i) = 0 := by
    have h1 := congrFun hcon i
    simpa only [mirrorFun_snd, Pi.zero_apply] using h1
  rcases eq_or_ne i 0 with hi0 | hi0
  · subst hi0
    simp at h0
    exact hi h0
  · simp [hi0] at h0
    exact hi h0

/-- The cut-off model with *independent* support radius `R` and deviation `δ`: unlike
`Work.Whitney.exists_bump_model_pair_smooth` (whose construction ties the support radius to the
deviation, roughly `support = deviation / 2`), here the support radius is exactly `R` and the
deviation is at most `δ`, for arbitrary positive `R`, `δ`.  The construction is the same
`structMap`/`bumpPlus` one, but with a cut-off `χ` supported in a ball of radius `s` whose plateau
contains the unit ball, and `β = λ • structMap χ (λ⁻¹ • ·)` with `λ = R/s`; then the support radius
is `λ s = R` and, for the concrete `structMap` bounds, the deviation is `≤ λ = R/s`, so `s ≥ R/δ`
(and `s ≥ 1`) gives deviation `≤ δ`. -/
theorem exists_bump_model_pair_smooth_scaled (n : ℕ) [NeZero n] (δ R : ℝ) (hδ : 0 < δ)
    (hR : 0 < R) :
    ∃ (βp βm : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (a b : Fin n → ℝ),
      a ≠ b ∧ ‖a‖ < R ∧ ‖b‖ < R ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) βp ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) βm ∧
      (∀ x, Function.Injective (fderiv ℝ βp x)) ∧
      (∀ x, Function.Injective (fderiv ℝ βm x)) ∧
      (∀ x, R ≤ ‖x‖ → βp x = Work.Whitney.inclModel n x) ∧
      (∀ x, R ≤ ‖x‖ → βm x = Work.Whitney.inclModel n x) ∧
      (∀ x, ‖βp x - Work.Whitney.inclModel n x‖ ≤ δ) ∧
      (∀ x, ‖βm x - Work.Whitney.inclModel n x‖ ≤ δ) ∧
      (∀ u, ‖u‖ < R → (βp u).2 ≠ 0) ∧ (∀ u, ‖u‖ < R → (βm u).2 ≠ 0) ∧
      βp a = βp b ∧ βm a = βm b ∧
      (∀ x y, x ≠ y → βp x = βp y → (x = a ∧ y = b) ∨ (x = b ∧ y = a)) ∧
      (∀ x y, x ≠ y → βm x = βm y → (x = a ∧ y = b) ∨ (x = b ∧ y = a)) ∧
      LinearMap.det (((fderiv ℝ βp a).coprod (fderiv ℝ βp b)).toLinearMap) ≠ 0 ∧
      LinearMap.det (((fderiv ℝ βm a).coprod (fderiv ℝ βm b)).toLinearMap) =
        -LinearMap.det (((fderiv ℝ βp a).coprod (fderiv ℝ βp b)).toLinearMap) := by
  -- the support radius: `s ≥ max 3 (R/δ) + 1`, so that `s > 2` (cut-off plateau contains the unit
  -- ball), `s > 1` (the double point `λ e₀` lies strictly inside the ball of radius `R`), and
  -- `λ = R/s ≤ δ`.
  set s : ℝ := max 3 (R / δ) + 1 with hsdef
  have hsδ : R / δ ≤ s := by rw [hsdef]; linarith [le_max_right (3 : ℝ) (R / δ)]
  have hs_gt3 : 3 < s := by rw [hsdef]; linarith [le_max_left (3 : ℝ) (R / δ)]
  have hs_pos : 0 < s := by linarith
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_gt1 : 1 < s := by linarith
  have hs_gt2 : 2 < s := by linarith
  have hδs : R ≤ δ * s := by
    have h := mul_le_mul_of_nonneg_left hsδ (le_of_lt hδ)
    rwa [mul_div_cancel₀ R (ne_of_gt hδ)] at h
  -- the cut-off function, supported in the closed ball of radius `s`
  let f : ContDiffBump (0 : Fin n → ℝ) := ContDiffBump.mk 2 s (by norm_num) hs_gt2
  let χ : (Fin n → ℝ) → ℝ := ⇑f
  have hχ_smooth : ContDiff ℝ ∞ χ := f.contDiff
  have hχ_nonneg : ∀ x, 0 ≤ χ x := fun x => f.nonneg
  have hχ_le_one : ∀ x, χ x ≤ 1 := fun x => f.le_one
  have hχ_eq_one : ∀ x, ‖x‖ ≤ 2 → χ x = 1 := by
    intro x hx
    exact f.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hx)
  have hχ_ne_zero : ∀ x, ‖x‖ < s → χ x ≠ 0 := by
    intro x hx
    exact ne_of_gt (f.pos_of_mem_ball (by rw [Metric.mem_ball, dist_zero_right]; exact hx))
  have hχ_eq_zero : ∀ x, s ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    exact f.zero_of_le_dist (by rw [dist_zero_right]; exact hx)
  -- the scaling factor `λ = R / s ≥ 1`
  set lam : ℝ := R / s with hlamdef
  have hlam_pos : 0 < lam := by rw [hlamdef]; exact div_pos hR hs_pos
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlam_mul : lam * s = R := by rw [hlamdef, div_mul_cancel₀ R hs_ne]
  have hlam_inv_mul : lam⁻¹ * R = s := by
    rw [← hlam_mul, ← mul_assoc, inv_mul_cancel₀ hlam_ne, one_mul]
  have hlam_le_δ : lam ≤ δ := by
    rw [hlamdef, div_le_iff₀ hs_pos]
    exact hδs
  have hlevel : ∀ t : ℝ, uhat n χ (t • e0 n) = 1 / 2 ↔ t = 1 ∨ t = -1 :=
    fun t => BumpModel.uhat_level n hχ_eq_one hχ_le_one t
  -- the scaled model is smooth and its derivative is the derivative of `structMap` at the rescaled point
  have hfd_smooth : ContDiff ℝ ∞ (bumpPlus n χ lam) ∧
      (∀ x : Fin n → ℝ,
        fderiv ℝ (bumpPlus n χ lam) x = fderiv ℝ (structMap n χ) (lam⁻¹ • x)) :=
    BumpModel.bumpPlus_fderiv_smooth n hχ_smooth hlam_ne
  -- the derivative of the structure map at the two preimages of the double point
  have hfd_struct : (∀ v : Fin n → ℝ, fderiv ℝ (structMap n χ) (e0 n) v = (v, sheetE0 n v)) ∧
      (∀ v : Fin n → ℝ, fderiv ℝ (structMap n χ) (-(e0 n)) v = (v, sheetNegE0 n v)) :=
    BumpModel.fderiv_structMap_at_pm_e0 n hχ_smooth hχ_eq_one
  -- the mirrored model has derivative the mirror applied to the derivative
  have hfd_minus : ∀ x : Fin n → ℝ,
      (fderiv ℝ (bumpMinus n χ lam) x).toLinearMap
        = (mirrorLin n) ∘ₗ (fderiv ℝ (bumpPlus n χ lam) x).toLinearMap :=
    fun x => BumpModel.fderiv_bumpMinus n hfd_smooth.1 x
  -- the second block of the structure map vanishes exactly where the cut-off does
  have hsnd_struct : ∀ x : Fin n → ℝ, (structMap n χ x).2 ≠ 0 ↔ χ x ≠ 0 :=
    fun x => BumpModel.structMap_snd_ne_zero n x
  -- the immersion property of the model
  have hcrit : ∀ t : ℝ, uhat n χ (t • e0 n) = 1 / 2 →
      (fderiv ℝ (uhat n χ) (t • e0 n)) (e0 n) ≠ 0 := by
    intro t ht
    rcases (hlevel t).mp ht with rfl | rfl
    · rw [one_smul, (BumpModel.uhat_fderiv_infty n hχ_smooth hχ_eq_one (e0 n)).1]
      simp only [e0, Pi.single_eq_same, mul_one]
      norm_num
    · rw [neg_one_smul, (BumpModel.uhat_fderiv_infty n hχ_smooth hχ_eq_one (e0 n)).2]
      simp only [e0, Pi.single_eq_same, mul_one]
      norm_num
  have himm_p : ∀ x : Fin n → ℝ, Function.Injective (fderiv ℝ (bumpPlus n χ lam) x) := by
    intro x
    rw [hfd_smooth.2 x]
    exact BumpModel.structMap_immersion_infty n hχ_smooth hcrit (lam⁻¹ • x)
  have hbm_smooth : ContDiff ℝ ∞ (bumpMinus n χ lam) := by
    have hM : ContDiff ℝ ∞ (mirrorFun n) := by
      have hfun : mirrorFun n = ⇑(LinearMap.toContinuousLinearMap (mirrorLin n)) := by
        funext z
        rw [show (LinearMap.toContinuousLinearMap (mirrorLin n)) z = mirrorLin n z from rfl,
          mirrorLin_apply]
      rw [hfun]
      exact (LinearMap.toContinuousLinearMap (mirrorLin n)).contDiff
    change ContDiff ℝ ∞ (fun x => mirrorFun n (bumpPlus n χ lam x))
    exact hM.comp hfd_smooth.1
  have himm_m : ∀ x : Fin n → ℝ, Function.Injective (fderiv ℝ (bumpMinus n χ lam) x) := by
    intro x u v huv
    have h1 : mirrorLin n ((fderiv ℝ (bumpPlus n χ lam) x) u)
        = mirrorLin n ((fderiv ℝ (bumpPlus n χ lam) x) v) := by
      have h2 : (fderiv ℝ (bumpMinus n χ lam) x) u
          = mirrorLin n ((fderiv ℝ (bumpPlus n χ lam) x) u) := by
        have h3 := congrArg (fun (L : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) => L u)
          (hfd_minus x)
        simpa using h3
      have h4 : (fderiv ℝ (bumpMinus n χ lam) x) v
          = mirrorLin n ((fderiv ℝ (bumpPlus n χ lam) x) v) := by
        have h3 := congrArg (fun (L : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) => L v)
          (hfd_minus x)
        simpa using h3
      rw [← h2, ← h4, huv]
    exact himm_p x (mirrorLin_injective n h1)
  have hag_p : ∀ x : Fin n → ℝ, R ≤ ‖x‖ → bumpPlus n χ lam x = inclModel n x := by
    intro x hx
    have h1 : s ≤ ‖lam⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam_pos)]
      have h5 := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hlam_pos))
      linarith [hlam_inv_mul]
    rw [bumpPlus_apply, structMap_eq_incl_of_chi_zero n (hχ_eq_zero _ h1),
      smul_inclModel_ne n hlam_ne x]
  have hag_m : ∀ x : Fin n → ℝ, R ≤ ‖x‖ → bumpMinus n χ lam x = inclModel n x := by
    intro x hx
    rw [bumpMinus_apply, hag_p x hx, mirrorFun_inclModel]
  have hclose_p : ∀ x : Fin n → ℝ, ‖bumpPlus n χ lam x - inclModel n x‖ ≤ δ := by
    intro x
    have h1 : bumpPlus n χ lam x - inclModel n x
        = lam • (structMap n χ (lam⁻¹ • x) - inclModel n (lam⁻¹ • x)) := by
      rw [bumpPlus_apply, ← smul_inclModel_ne n hlam_ne x, ← smul_sub]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hlam_pos]
    have h2 := structMap_sub_incl_bound n hχ_nonneg hχ_le_one (lam⁻¹ • x)
    have h3 : lam * ‖structMap n χ (lam⁻¹ • x) - inclModel n (lam⁻¹ • x)‖ ≤ lam * 1 :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hlam_pos)
    linarith [hlam_le_δ]
  have hclose_m : ∀ x : Fin n → ℝ, ‖bumpMinus n χ lam x - inclModel n x‖ ≤ δ := by
    intro x
    have h1 : bumpMinus n χ lam x - inclModel n x
        = mirrorLin n (bumpPlus n χ lam x - inclModel n x) := by
      conv_lhs =>
        rw [show bumpMinus n χ lam x = mirrorLin n (bumpPlus n χ lam x) from by
              rw [bumpMinus_apply, mirrorLin_apply],
            show inclModel n x = mirrorLin n (inclModel n x) from by
              rw [mirrorLin_apply]
              exact (mirrorFun_inclModel n x).symm]
      rw [← map_sub]
    rw [h1, mirrorLin_norm]
    exact hclose_p x
  have hsnd_p : ∀ u : Fin n → ℝ, ‖u‖ < R → (bumpPlus n χ lam u).2 ≠ 0 := by
    intro u hu
    have hu' : ‖lam⁻¹ • u‖ < s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam_pos)]
      have h5 := mul_lt_mul_of_pos_left hu (inv_pos.mpr hlam_pos)
      linarith [hlam_inv_mul]
    have hχnz : χ (lam⁻¹ • u) ≠ 0 := hχ_ne_zero _ hu'
    rw [bumpPlus_apply, Prod.smul_snd]
    exact smul_ne_zero hlam_ne ((hsnd_struct (lam⁻¹ • u)).mpr hχnz)
  have hsnd_m : ∀ u : Fin n → ℝ, ‖u‖ < R → (bumpMinus n χ lam u).2 ≠ 0 := by
    intro u hu
    rw [bumpMinus_apply]
    exact mirrorFun_snd_ne_zero_of n (hsnd_p u hu)
  have heq_p : bumpPlus n χ lam (lam • e0 n) = bumpPlus n χ lam (-(lam • e0 n)) := by
    have h1 : lam⁻¹ • (lam • e0 n) = e0 n := by
      rw [smul_smul, inv_mul_cancel₀ hlam_ne, one_smul]
    have h2 : lam⁻¹ • (-(lam • e0 n)) = -(e0 n) := by
      rw [smul_neg, smul_smul, inv_mul_cancel₀ hlam_ne, one_smul]
    rw [bumpPlus_apply, bumpPlus_apply, h1, h2]
    exact congrArg (fun z : (Fin n → ℝ) × (Fin n → ℝ) => lam • z)
      ((BumpModel.structMap_double_point n hlevel (e0 n) (-(e0 n))).mpr
        (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have heq_m : bumpMinus n χ lam (lam • e0 n) = bumpMinus n χ lam (-(lam • e0 n)) := by
    rw [bumpMinus_apply, bumpMinus_apply, heq_p]
  have hdouble : ∀ x y : Fin n → ℝ, x ≠ y → bumpPlus n χ lam x = bumpPlus n χ lam y →
      (x = lam • e0 n ∧ y = -(lam • e0 n)) ∨ (x = -(lam • e0 n) ∧ y = lam • e0 n) := by
    intro x y hxy h
    have h' : structMap n χ (lam⁻¹ • x) = structMap n χ (lam⁻¹ • y) := by
      have h2 := congrArg (fun z : (Fin n → ℝ) × (Fin n → ℝ) => lam⁻¹ • z) h
      simp only [bumpPlus_apply] at h2
      rwa [smul_smul, smul_smul, inv_mul_cancel₀ hlam_ne, one_smul, one_smul] at h2
    rcases (BumpModel.structMap_double_point n hlevel (lam⁻¹ • x) (lam⁻¹ • y)).mp h' with
      h1 | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact absurd (by rw [← smul_inv_smul_ne n hlam_ne x, h1, smul_inv_smul_ne n hlam_ne y]) hxy
    · left
      refine ⟨?_, ?_⟩
      · rw [← smul_inv_smul_ne n hlam_ne x, hx]
      · rw [← smul_inv_smul_ne n hlam_ne y, hy, smul_neg]
    · right
      refine ⟨?_, ?_⟩
      · rw [← smul_inv_smul_ne n hlam_ne x, hx, smul_neg]
      · rw [← smul_inv_smul_ne n hlam_ne y, hy]
  have huniq_m : ∀ x y : Fin n → ℝ, x ≠ y → bumpMinus n χ lam x = bumpMinus n χ lam y →
      (x = lam • e0 n ∧ y = -(lam • e0 n)) ∨ (x = -(lam • e0 n) ∧ y = lam • e0 n) := by
    intro x y hxy h
    apply hdouble x y hxy
    have h' : mirrorLin n (bumpPlus n χ lam x) = mirrorLin n (bumpPlus n χ lam y) := by
      have h2 := h
      simp only [bumpMinus_apply, ← mirrorLin_apply] at h2
      exact h2
    exact mirrorLin_injective n h'
  have hra : ‖lam • e0 n‖ = lam := by rw [norm_smul_e0 n lam, abs_of_pos hlam_pos]
  have hna : ‖lam • e0 n‖ < R := by
    rw [hra, hlamdef]
    exact div_lt_self hR hs_gt1
  have hnb : ‖-(lam • e0 n)‖ < R := by
    rw [norm_neg, hra, hlamdef]
    exact div_lt_self hR hs_gt1
  have hane : lam • e0 n ≠ -(lam • e0 n) := by
    intro h
    have h0 : lam = -lam := by
      have h1 := congrFun h 0
      simpa only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, e0, Pi.single_eq_same, mul_one]
        using h1
    linarith
  -- the two-sheets endomorphism of `bumpPlus` is `C n`
  have hfa : fderiv ℝ (bumpPlus n χ lam) (lam • e0 n) = fderiv ℝ (structMap n χ) (e0 n) := by
    rw [hfd_smooth.2]
    congr 1
    rw [smul_smul, inv_mul_cancel₀ hlam_ne, one_smul]
  have hfb : fderiv ℝ (bumpPlus n χ lam) (-(lam • e0 n)) = fderiv ℝ (structMap n χ) (-(e0 n)) := by
    rw [hfd_smooth.2]
    congr 1
    rw [smul_neg, smul_smul, inv_mul_cancel₀ hlam_ne, one_smul]
  have hCp : ((fderiv ℝ (bumpPlus n χ lam) (lam • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ lam) (-(lam • e0 n)))).toLinearMap = C n := by
    apply LinearMap.ext
    intro p
    simp only [ContinuousLinearMap.coe_coprod, LinearMap.coprod_apply,
      ContinuousLinearMap.coe_coe, hfa, hfb, hfd_struct.1 p.1, hfd_struct.2 p.2, C_apply,
      Prod.mk_add_mk]
  have hdet_p : LinearMap.det (((fderiv ℝ (bumpPlus n χ lam) (lam • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ lam) (-(lam • e0 n)))).toLinearMap) ≠ 0 := by
    rw [hCp]
    exact det_C_ne_zero n
  have hCm : ((fderiv ℝ (bumpMinus n χ lam) (lam • e0 n)).coprod
        (fderiv ℝ (bumpMinus n χ lam) (-(lam • e0 n)))).toLinearMap
      = (mirrorLin n) ∘ₗ ((fderiv ℝ (bumpPlus n χ lam) (lam • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ lam) (-(lam • e0 n)))).toLinearMap := by
    apply LinearMap.ext
    intro p
    simp only [ContinuousLinearMap.coe_coprod, LinearMap.coprod_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, hfd_minus, map_add]
  have hdet_m : LinearMap.det (((fderiv ℝ (bumpMinus n χ lam) (lam • e0 n)).coprod
        (fderiv ℝ (bumpMinus n χ lam) (-(lam • e0 n)))).toLinearMap)
      = - LinearMap.det (((fderiv ℝ (bumpPlus n χ lam) (lam • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ lam) (-(lam • e0 n)))).toLinearMap) := by
    rw [hCm, LinearMap.det_comp, mirrorLin_det]
    ring
  refine ⟨bumpPlus n χ lam, bumpMinus n χ lam, lam • e0 n, -(lam • e0 n),
    hane, hna, hnb, hfd_smooth.1, hbm_smooth, himm_p, himm_m,
    hag_p, hag_m, hclose_p, hclose_m, hsnd_p, hsnd_m, heq_p, heq_m, hdouble, huniq_m,
    hdet_p, hdet_m⟩

end Work.Whitney
