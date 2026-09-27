import Mathlib
import Submission.Work.Whitney.LocalModel
import Submission.Work.Whitney.TransverseAux
import Submission.Work.Whitney.BumpModel.Defs
import Submission.Work.Whitney.BumpModel.exists_bump_chi
import Submission.Work.Whitney.BumpModel.structMap_double_point
import Submission.Work.Whitney.BumpModel.uhat_level
import Submission.Work.Whitney.BumpModel.structMap_immersion_infty
import Submission.Work.Whitney.BumpModel.uhat_fderiv_infty
import Submission.Work.Whitney.BumpModel.bumpPlus_fderiv_smooth
import Submission.Work.Whitney.BumpModel.fderiv_structMap_at_pm_e0
import Submission.Work.Whitney.BumpModel.fderiv_bumpMinus
import Submission.Work.Whitney.BumpModel.structMap_snd_ne_zero

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

private lemma smul_inclModel (n : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (x : Fin n → ℝ) :
    ρ • inclModel n (ρ⁻¹ • x) = inclModel n x := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_fst, inclModel_fst, smul_smul, mul_inv_cancel₀ hρ, one_smul]
  · simp only [Prod.smul_snd, inclModel_snd, smul_zero]

private lemma smul_inv_smul_aux (n : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (x : Fin n → ℝ) :
    ρ • (ρ⁻¹ • x) = x := by
  rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]

private lemma inv_smul_smul_aux (n : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (x : Fin n → ℝ) :
    ρ⁻¹ • (ρ • x) = x := by
  rw [smul_smul, inv_mul_cancel₀ hρ, one_smul]

private lemma mirrorFun_snd_ne_zero (n : ℕ) [NeZero n] {z : (Fin n → ℝ) × (Fin n → ℝ)}
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

/-- For every `δ > 0` and every bound `R₀ > 0` on the size of the modification region there are two
"cut-off Whitney models": smooth (`C^∞`, *not* analytic — `ContDiff ℝ ∞`, since `⊤` would mean
analyticity and an analytic map agreeing with the linear inclusion outside a ball is the inclusion
itself, by analytic continuation) immersions `β⁺, β⁻ : ℝⁿ → ℝⁿ × ℝⁿ` which agree exactly with the
linear inclusion `inclModel n` (`x ↦ (x, 0)`) outside a ball of radius `R ≤ R₀`, are `δ`-close to it
everywhere, each have exactly one double point — the same pair `a ≠ b` with `β⁺ a = β⁺ b`,
`β⁻ a = β⁻ b` — with `‖a‖ < R` and `‖b‖ < R`, whose second block is nonzero on the ball of radius
`R`, transversely, and whose double points have opposite signs: the determinants of the "two sheets"
endomorphisms `(u, v) ↦ D β a u + D β b v` are nonzero and opposite.  (The helper files under
`Submission/Work/Whitney/BumpModel/` — `structMap`, `bumpPlus`, `bumpMinus`, `mirrorLin` and their
lemmas, including the `_infty` smoothness variants — were written by a colleague for exactly this
statement and are reusable.) -/
theorem exists_bump_model_pair_smooth (n : ℕ) [NeZero n] (δ R₀ : ℝ) (hδ : 0 < δ) (hR₀ : 0 < R₀) :
    ∃ (βp βm : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (a b : Fin n → ℝ) (R : ℝ),
      0 < R ∧ R ≤ R₀ ∧ a ≠ b ∧ ‖a‖ < R ∧ ‖b‖ < R ∧
      ContDiff ℝ ∞ βp ∧ ContDiff ℝ ∞ βm ∧
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
  obtain ⟨χ, hχ_smooth, hχ_nonneg, hχ_le_one, hχ_eq_one, hχ_ne_zero, hχ_eq_zero⟩ :=
    BumpModel.exists_bump_chi n
  have hmin_pos : 0 < min δ R₀ := lt_min hδ hR₀
  set ρ : ℝ := min δ R₀ / 8 with hρdef
  have hρ_pos : 0 < ρ := by rw [hρdef]; exact div_pos hmin_pos (by norm_num)
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
  have hρ_le_δ : ρ ≤ δ := by
    rw [hρdef]; have := min_le_left δ R₀; linarith
  have hR_le_R₀ : 4 * ρ ≤ R₀ := by
    rw [hρdef]; nlinarith [min_le_right δ R₀, hR₀]
  have hR_pos : 0 < 4 * ρ := by linarith
  have hlevel : ∀ t : ℝ, uhat n χ (t • e0 n) = 1 / 2 ↔ t = 1 ∨ t = -1 :=
    fun t => BumpModel.uhat_level n hχ_eq_one hχ_le_one t
  -- the scaled model is smooth and its derivative is the derivative of `structMap` at the rescaled point
  have hfd_smooth : ContDiff ℝ ∞ (bumpPlus n χ ρ) ∧
      (∀ x : Fin n → ℝ,
        fderiv ℝ (bumpPlus n χ ρ) x = fderiv ℝ (structMap n χ) (ρ⁻¹ • x)) :=
    BumpModel.bumpPlus_fderiv_smooth n hχ_smooth hρ_ne
  -- the derivative of the structure map at the two preimages of the double point
  have hfd_struct : (∀ v : Fin n → ℝ, fderiv ℝ (structMap n χ) (e0 n) v = (v, sheetE0 n v)) ∧
      (∀ v : Fin n → ℝ, fderiv ℝ (structMap n χ) (-(e0 n)) v = (v, sheetNegE0 n v)) :=
    BumpModel.fderiv_structMap_at_pm_e0 n hχ_smooth hχ_eq_one
  -- the mirrored model has derivative the mirror applied to the derivative
  have hfd_minus : ∀ x : Fin n → ℝ,
      (fderiv ℝ (bumpMinus n χ ρ) x).toLinearMap
        = (mirrorLin n) ∘ₗ (fderiv ℝ (bumpPlus n χ ρ) x).toLinearMap :=
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
  have himm_p : ∀ x : Fin n → ℝ, Function.Injective (fderiv ℝ (bumpPlus n χ ρ) x) := by
    intro x
    rw [hfd_smooth.2 x]
    exact BumpModel.structMap_immersion_infty n hχ_smooth hcrit (ρ⁻¹ • x)
  have hbm_smooth : ContDiff ℝ ∞ (bumpMinus n χ ρ) := by
    have hM : ContDiff ℝ ∞ (mirrorFun n) := by
      have hfun : mirrorFun n = ⇑(LinearMap.toContinuousLinearMap (mirrorLin n)) := by
        funext z
        rw [show (LinearMap.toContinuousLinearMap (mirrorLin n)) z = mirrorLin n z from rfl,
          mirrorLin_apply]
      rw [hfun]
      exact (LinearMap.toContinuousLinearMap (mirrorLin n)).contDiff
    change ContDiff ℝ ∞ (fun x => mirrorFun n (bumpPlus n χ ρ x))
    exact hM.comp hfd_smooth.1
  have himm_m : ∀ x : Fin n → ℝ, Function.Injective (fderiv ℝ (bumpMinus n χ ρ) x) := by
    intro x u v huv
    have h1 : mirrorLin n ((fderiv ℝ (bumpPlus n χ ρ) x) u)
        = mirrorLin n ((fderiv ℝ (bumpPlus n χ ρ) x) v) := by
      have h2 : (fderiv ℝ (bumpMinus n χ ρ) x) u
          = mirrorLin n ((fderiv ℝ (bumpPlus n χ ρ) x) u) := by
        have h3 := congrArg (fun (L : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) => L u)
          (hfd_minus x)
        simpa using h3
      have h4 : (fderiv ℝ (bumpMinus n χ ρ) x) v
          = mirrorLin n ((fderiv ℝ (bumpPlus n χ ρ) x) v) := by
        have h3 := congrArg (fun (L : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) => L v)
          (hfd_minus x)
        simpa using h3
      rw [← h2, ← h4, huv]
    exact himm_p x (mirrorLin_injective n h1)
  have hag_p : ∀ x : Fin n → ℝ, 4 * ρ ≤ ‖x‖ → bumpPlus n χ ρ x = inclModel n x := by
    intro x hx
    have h1 : 4 ≤ ‖ρ⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ_pos)]
      have h4 : ρ⁻¹ * (4 * ρ) = 4 := by
        rw [mul_comm (4 : ℝ) ρ, ← mul_assoc, inv_mul_cancel₀ hρ_ne, one_mul]
      have h5 := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hρ_pos))
      linarith
    rw [bumpPlus_apply, structMap_eq_incl_of_chi_zero n (hχ_eq_zero _ h1),
      smul_inclModel n hρ_ne x]
  have hag_m : ∀ x : Fin n → ℝ, 4 * ρ ≤ ‖x‖ → bumpMinus n χ ρ x = inclModel n x := by
    intro x hx
    rw [bumpMinus_apply, hag_p x hx, mirrorFun_inclModel]
  have hclose_p : ∀ x : Fin n → ℝ, ‖bumpPlus n χ ρ x - inclModel n x‖ ≤ δ := by
    intro x
    have h1 : bumpPlus n χ ρ x - inclModel n x
        = ρ • (structMap n χ (ρ⁻¹ • x) - inclModel n (ρ⁻¹ • x)) := by
      rw [bumpPlus_apply, ← smul_inclModel n hρ_ne x, ← smul_sub]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hρ_pos]
    have h2 := structMap_sub_incl_bound n hχ_nonneg hχ_le_one (ρ⁻¹ • x)
    have h3 : ρ * ‖structMap n χ (ρ⁻¹ • x) - inclModel n (ρ⁻¹ • x)‖ ≤ ρ * 1 :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hρ_pos)
    linarith
  have hclose_m : ∀ x : Fin n → ℝ, ‖bumpMinus n χ ρ x - inclModel n x‖ ≤ δ := by
    intro x
    have h1 : bumpMinus n χ ρ x - inclModel n x
        = mirrorLin n (bumpPlus n χ ρ x - inclModel n x) := by
      conv_lhs =>
        rw [show bumpMinus n χ ρ x = mirrorLin n (bumpPlus n χ ρ x) from by
              rw [bumpMinus_apply, mirrorLin_apply],
            show inclModel n x = mirrorLin n (inclModel n x) from by
              rw [mirrorLin_apply]
              exact (mirrorFun_inclModel n x).symm]
      rw [← map_sub]
    rw [h1, mirrorLin_norm]
    exact hclose_p x
  have hsnd_p : ∀ u : Fin n → ℝ, ‖u‖ < 4 * ρ → (bumpPlus n χ ρ u).2 ≠ 0 := by
    intro u hu
    have hu' : ‖ρ⁻¹ • u‖ < 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ_pos)]
      have h4 : ρ⁻¹ * (4 * ρ) = 4 := by
        rw [mul_comm (4 : ℝ) ρ, ← mul_assoc, inv_mul_cancel₀ hρ_ne, one_mul]
      have h5 := mul_lt_mul_of_pos_left hu (inv_pos.mpr hρ_pos)
      linarith
    have hχnz : χ (ρ⁻¹ • u) ≠ 0 := hχ_ne_zero _ hu'
    rw [bumpPlus_apply, Prod.smul_snd]
    exact smul_ne_zero hρ_ne ((hsnd_struct (ρ⁻¹ • u)).mpr hχnz)
  have hsnd_m : ∀ u : Fin n → ℝ, ‖u‖ < 4 * ρ → (bumpMinus n χ ρ u).2 ≠ 0 := by
    intro u hu
    rw [bumpMinus_apply]
    exact mirrorFun_snd_ne_zero n (hsnd_p u hu)
  have heq_p : bumpPlus n χ ρ (ρ • e0 n) = bumpPlus n χ ρ (-(ρ • e0 n)) := by
    have h1 : ρ⁻¹ • (ρ • e0 n) = e0 n := by rw [smul_smul, inv_mul_cancel₀ hρ_ne, one_smul]
    have h2 : ρ⁻¹ • (-(ρ • e0 n)) = -(e0 n) := by
      rw [smul_neg, smul_smul, inv_mul_cancel₀ hρ_ne, one_smul]
    rw [bumpPlus_apply, bumpPlus_apply, h1, h2]
    exact congrArg (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ρ • z)
      ((BumpModel.structMap_double_point n hlevel (e0 n) (-(e0 n))).mpr
        (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have heq_m : bumpMinus n χ ρ (ρ • e0 n) = bumpMinus n χ ρ (-(ρ • e0 n)) := by
    rw [bumpMinus_apply, bumpMinus_apply, heq_p]
  have hdouble : ∀ x y : Fin n → ℝ, x ≠ y → bumpPlus n χ ρ x = bumpPlus n χ ρ y →
      (x = ρ • e0 n ∧ y = -(ρ • e0 n)) ∨ (x = -(ρ • e0 n) ∧ y = ρ • e0 n) := by
    intro x y hxy h
    have h' : structMap n χ (ρ⁻¹ • x) = structMap n χ (ρ⁻¹ • y) := by
      have h2 := congrArg (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ρ⁻¹ • z) h
      simp only [bumpPlus_apply] at h2
      rwa [smul_smul, smul_smul, inv_mul_cancel₀ hρ_ne, one_smul, one_smul] at h2
    rcases (BumpModel.structMap_double_point n hlevel (ρ⁻¹ • x) (ρ⁻¹ • y)).mp h' with
      h1 | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact absurd (by rw [← smul_inv_smul_aux n hρ_ne x, h1, smul_inv_smul_aux n hρ_ne y]) hxy
    · left
      refine ⟨?_, ?_⟩
      · rw [← smul_inv_smul_aux n hρ_ne x, hx]
      · rw [← smul_inv_smul_aux n hρ_ne y, hy, smul_neg]
    · right
      refine ⟨?_, ?_⟩
      · rw [← smul_inv_smul_aux n hρ_ne x, hx, smul_neg]
      · rw [← smul_inv_smul_aux n hρ_ne y, hy]
  have huniq_m : ∀ x y : Fin n → ℝ, x ≠ y → bumpMinus n χ ρ x = bumpMinus n χ ρ y →
      (x = ρ • e0 n ∧ y = -(ρ • e0 n)) ∨ (x = -(ρ • e0 n) ∧ y = ρ • e0 n) := by
    intro x y hxy h
    apply hdouble x y hxy
    have h' : mirrorLin n (bumpPlus n χ ρ x) = mirrorLin n (bumpPlus n χ ρ y) := by
      have h2 := h
      simp only [bumpMinus_apply, ← mirrorLin_apply] at h2
      exact h2
    exact mirrorLin_injective n h'
  have hra : ‖ρ • e0 n‖ = ρ := by rw [norm_smul_e0 n ρ, abs_of_pos hρ_pos]
  have hna : ‖ρ • e0 n‖ < 4 * ρ := by rw [hra]; linarith
  have hnb : ‖-(ρ • e0 n)‖ < 4 * ρ := by rw [norm_neg, hra]; linarith
  have hane : ρ • e0 n ≠ -(ρ • e0 n) := by
    intro h
    have h0 : ρ = -ρ := by
      have h1 := congrFun h 0
      simpa only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, e0, Pi.single_eq_same, mul_one]
        using h1
    linarith
  -- the two-sheets endomorphism of `bumpPlus` is `C n`
  have hfa : fderiv ℝ (bumpPlus n χ ρ) (ρ • e0 n) = fderiv ℝ (structMap n χ) (e0 n) := by
    rw [hfd_smooth.2]
    congr 1
    rw [smul_smul, inv_mul_cancel₀ hρ_ne, one_smul]
  have hfb : fderiv ℝ (bumpPlus n χ ρ) (-(ρ • e0 n)) = fderiv ℝ (structMap n χ) (-(e0 n)) := by
    rw [hfd_smooth.2]
    congr 1
    rw [smul_neg, smul_smul, inv_mul_cancel₀ hρ_ne, one_smul]
  have hCp : ((fderiv ℝ (bumpPlus n χ ρ) (ρ • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ ρ) (-(ρ • e0 n)))).toLinearMap = C n := by
    apply LinearMap.ext
    intro p
    simp only [ContinuousLinearMap.coe_coprod, LinearMap.coprod_apply,
      ContinuousLinearMap.coe_coe, hfa, hfb, hfd_struct.1 p.1, hfd_struct.2 p.2, C_apply,
      Prod.mk_add_mk]
  have hdet_p : LinearMap.det (((fderiv ℝ (bumpPlus n χ ρ) (ρ • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ ρ) (-(ρ • e0 n)))).toLinearMap) ≠ 0 := by
    rw [hCp]
    exact det_C_ne_zero n
  have hCm : ((fderiv ℝ (bumpMinus n χ ρ) (ρ • e0 n)).coprod
        (fderiv ℝ (bumpMinus n χ ρ) (-(ρ • e0 n)))).toLinearMap
      = (mirrorLin n) ∘ₗ ((fderiv ℝ (bumpPlus n χ ρ) (ρ • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ ρ) (-(ρ • e0 n)))).toLinearMap := by
    apply LinearMap.ext
    intro p
    simp only [ContinuousLinearMap.coe_coprod, LinearMap.coprod_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, hfd_minus, map_add]
  have hdet_m : LinearMap.det (((fderiv ℝ (bumpMinus n χ ρ) (ρ • e0 n)).coprod
        (fderiv ℝ (bumpMinus n χ ρ) (-(ρ • e0 n)))).toLinearMap)
      = - LinearMap.det (((fderiv ℝ (bumpPlus n χ ρ) (ρ • e0 n)).coprod
        (fderiv ℝ (bumpPlus n χ ρ) (-(ρ • e0 n)))).toLinearMap) := by
    rw [hCm, LinearMap.det_comp, mirrorLin_det]
    ring
  refine ⟨bumpPlus n χ ρ, bumpMinus n χ ρ, ρ • e0 n, -(ρ • e0 n), 4 * ρ,
    hR_pos, hR_le_R₀, hane, hna, hnb, hfd_smooth.1, hbm_smooth, himm_p, himm_m,
    hag_p, hag_m, hclose_p, hclose_m, hsnd_p, hsnd_m, heq_p, heq_m, hdouble, huniq_m,
    hdet_p, hdet_m⟩

end Work.Whitney
