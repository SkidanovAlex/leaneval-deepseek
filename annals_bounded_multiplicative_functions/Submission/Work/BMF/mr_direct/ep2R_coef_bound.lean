import Mathlib
import Submission.Work.BMF.mr_direct.ep2R_defs
import Submission.Work.BMF.mr_direct.ep2_integral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

lemma ep2R_coef_bound {P Q A B : ℝ} (hA : 1 ≤ A) (a b c : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (x : Σ _ : ℕ, ℕ) (hx : x ∈ Work.BMF.mr_direct.pSetER P Q A B) :
    ‖Work.BMF.mr_direct.coef a b c P Q x‖
      ≤ 2 / (Work.BMF.mrDirect.omegaCount P Q (Work.BMF.mr_direct.freq x) : ℝ) := by
  have hr1 : 1 ≤ Work.BMF.mrDirect.omegaCount P Q x.2 := one_le_omegaCount_sndR hA hx
  have hfreq := omegaCount_freq_eqR hx
  have hnorm1 : ‖(((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ) : ℂ))⁻¹‖
      = (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have hnorm2 : ‖(((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ) : ℂ))⁻¹‖
      = (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have hmain : ‖coef a b c P Q x‖ ≤
      (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
        (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by
    rw [coef]
    calc ‖a (x.2 * x.1) * (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ) : ℂ))⁻¹ -
            b x.2 * c x.1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ) : ℂ))⁻¹‖
        ≤ ‖a (x.2 * x.1) * (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ) : ℂ))⁻¹‖ +
            ‖b x.2 * c x.1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ) : ℂ))⁻¹‖ :=
          norm_sub_le _ _
      _ ≤ 1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
            1 * 1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by
          apply add_le_add
          · rw [norm_mul, hnorm1]
            exact mul_le_mul_of_nonneg_right (ha _) (by positivity)
          · rw [norm_mul, norm_mul, hnorm2]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul (hb _) (hc _) (by positivity) (by norm_num)
      _ = (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
            (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by ring
  calc ‖coef a b c P Q x‖
      ≤ (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
          (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := hmain
    _ ≤ 2 / (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ) :=
        inv_add_inv_succ_le _ hr1
    _ = 2 / (Work.BMF.mrDirect.omegaCount P Q (freq x) : ℝ) := by rw [hfreq]

end Work.BMF.mr_direct
