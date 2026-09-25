import Mathlib
import Submission.Work.NN.Ratio.Setup
import Submission.Work.NN.Newton.ThinProfile.smoothTransitionConstants
import Submission.Work.NN.Newton.ThinProfile.lipschitz_radial_field
import Submission.Work.NN.Newton.ThinProfile.abs_le_of_radial_scalar

namespace Work.NN.Newton.ThinProfile

open scoped NNReal ENNReal ContDiff
open Set

/-- The one-variable derivative of the radial profile `rCutR`, in the form used below. -/
private lemma deriv_rCutR_eq_formula (a b s : ℝ) :
    deriv (Work.NN.Ratio.rCutR a b) s
      = -(deriv Real.smoothTransition ((b ^ 2 - s) / (b ^ 2 - a ^ 2)) * (b ^ 2 - a ^ 2)⁻¹) := by
  unfold Work.NN.Ratio.rCutR
  have hu : HasDerivAt (fun s : ℝ => (b ^ 2 - s) / (b ^ 2 - a ^ 2))
      (-(b ^ 2 - a ^ 2)⁻¹) s := by
    have h : (fun s : ℝ => (b ^ 2 - s) / (b ^ 2 - a ^ 2))
        = fun s : ℝ => (b ^ 2 - s) * (b ^ 2 - a ^ 2)⁻¹ := by
      funext s; rw [div_eq_mul_inv]
    rw [h]
    have := ((hasDerivAt_const (x := s) (c := b ^ 2)).sub (hasDerivAt_id s)).mul_const
      ((b ^ 2 - a ^ 2)⁻¹)
    simpa using this
  have hσ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((b ^ 2 - s) / (b ^ 2 - a ^ 2)))
      ((b ^ 2 - s) / (b ^ 2 - a ^ 2)) := by
    have hd : DifferentiableAt ℝ Real.smoothTransition ((b ^ 2 - s) / (b ^ 2 - a ^ 2)) :=
      (Real.smoothTransition.contDiffAt (n := (2 : ℕ∞))).differentiableAt (by norm_num)
    exact hd.hasDerivAt
  simpa [Function.comp_def] using (hσ.comp s hu).deriv

private lemma norm_ofReal_coe (x : ℝ) : ‖((x : ℂ))‖ = |x| := by
  simpa [Real.norm_eq_abs] using Complex.ofRealLI.norm_map x

private lemma norm_ofReal_sub (x y : ℝ) : ‖((x : ℂ) - (y : ℂ))‖ = |x - y| := by
  rw [← Complex.ofReal_sub]
  exact norm_ofReal_coe (x - y)


theorem thinProfile :
    ∃ K : ℝ, 0 < K ∧ ∀ a b : ℝ, 1 / 4 ≤ a → a < b → b ≤ 8 →
      ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧
        (∀ ζ : ℂ, ‖ζ‖ ≤ a → χ ζ = 1) ∧
        (∀ ζ : ℂ, b ≤ ‖ζ‖ → χ ζ = 0) ∧
        (∀ ζ : ℂ, ‖χ ζ‖ ≤ 1) ∧
        (∀ ζ : ℂ, ‖ζ‖ ≤ a → Work.CR.Flat.dbarC χ ζ = 0) ∧
        (∀ ζ : ℂ, b ≤ ‖ζ‖ → Work.CR.Flat.dbarC χ ζ = 0) ∧
        (∀ ζ : ℂ, ‖Work.CR.Flat.dbarC χ ζ‖ ≤ K / (b - a)) ∧
        (∀ ζ ζ' : ℂ, ‖Work.CR.Flat.dbarC χ ζ - Work.CR.Flat.dbarC χ ζ'‖ ≤
          K / (b - a) ^ 2 * ‖ζ - ζ'‖) ∧
        (∀ ζ ζ' : ℂ, ‖χ ζ - χ ζ'‖ ≤ K / (b - a) * ‖ζ - ζ'‖) := by
  obtain ⟨M0, M1, hM0, hM1, hσ_bd, hσ_lip, hσ'_lip, hσ'0⟩ := smoothTransitionConstants
  refine ⟨1024 * (M0 + M1 + 1), by nlinarith, ?_⟩
  intro a b ha hab hb
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hbpos : 0 < b := by linarith
  have hbma : 0 < b - a := by linarith
  have hbma8 : b - a ≤ 8 := by linarith
  have hApos : 0 < b ^ 2 - a ^ 2 := by
    have h : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    rw [h]
    exact mul_pos (by linarith) (by linarith)
  set c : ℝ := (b ^ 2 - a ^ 2)⁻¹ with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; exact inv_nonneg.mpr hApos.le
  have hcinv : (b ^ 2 - a ^ 2)⁻¹ = c := hcdef.symm
  have hc_mul : c * (b - a) ≤ 2 := by
    rw [hcdef, mul_comm, ← div_eq_mul_inv, div_le_iff₀ hApos]
    have h : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    rw [h]
    have h1 : (1 : ℝ) ≤ 2 * (b + a) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hbma.le]
  have hc_sq : (c * (b - a)) ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (mul_nonneg hc0 hbma.le) hc_mul 2
    norm_num at h
    exact h
  have hdsig : ∀ s : ℝ, deriv (Work.NN.Ratio.rCutR a b) s
      = -(deriv Real.smoothTransition (c * (b ^ 2 - s)) * c) := by
    intro s
    rw [deriv_rCutR_eq_formula a b s]
    have harg : (b ^ 2 - s) / (b ^ 2 - a ^ 2) = c * (b ^ 2 - s) := by
      rw [div_eq_mul_inv, mul_comm (b ^ 2 - s) (b ^ 2 - a ^ 2)⁻¹, ← hcdef]
    rw [harg, hcinv]
  have hFb1 : ∀ s : ℝ, |deriv (Work.NN.Ratio.rCutR a b) s| ≤ M0 * c := by
    intro s
    rw [hdsig s, abs_neg, abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_right (hσ_bd _) hc0
  have hFb2 : ∀ s : ℝ, |deriv (Work.NN.Ratio.rCutR a b) s| ≤ M1 * c ^ 2 * |b ^ 2 - s| := by
    intro s
    rw [hdsig s, abs_neg, abs_mul, abs_of_nonneg hc0]
    have h : |deriv Real.smoothTransition (c * (b ^ 2 - s))|
        ≤ M1 * |c * (b ^ 2 - s)| := by
      have h0 := hσ'_lip (c * (b ^ 2 - s)) 0
      simpa [hσ'0] using h0
    calc |deriv Real.smoothTransition (c * (b ^ 2 - s))| * c
        ≤ (M1 * |c * (b ^ 2 - s)|) * c := mul_le_mul_of_nonneg_right h hc0
      _ = M1 * c ^ 2 * |b ^ 2 - s| := by rw [abs_mul, abs_of_nonneg hc0]; ring
  have hFlip : ∀ s s' : ℝ,
      |deriv (Work.NN.Ratio.rCutR a b) s - deriv (Work.NN.Ratio.rCutR a b) s'|
        ≤ M1 * c ^ 2 * |s - s'| := by
    intro s s'
    rw [hdsig s, hdsig s']
    have heq : -(deriv Real.smoothTransition (c * (b ^ 2 - s)) * c)
        - -(deriv Real.smoothTransition (c * (b ^ 2 - s')) * c)
        = -((deriv Real.smoothTransition (c * (b ^ 2 - s))
            - deriv Real.smoothTransition (c * (b ^ 2 - s'))) * c) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_nonneg hc0]
    have h := hσ'_lip (c * (b ^ 2 - s)) (c * (b ^ 2 - s'))
    calc |deriv Real.smoothTransition (c * (b ^ 2 - s))
            - deriv Real.smoothTransition (c * (b ^ 2 - s'))| * c
        ≤ (M1 * |c * (b ^ 2 - s) - c * (b ^ 2 - s')|) * c :=
          mul_le_mul_of_nonneg_right h hc0
      _ = M1 * c ^ 2 * |s - s'| := by
          have h1 : c * (b ^ 2 - s) - c * (b ^ 2 - s') = c * (s' - s) := by ring
          rw [h1, abs_mul, abs_of_nonneg hc0, abs_sub_comm]
          ring
  have hFz : ∀ s : ℝ, b ^ 2 ≤ s → deriv (Work.NN.Ratio.rCutR a b) s = 0 :=
    fun s hs => Work.NN.Ratio.deriv_rCutR_eq_zero_of_le' ha0 hab hs
  refine ⟨Work.NN.Ratio.rCut a b, Work.NN.Ratio.contDiff_rCut a b,
    fun ζ h => Work.NN.Ratio.rCut_eq_one_of_norm_le ha0 hab h,
    fun ζ h => Work.NN.Ratio.rCut_eq_zero_of_le_norm ha0 hab h,
    fun ζ => Work.NN.Ratio.norm_rCut_le_one a b ζ,
    fun ζ h => Work.NN.Ratio.dbarC_rCut_eq_zero_of_norm_le ha0 hab h,
    fun ζ h => Work.NN.Ratio.dbarC_rCut_eq_zero_of_le_norm ha0 hab h,
    ?_, ?_, ?_⟩
  · intro ζ
    rw [Work.NN.Ratio.dbarC_rCut_eq a b ζ]
    rw [norm_mul, norm_ofReal_coe, le_div_iff₀ hbma]
    by_cases hζ : ‖ζ‖ ≤ b
    · have h1 : |deriv (Work.NN.Ratio.rCutR a b) (Complex.normSq ζ)| * ‖ζ‖ ≤ M0 * c * b :=
        mul_le_mul (hFb1 _) hζ (norm_nonneg _) (mul_nonneg hM0 hc0)
      have h2 : M0 * c * b * (b - a) ≤ 16 * M0 := by
        have he : M0 * c * b * (b - a) = M0 * b * (c * (b - a)) := by ring
        rw [he]
        have h3 : M0 * b * (c * (b - a)) ≤ M0 * 8 * 2 := by gcongr
        nlinarith
      nlinarith [h1, h2, hM0, hM1]
    · simp only [not_le] at hζ
      have hz : deriv (Work.NN.Ratio.rCutR a b) (Complex.normSq ζ) = 0 := by
        refine Work.NN.Ratio.deriv_rCutR_eq_zero_of_le' ha0 hab ?_
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ hb0 hζ.le 2
      rw [hz]
      simp only [abs_zero, zero_mul]
      nlinarith [hM0, hM1]
  · intro ζ ζ'
    rw [Work.NN.Ratio.dbarC_rCut_eq a b ζ, Work.NN.Ratio.dbarC_rCut_eq a b ζ']
    have h := lipschitz_radial_field (F := fun s => deriv (Work.NN.Ratio.rCutR a b) s)
      (b := b) (M0 := M0) (M1 := M1) (c := c) hbpos hM0 hM1 hc0 hFb1 hFb2 hFlip hFz ζ ζ'
    refine h.trans ?_
    have hK : M0 * c + 2 * b ^ 2 * M1 * c ^ 2
        ≤ 1024 * (M0 + M1 + 1) / (b - a) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (b - a) ^ 2)]
      have h1 : M0 * c * (b - a) ^ 2 ≤ 16 * M0 := by
        have he : M0 * c * (b - a) ^ 2 = M0 * (b - a) * (c * (b - a)) := by ring
        rw [he]
        have h3 : M0 * (b - a) * (c * (b - a)) ≤ M0 * 8 * 2 := by gcongr
        nlinarith
      have h2 : 2 * b ^ 2 * M1 * c ^ 2 * (b - a) ^ 2 ≤ 512 * M1 := by
        have he : 2 * b ^ 2 * M1 * c ^ 2 * (b - a) ^ 2
            = 2 * b ^ 2 * M1 * (c * (b - a)) ^ 2 := by ring
        rw [he]
        have hb2 : b ^ 2 ≤ 64 := by nlinarith
        have h3 : 2 * b ^ 2 * M1 * (c * (b - a)) ^ 2 ≤ 2 * 64 * M1 * 4 := by gcongr
        nlinarith
      nlinarith [h1, h2, hM0, hM1]
    exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  · intro ζ ζ'
    have hχ : ∀ ζ : ℂ, Work.NN.Ratio.rCut a b ζ
        = (((Real.smoothTransition (c * (b ^ 2 - Complex.normSq ζ))) : ℝ) : ℂ) := by
      intro ζ
      have harg : (b ^ 2 - Complex.normSq ζ) / (b ^ 2 - a ^ 2)
          = c * (b ^ 2 - Complex.normSq ζ) := by
        rw [div_eq_mul_inv, mul_comm (b ^ 2 - Complex.normSq ζ) (b ^ 2 - a ^ 2)⁻¹, ← hcdef]
      rw [Work.NN.Ratio.rCut, Work.NN.Ratio.rCutR, harg]
    rw [hχ ζ, hχ ζ']
    rw [norm_ofReal_sub]
    have hz : ∀ s : ℝ, b ^ 2 ≤ s → Real.smoothTransition (c * (b ^ 2 - s)) = 0 := by
      intro s hs
      refine Real.smoothTransition.zero_of_nonpos ?_
      exact mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
    have h := abs_le_of_radial_scalar (b := b) (M := M0) (c := c) hbpos hM0 hc0 hσ_lip hz ζ ζ'
    refine h.trans ?_
    have hK : 2 * b * M0 * c ≤ 1024 * (M0 + M1 + 1) / (b - a) := by
      rw [le_div_iff₀ hbma]
      have he : 2 * b * M0 * c * (b - a) = 2 * b * M0 * (c * (b - a)) := by ring
      rw [he]
      have h3 : 2 * b * M0 * (c * (b - a)) ≤ 2 * 8 * M0 * 2 := by gcongr
      nlinarith
    exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)

end Work.NN.Newton.ThinProfile
