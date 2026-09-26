/-
# Third-order cusp asymptotics of `Y = (ξ₄|₄S)E₈ - (ξ₂|₂S)E₁₀`

The quantity `Yfun` is a cusp form of weight `14` in the CKMRV residue calculus; at the cusp
`i∞` it vanishes to first order.  This file computes its expansion up to the third order.

The exact factorisation `Work.Residues.Yfun_eq`,

  `Yfun τ = V(τ) · S_Y (U(τ) - 1) (V(τ))`,

where `U = θ₀₀⁴`, `V = θ₁₀⁴` and `S_Y` is the explicit quotient polynomial, together with the
cusp expansions `U = 1 + 8E + 24E² + O(‖E‖³)` (`cusp_U_second`) and `V = 16E + O(‖E‖³)`
(`VFun_expansion`) gives the leading terms of `Y`.  Writing `G(x,y) = y·S_Y(x,y)`,
`a₀ = 8E + 24E²`, `b₀ = 16E`, the difference

  `G(a, b) - G(a₀, b₀)`

is controlled by a mean-value estimate on the fixed compact set `‖(x,y)‖ ≤ M`, whose derivative
bound is supplied by compactness (no explicit constant is needed), while the purely `E`-dependent
remainder `G(a₀,b₀) - (72E - 576E²) = E³·YfunPsi3(E)` is an explicit polynomial identity checked
by `ring`.  The conclusion is

  `Yfun τ = 72 E(τ) - 576 E(τ)² + O(‖E(τ)‖³)`.
-/
import Mathlib
import Submission.Work.Asymptotics.cusp_U_second
import Submission.Work.Residues.KMinusCuspDefs

open UpperHalfPlane

namespace Work.Asymptotics

noncomputable section

/-- The polynomial map `G(x,y) = y · S_Y(x,y)`, so that `Yfun = G(U-1, V)` by
`Work.Residues.Yfun_eq`. -/
def YfunGpoly (p : ℂ × ℂ) : ℂ := p.2 * Work.Residues.S_Y p.1 p.2

/-- The residual polynomial of the cusp expansion of `Y`, characterised by
`16z·S_Y(8z+24z²) (16z) - (72z - 576z²) = z³·YfunPsi3 z`. -/
def YfunPsi3 (z : ℂ) : ℂ :=
  17856 - 129024 * z + 193536 * z ^ 2 + 1548288 * z ^ 3 + 4644864 * z ^ 4
    - 74317824 * z ^ 5 + 246841344 * z ^ 6 - 191102976 * z ^ 7 + 573308928 * z ^ 8

lemma contDiff_YfunGpoly : ContDiff ℝ ⊤ YfunGpoly := by
  unfold YfunGpoly Work.Residues.S_Y
  fun_prop

lemma YfunPsi3_spec (z : ℂ) :
    16 * z * Work.Residues.S_Y (8 * z + 24 * z ^ 2) (16 * z) - (72 * z - 576 * z ^ 2)
      = z ^ 3 * YfunPsi3 z := by
  unfold YfunPsi3 Work.Residues.S_Y
  ring

theorem Yfun_third_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Residues.Yfun τ
        - (72 * Work.Residues.Ept τ - 576 * (Work.Residues.Ept τ) ^ 2)‖
        ≤ C * ‖Work.Residues.Ept τ‖ ^ 3 := by
  obtain ⟨CA, hCA, hU⟩ := cusp_U_second
  obtain ⟨CB, hCB, hV⟩ := Work.Residues.VFun_expansion
  -- A bound for the residual polynomial `YfunPsi3` on the closed unit disc.
  have hPsi3cont : Continuous YfunPsi3 := by unfold YfunPsi3; fun_prop
  obtain ⟨K0, hK0⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hPsi3cont.continuousOn
  have hK0' : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖YfunPsi3 z‖ ≤ K0 := by
    intro z hz
    exact hK0 z (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz)
  have hK00 : 0 ≤ K0 := le_trans (norm_nonneg _)
    (hK0 0 (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_zero]; norm_num))
  -- A bound for the derivative of `G` on the fixed compact ball of radius `Ma + Mb`.
  have hGdiff : Differentiable ℝ YfunGpoly := by
    unfold YfunGpoly Work.Residues.S_Y; fun_prop
  have hfdcont : Continuous (fderiv ℝ YfunGpoly) :=
    contDiff_YfunGpoly.continuous_fderiv (by simp)
  set Ma : ℝ := 32 + CA with hMa_def
  set Mb : ℝ := 16 + CB with hMb_def
  have hMa : 0 < Ma := by rw [hMa_def]; linarith
  have hMb : 0 < Mb := by rw [hMb_def]; linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ × ℂ) (Ma + Mb)).exists_bound_of_continuousOn
    hfdcont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM 0 (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_zero]; linarith [hMa, hMb]))
  refine ⟨M * (CA + CB) + K0 + 1, by nlinarith [hM0, hK00, hCA, hCB], fun τ hτ => ?_⟩
  set e : ℂ := Work.Residues.Ept τ with he
  have he_le : ‖e‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
  have he0 : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  set a : ℂ := Work.Residues.acusp τ with ha
  set b : ℂ := Work.Residues.bcusp τ with hb
  set a0 : ℂ := 8 * e + 24 * e ^ 2 with ha0
  set b0 : ℂ := 16 * e with hb0
  have hY : Work.Residues.Yfun τ = YfunGpoly (a, b) := by
    rw [Work.Residues.Yfun_eq, ha, hb]; rfl
  -- The two expansions `U - 1 = a₀ + A`, `V = b₀ + B` with `A, B = O(‖E‖³)`.
  have hA : ‖a - a0‖ ≤ CA * ‖e‖ ^ 3 := by
    rw [ha, ha0, he]
    have hkey : Work.Residues.acusp τ - (8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2)
        = Work.Kernels.UFun τ - (1 + 8 * Work.Residues.Ept τ
            + 24 * Work.Residues.Ept τ ^ 2) := by
      simp only [Work.Residues.acusp]; ring
    rw [hkey]
    exact hU τ hτ
  have hB : ‖b - b0‖ ≤ CB * ‖e‖ ^ 3 := by
    rw [hb, hb0, he]
    exact hV τ hτ
  -- Membership of the two points in the fixed compact ball.
  have ha0n : ‖a0‖ ≤ 32 := by
    have h1 : ‖(24 : ℂ) * e ^ 2‖ = 24 * ‖e‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h2 : ‖(8 : ℂ) * e‖ = 8 * ‖e‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h3 := norm_add_le ((8 : ℂ) * e) ((24 : ℂ) * e ^ 2)
    rw [h2, h1] at h3
    have he2 : ‖e‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [h3, he0, he2]
  have hb0n : ‖b0‖ ≤ 16 := by
    have h1 : ‖(16 : ℂ) * e‖ = 16 * ‖e‖ := by rw [norm_mul, Complex.norm_ofNat]
    rw [h1]; nlinarith
  have han : ‖a‖ ≤ Ma := by
    have h1 : ‖a‖ ≤ ‖a0‖ + ‖a - a0‖ := by
      have := norm_add_le a0 (a - a0); rw [add_sub_cancel] at this; exact this
    have h2 : ‖a - a0‖ ≤ CA := le_trans hA
      (by nlinarith [pow_le_pow_of_le_one he0 he_le (by norm_num : 1 ≤ 3), hCA])
    rw [hMa_def]; linarith
  have hbn : ‖b‖ ≤ Mb := by
    have h1 : ‖b‖ ≤ ‖b0‖ + ‖b - b0‖ := by
      have := norm_add_le b0 (b - b0); rw [add_sub_cancel] at this; exact this
    have h2 : ‖b - b0‖ ≤ CB := le_trans hB
      (by nlinarith [pow_le_pow_of_le_one he0 he_le (by norm_num : 1 ≤ 3), hCB])
    rw [hMb_def]; linarith
  have hmem1 : (a, b) ∈ Metric.closedBall (0 : ℂ × ℂ) (Ma + Mb) := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
    exact max_le (le_trans han (by linarith)) (le_trans hbn (by linarith))
  have hmem2 : (a0, b0) ∈ Metric.closedBall (0 : ℂ × ℂ) (Ma + Mb) := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
    exact max_le (by linarith [ha0n, hMa]) (by linarith [hb0n, hMb])
  -- Mean-value estimate: `G(a,b) - G(a₀,b₀) = O(‖E‖³)`.
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := YfunGpoly) (s := Metric.closedBall (0 : ℂ × ℂ) (Ma + Mb))
    (f' := fun p => fderiv ℝ YfunGpoly p) (C := M)
    (fun x hx => (hGdiff x).hasFDerivAt.hasFDerivWithinAt)
    (fun x hx => hM x hx)
    (convex_closedBall _ _) hmem2 hmem1
  have hdist : ‖(a, b) - (a0, b0)‖ ≤ (CA + CB) * ‖e‖ ^ 3 := by
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub]
    calc max ‖a - a0‖ ‖b - b0‖ ≤ ‖a - a0‖ + ‖b - b0‖ :=
          max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
      _ ≤ CA * ‖e‖ ^ 3 + CB * ‖e‖ ^ 3 := add_le_add hA hB
      _ = (CA + CB) * ‖e‖ ^ 3 := by ring
  have hpart1 : ‖YfunGpoly (a, b) - YfunGpoly (a0, b0)‖ ≤ M * (CA + CB) * ‖e‖ ^ 3 := by
    calc ‖YfunGpoly (a, b) - YfunGpoly (a0, b0)‖ ≤ M * ‖(a, b) - (a0, b0)‖ := hmvt
      _ ≤ M * ((CA + CB) * ‖e‖ ^ 3) := mul_le_mul_of_nonneg_left hdist hM0
      _ = M * (CA + CB) * ‖e‖ ^ 3 := by ring
  -- The purely `E`-dependent remainder.
  have hpart2 : ‖YfunGpoly (a0, b0) - (72 * e - 576 * e ^ 2)‖ ≤ K0 * ‖e‖ ^ 3 := by
    have hid : YfunGpoly (a0, b0) - (72 * e - 576 * e ^ 2) = e ^ 3 * YfunPsi3 e := by
      simp only [YfunGpoly, ha0, hb0]
      exact YfunPsi3_spec e
    rw [hid, norm_mul, norm_pow]
    calc ‖e‖ ^ 3 * ‖YfunPsi3 e‖ ≤ ‖e‖ ^ 3 * K0 :=
          mul_le_mul_of_nonneg_left (hK0' e he_le) (pow_nonneg he0 3)
      _ = K0 * ‖e‖ ^ 3 := by ring
  have hmain : ‖Work.Residues.Yfun τ - (72 * e - 576 * e ^ 2)‖
      ≤ (M * (CA + CB) + K0) * ‖e‖ ^ 3 := by
    rw [hY]
    have hsplit : YfunGpoly (a, b) - (72 * e - 576 * e ^ 2)
        = (YfunGpoly (a, b) - YfunGpoly (a0, b0))
          + (YfunGpoly (a0, b0) - (72 * e - 576 * e ^ 2)) := by ring
    rw [hsplit]
    calc ‖(YfunGpoly (a, b) - YfunGpoly (a0, b0))
            + (YfunGpoly (a0, b0) - (72 * e - 576 * e ^ 2))‖
        ≤ ‖YfunGpoly (a, b) - YfunGpoly (a0, b0)‖
            + ‖YfunGpoly (a0, b0) - (72 * e - 576 * e ^ 2)‖ := norm_add_le _ _
      _ ≤ M * (CA + CB) * ‖e‖ ^ 3 + K0 * ‖e‖ ^ 3 := add_le_add hpart1 hpart2
      _ = (M * (CA + CB) + K0) * ‖e‖ ^ 3 := by ring
  rw [he] at hmain ⊢
  refine le_trans hmain ?_
  have hq : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 3 := pow_nonneg (norm_nonneg _) 3
  nlinarith [hq]

end

end Work.Asymptotics
