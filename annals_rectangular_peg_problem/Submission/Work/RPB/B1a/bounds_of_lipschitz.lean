import Mathlib
import Submission.Work.RPB.B1a.HalfBallRegion

namespace Work.RPB.B1a

theorem bounds_of_lipschitz (g : ℝ → ℂ) (w : ℂ) (hw : w ≠ 0) (hg0 : g 0 = 0)
    (hdiff : ∀ x : ℝ, DifferentiableAt ℝ g x)
    {K δ r : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (hr : 0 < r) (hrδ : 2 * r ≤ δ)
    (hLip : ∀ x, |x| ≤ δ → ‖deriv g x - w‖ ≤ K * |x|) :
    Work.RPB.B1a.hRe g w 0 = 0 ∧ Work.RPB.B1a.hIm g w 0 = 0 ∧
      (∀ x, |x| ≤ 2 * r →
        HasDerivAt (Work.RPB.B1a.hRe g w) (Work.RPB.B1a.hDre g w x) x ∧
        HasDerivAt (Work.RPB.B1a.hIm g w) (Work.RPB.B1a.hDim g w x) x ∧
        |Work.RPB.B1a.hDre g w x| ≤ (K / ‖w‖) * |x| ∧
        |Work.RPB.B1a.hDim g w x - 1| ≤ (K / ‖w‖) * |x|) := by
  have hw_pos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨?_, ?_, ?_⟩
  · simp [Work.RPB.B1a.hRe, Work.RPB.B1a.hArg, hg0]
  · simp [Work.RPB.B1a.hIm, Work.RPB.B1a.hArg, hg0]
  · intro x hx
    have hxδ : |x| ≤ δ := le_trans hx hrδ
    have hmain : HasDerivAt (fun y => Complex.I * g y / w) (Complex.I * deriv g x / w) x :=
      ((hdiff x).hasDerivAt.const_mul Complex.I).div_const w
    have hfunRe : Work.RPB.B1a.hRe g w = fun y => (Complex.I * g y / w).re := by
      funext y; simp [Work.RPB.B1a.hRe, Work.RPB.B1a.hArg]
    have hfunIm : Work.RPB.B1a.hIm g w = fun y => (Complex.I * g y / w).im := by
      funext y; simp [Work.RPB.B1a.hIm, Work.RPB.B1a.hArg]
    have hre : HasDerivAt (Work.RPB.B1a.hRe g w) (Work.RPB.B1a.hDre g w x) x := by
      rw [hfunRe, Work.RPB.B1a.hDre]
      simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hmain
    have him : HasDerivAt (Work.RPB.B1a.hIm g w) (Work.RPB.B1a.hDim g w x) x := by
      rw [hfunIm, Work.RPB.B1a.hDim]
      simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hmain
    -- `hDre` and `hDim - 1` are the real and imaginary parts of the same complex number
    -- `I * (deriv g x - w) / w`, of norm `‖deriv g x - w‖ / ‖w‖`.
    have hsplit : Complex.I * deriv g x / w
        = Complex.I + Complex.I * (deriv g x - w) / w := by
      field_simp
      ring
    have hdre : Work.RPB.B1a.hDre g w x = (Complex.I * (deriv g x - w) / w).re := by
      simp only [Work.RPB.B1a.hDre]
      rw [hsplit]
      simp
    have hdim : Work.RPB.B1a.hDim g w x - 1 = (Complex.I * (deriv g x - w) / w).im := by
      simp only [Work.RPB.B1a.hDim]
      rw [hsplit]
      simp
    have hnorm : ‖Complex.I * (deriv g x - w) / w‖ = ‖deriv g x - w‖ / ‖w‖ := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul]
    have hbdre : |(Complex.I * (deriv g x - w) / w).re| ≤ (K / ‖w‖) * |x| :=
      calc |(Complex.I * (deriv g x - w) / w).re|
          ≤ ‖Complex.I * (deriv g x - w) / w‖ := Complex.abs_re_le_norm _
        _ = ‖deriv g x - w‖ / ‖w‖ := hnorm
        _ ≤ (K * |x|) / ‖w‖ := div_le_div_of_nonneg_right (hLip x hxδ) (le_of_lt hw_pos)
        _ = (K / ‖w‖) * |x| := by ring
    have hbdim : |(Complex.I * (deriv g x - w) / w).im| ≤ (K / ‖w‖) * |x| :=
      calc |(Complex.I * (deriv g x - w) / w).im|
          ≤ ‖Complex.I * (deriv g x - w) / w‖ := Complex.abs_im_le_norm _
        _ = ‖deriv g x - w‖ / ‖w‖ := hnorm
        _ ≤ (K * |x|) / ‖w‖ := div_le_div_of_nonneg_right (hLip x hxδ) (le_of_lt hw_pos)
        _ = (K / ‖w‖) * |x| := by ring
    exact ⟨hre, him, by rw [hdre]; exact hbdre, by rw [hdim]; exact hbdim⟩

end Work.RPB.B1a
