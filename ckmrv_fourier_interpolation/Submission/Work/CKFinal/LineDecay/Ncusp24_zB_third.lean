import Mathlib
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Kernels.Kernels

namespace Work.CKFinal.LineDecay

/-!
# Third-order vanishing at the cusp of the `z`-atom `E₁₀(U² − W²) − 2E₄³V`

This file proves

  `‖E₁₀(z)(U(z)² − W(z)²) − 2E₄(z)³V(z)‖ ≤ C e^{−3π Im z}`   for `Im z ≥ 1/3`,

used in the `z`-part of the control of the `K₋` funnel tails for `d = 24`.

The point is that the two summands are only `O(e^{−π Im z})` individually (they both vanish at
the cusp `i∞` to first order), but their *difference* vanishes to third order.  The mechanism is
the exact classical theta identity.  With `U = W + V` (Jacobi, `TildeFacts.theta_quartic`) and

  `E₄ = (U² + V² + W²)/2`,  `E₆ = (W − V)(V² + W² + (5/2)VW)`

(`Residues.KMinusT_E4Fun_eq_theta`, `TildeFacts.E6Fun_eq_theta`) one has, since `E₁₀ = E₄E₆`,

  `E₁₀(U² − W²) − 2E₄³V = −(3/2)·E₄·V³·(2V² + 5VW + 5W²)`,

and the right-hand side is visibly `O(V³) = O(e^{−3π Im z})` because `E₄` and `W` are bounded on
`{Im z ≥ 1/3}` while `V = O(e^{−π Im z})`.
-/

theorem Ncusp24_zB_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.E10Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)
          - 2 * Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z‖
        ≤ C * Real.exp (-(Real.pi * z.im)) ^ 3 := by
  obtain ⟨cE4, hcE4, hE4⟩ := Work.Asymptotics.E4Fun_bound_third
  obtain ⟨cW, hcW, hW⟩ := Work.Asymptotics.WFun_sub_one_le_third
  obtain ⟨cV, hcV, hV⟩ := Work.Asymptotics.VFun_bound_third
  refine ⟨(3 / 2) * cE4 * cV ^ 3 * (2 * cV ^ 2 + 5 * cV * (1 + cW) + 5 * (1 + cW) ^ 2) + 1,
    by positivity, fun z hz => ?_⟩
  set t : ℝ := Real.exp (-(Real.pi * z.im)) with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact (Real.exp_pos _).le
  have ht1 : t ≤ 1 := by
    rw [ht]; exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])
  have hVz : ‖Work.Kernels.VFun z‖ ≤ cV * t := hV z hz
  have hWz : ‖Work.Kernels.WFun z‖ ≤ 1 + cW := by
    have h := hW z hz
    have h2 := norm_add_le (Work.Kernels.WFun z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h2
    calc ‖Work.Kernels.WFun z‖ ≤ ‖Work.Kernels.WFun z - 1‖ + 1 := h2
      _ ≤ cW * t + 1 := by linarith
      _ ≤ cW * 1 + 1 := by nlinarith [hcW, ht1]
      _ = 1 + cW := by ring
  have hE4z := hE4 z hz
  -- The exact theta identity behind the third-order vanishing.
  have key : Work.Kernels.E10Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)
        - 2 * Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z
      = -(3 / 2) * Work.Kernels.E4Fun z * Work.Kernels.VFun z ^ 3
          * (2 * Work.Kernels.VFun z ^ 2 + 5 * Work.Kernels.VFun z * Work.Kernels.WFun z
              + 5 * Work.Kernels.WFun z ^ 2) := by
    simp only [Work.Kernels.E10Fun]
    rw [Work.Residues.KMinusT_E4Fun_eq_theta z,
        Work.Kernels.TildeFacts.E6Fun_eq_theta z,
        Work.Kernels.TildeFacts.theta_quartic z]
    ring
  rw [key]
  have hnorm : ‖-(3 / 2) * Work.Kernels.E4Fun z * Work.Kernels.VFun z ^ 3
          * (2 * Work.Kernels.VFun z ^ 2 + 5 * Work.Kernels.VFun z * Work.Kernels.WFun z
              + 5 * Work.Kernels.WFun z ^ 2)‖
      = (3 / 2) * ‖Work.Kernels.E4Fun z‖ * ‖Work.Kernels.VFun z‖ ^ 3
          * ‖2 * Work.Kernels.VFun z ^ 2 + 5 * Work.Kernels.VFun z * Work.Kernels.WFun z
              + 5 * Work.Kernels.WFun z ^ 2‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg]
    norm_num
  rw [hnorm]
  -- `‖2V² + 5VW + 5W²‖` is bounded by its value at the cusp.
  have hIn : ‖2 * Work.Kernels.VFun z ^ 2 + 5 * Work.Kernels.VFun z * Work.Kernels.WFun z
        + 5 * Work.Kernels.WFun z ^ 2‖
      ≤ 2 * (cV * t) ^ 2 + 5 * (cV * t) * (1 + cW) + 5 * (1 + cW) ^ 2 := by
    have n1 : ‖2 * Work.Kernels.VFun z ^ 2‖ = 2 * ‖Work.Kernels.VFun z‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have n2 : ‖5 * Work.Kernels.VFun z * Work.Kernels.WFun z‖
        = 5 * ‖Work.Kernels.VFun z‖ * ‖Work.Kernels.WFun z‖ := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have n3 : ‖5 * Work.Kernels.WFun z ^ 2‖ = 5 * ‖Work.Kernels.WFun z‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have s2 := norm_add_le
      (2 * Work.Kernels.VFun z ^ 2 + 5 * Work.Kernels.VFun z * Work.Kernels.WFun z)
      (5 * Work.Kernels.WFun z ^ 2)
    have s1 := norm_add_le
      (2 * Work.Kernels.VFun z ^ 2) (5 * Work.Kernels.VFun z * Work.Kernels.WFun z)
    rw [n1, n2] at s1
    rw [n3] at s2
    nlinarith [s1, s2, norm_nonneg (Work.Kernels.VFun z), norm_nonneg (Work.Kernels.WFun z),
      hVz, hWz]
  have hV3 : ‖Work.Kernels.VFun z‖ ^ 3 ≤ (cV * t) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hVz 3
  have step1 : (3 / 2) * ‖Work.Kernels.E4Fun z‖ * ‖Work.Kernels.VFun z‖ ^ 3
      ≤ (3 / 2) * cE4 * (cV * t) ^ 3 := by
    have h1 : (3 / 2) * ‖Work.Kernels.E4Fun z‖ ≤ (3 / 2) * cE4 :=
      mul_le_mul_of_nonneg_left hE4z (by norm_num)
    exact mul_le_mul h1 hV3 (pow_nonneg (norm_nonneg _) 3) (by positivity)
  have step2 : (3 / 2) * ‖Work.Kernels.E4Fun z‖ * ‖Work.Kernels.VFun z‖ ^ 3
        * ‖2 * Work.Kernels.VFun z ^ 2 + 5 * Work.Kernels.VFun z * Work.Kernels.WFun z
              + 5 * Work.Kernels.WFun z ^ 2‖
      ≤ ((3 / 2) * cE4 * (cV * t) ^ 3)
        * (2 * (cV * t) ^ 2 + 5 * (cV * t) * (1 + cW) + 5 * (1 + cW) ^ 2) :=
    mul_le_mul step1 hIn (norm_nonneg _) (by positivity)
  have step3 : 2 * (cV * t) ^ 2 + 5 * (cV * t) * (1 + cW) + 5 * (1 + cW) ^ 2
      ≤ 2 * cV ^ 2 + 5 * cV * (1 + cW) + 5 * (1 + cW) ^ 2 := by
    have hct : cV * t ≤ cV := by nlinarith [ht1, hcV.le]
    have hct2 : (cV * t) ^ 2 ≤ cV ^ 2 := pow_le_pow_left₀ (by positivity) hct 2
    have hm : (cV * t) * (1 + cW) ≤ cV * (1 + cW) :=
      mul_le_mul_of_nonneg_right hct (by linarith)
    nlinarith [hct2, hm]
  have step4 : ((3 / 2) * cE4 * (cV * t) ^ 3)
        * (2 * (cV * t) ^ 2 + 5 * (cV * t) * (1 + cW) + 5 * (1 + cW) ^ 2)
      ≤ ((3 / 2) * cE4 * cV ^ 3 * (2 * cV ^ 2 + 5 * cV * (1 + cW) + 5 * (1 + cW) ^ 2) + 1)
        * t ^ 3 := by
    have h0 : 0 ≤ (3 / 2) * cE4 * (cV * t) ^ 3 := by positivity
    have h1 := mul_le_mul_of_nonneg_left step3 h0
    calc ((3 / 2) * cE4 * (cV * t) ^ 3)
          * (2 * (cV * t) ^ 2 + 5 * (cV * t) * (1 + cW) + 5 * (1 + cW) ^ 2)
        ≤ ((3 / 2) * cE4 * (cV * t) ^ 3)
          * (2 * cV ^ 2 + 5 * cV * (1 + cW) + 5 * (1 + cW) ^ 2) := h1
      _ = (3 / 2) * cE4 * cV ^ 3
            * (2 * cV ^ 2 + 5 * cV * (1 + cW) + 5 * (1 + cW) ^ 2) * t ^ 3 := by
          ring
      _ ≤ ((3 / 2) * cE4 * cV ^ 3
            * (2 * cV ^ 2 + 5 * cV * (1 + cW) + 5 * (1 + cW) ^ 2) + 1) * t ^ 3 := by
          nlinarith [pow_nonneg ht0 3]
  exact le_trans step2 step4

end Work.CKFinal.LineDecay
