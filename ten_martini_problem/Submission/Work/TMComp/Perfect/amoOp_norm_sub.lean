import Mathlib
import Submission.Work.TMComp.PerfectDefs

open Work.TMContract

namespace Work.TMComp.Perfect

/-- The canonical almost Mathieu operator is Lipschitz in the phase `θ`, with constant `4π|λ|`. -/
theorem amoOp_norm_sub (α lam θ θ' : ℝ) :
    ‖Work.TMComp.Perfect.amoOp α lam θ - Work.TMComp.Perfect.amoOp α lam θ'‖
      ≤ 4 * Real.pi * |lam| * |θ - θ'| := by
  -- Pointwise bound on the difference of the potential values.
  have hK : ∀ n : ℤ, ‖potC α lam θ n - potC α lam θ' n‖ ≤ 4 * Real.pi * |lam| * |θ - θ'| := by
    intro n
    have hcnv : potC α lam θ n - potC α lam θ' n
        = (((amoPot α lam θ n - amoPot α lam θ' n : ℝ)) : ℂ) := by
      simp only [potC_apply, ← Complex.ofReal_sub]
    rw [hcnv, Complex.norm_real, Real.norm_eq_abs]
    have h1 : amoPot α lam θ n - amoPot α lam θ' n
        = 2 * lam * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α))) := by
      rw [amoPot, amoPot]; ring
    have harg : |2 * Real.pi * (θ + (n : ℝ) * α) - 2 * Real.pi * (θ' + (n : ℝ) * α)|
        = 2 * Real.pi * |θ - θ'| := by
      rw [show 2 * Real.pi * (θ + (n : ℝ) * α) - 2 * Real.pi * (θ' + (n : ℝ) * α)
            = 2 * Real.pi * (θ - θ') by ring,
        abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hcos : |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
        - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α))| ≤ 2 * Real.pi * |θ - θ'| := by
      rw [← harg]; exact Real.abs_cos_sub_cos_le _ _
    have hmain : |amoPot α lam θ n - amoPot α lam θ' n|
        ≤ 2 * |lam| * (2 * Real.pi * |θ - θ'|) := by
      rw [h1, abs_mul]
      have h2 : |(2 : ℝ) * lam| = 2 * |lam| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [h2]
      exact mul_le_mul_of_nonneg_left hcos (by positivity)
    calc |amoPot α lam θ n - amoPot α lam θ' n|
        ≤ 2 * |lam| * (2 * Real.pi * |θ - θ'|) := hmain
      _ = 4 * Real.pi * |lam| * |θ - θ'| := by ring
  -- The shifts cancel, leaving the diagonal operator with coefficients `potC θ - potC θ'`.
  have hdiff : amoOp α lam θ - amoOp α lam θ' =
      diag (fun n : ℤ => potC α lam θ n - potC α lam θ' n)
        (4 * Real.pi * |lam| * |θ - θ'|) hK := by
    simp only [amoOp]
    rw [add_sub_add_left_eq_sub,
      diag_sub (potC_bound α lam θ) (potC_bound α lam θ') hK]
  rw [hdiff]
  exact ContinuousLinearMap.opNorm_le_bound _
    (by positivity) (fun f => diag_norm_le _ _ _ f)

end Work.TMComp.Perfect
