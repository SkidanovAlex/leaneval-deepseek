import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-- **Discrete Cauchy–Schwarz for a weighted sum of square-root products.**  If each term of a
family `x` is dominated by `C γ * √(a γ) * √(b γ)` with the weights `C γ` nonnegative, then the
absolute value of the total sum is dominated by `(∑ C) * √(∑ a) * √(∑ b)`.

This is the arithmetic content of `sum_pairing_le`: the triangle inequality, the Cauchy–Schwarz
inequality `∑ √(a γ) √(b γ) ≤ √(∑ a) √(∑ b)` (`Real.sum_sqrt_mul_sqrt_le`), and the observation
that every single weight is at most the total weight `∑ C` (which needs `C ≥ 0`). -/
theorem abs_sum_le_sum_mul_sqrt {κ : Type*} [Fintype κ] (x C a b : κ → ℝ)
    (hC : ∀ γ, 0 ≤ C γ) (ha : ∀ γ, 0 ≤ a γ) (hb : ∀ γ, 0 ≤ b γ)
    (hx : ∀ γ, |x γ| ≤ C γ * Real.sqrt (a γ) * Real.sqrt (b γ)) :
    |∑ γ, x γ| ≤ (∑ γ, C γ) * Real.sqrt (∑ γ, a γ) * Real.sqrt (∑ γ, b γ) := by
  have hSnn : 0 ≤ ∑ γ, C γ := Finset.sum_nonneg fun γ _ => hC γ
  have hsqrtnn : ∀ γ, 0 ≤ Real.sqrt (a γ) * Real.sqrt (b γ) :=
    fun γ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |∑ γ, x γ| ≤ ∑ γ, |x γ| := Finset.abs_sum_le_sum_abs x Finset.univ
    _ ≤ ∑ γ, C γ * Real.sqrt (a γ) * Real.sqrt (b γ) :=
        Finset.sum_le_sum fun γ _ => hx γ
    _ ≤ ∑ γ, (∑ γ, C γ) * (Real.sqrt (a γ) * Real.sqrt (b γ)) := by
        refine Finset.sum_le_sum fun γ _ => ?_
        have hCle : C γ ≤ ∑ γ, C γ :=
          Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ γ)
        calc C γ * Real.sqrt (a γ) * Real.sqrt (b γ)
            = C γ * (Real.sqrt (a γ) * Real.sqrt (b γ)) := by ring
          _ ≤ (∑ γ, C γ) * (Real.sqrt (a γ) * Real.sqrt (b γ)) :=
              mul_le_mul_of_nonneg_right hCle (hsqrtnn γ)
    _ = (∑ γ, C γ) * ∑ γ, Real.sqrt (a γ) * Real.sqrt (b γ) := by
        rw [Finset.mul_sum]
    _ ≤ (∑ γ, C γ) * (Real.sqrt (∑ γ, a γ) * Real.sqrt (∑ γ, b γ)) :=
        mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Finset.univ ha hb) hSnn
    _ = (∑ γ, C γ) * Real.sqrt (∑ γ, a γ) * Real.sqrt (∑ γ, b γ) := by ring

theorem sum_pairing_le {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
    (d : ℕ) (hd : 1 ≤ d)
    (T : κ → Work.Diff.STE.B3.VarCoef.Op ι) (C : κ → ℝ) (hC : ∀ γ, 0 ≤ C γ)
    (hT : ∀ (γ : κ) (F U : (ι → ℝ) → ℂ), Work.Diff.STE.B3.VarCoef.SmoothPer F →
      Work.Diff.STE.B3.VarCoef.SmoothPer U →
      |Work.Diff.STE.L2re F (T γ U)|
        ≤ C γ * Real.sqrt (Work.Diff.STE.CSq (d - 1) (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.CSq d (Work.Diff.STE.fourierCoeff U)))
    (F U : κ → (ι → ℝ) → ℂ)
    (hF : ∀ γ, Work.Diff.STE.B3.VarCoef.SmoothPer (F γ))
    (hU : ∀ γ, Work.Diff.STE.B3.VarCoef.SmoothPer (U γ)) :
    |∑ γ, Work.Diff.STE.L2re (F γ) (T γ (U γ))|
      ≤ (∑ γ, C γ) *
          Real.sqrt (∑ γ, Work.Diff.STE.CSq (d - 1) (Work.Diff.STE.fourierCoeff (F γ))) *
          Real.sqrt (∑ γ, Work.Diff.STE.CSq d (Work.Diff.STE.fourierCoeff (U γ))) := by
  classical
  exact abs_sum_le_sum_mul_sqrt (fun γ => Work.Diff.STE.L2re (F γ) (T γ (U γ)))
    C (fun γ => Work.Diff.STE.CSq (d - 1) (Work.Diff.STE.fourierCoeff (F γ)))
    (fun γ => Work.Diff.STE.CSq d (Work.Diff.STE.fourierCoeff (U γ)))
    hC (fun γ => Work.Diff.STE.CSq_nonneg (d - 1) _)
    (fun γ => Work.Diff.STE.CSq_nonneg d _)
    (fun γ => hT γ (F γ) (U γ) (hF γ) (hU γ))

end Work.Diff.STE.B3.VarCoef
