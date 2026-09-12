import Submission.Rad.LinFun
import Submission.Rad.Prob
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The Enflo-type inequality (for the linear test function) implies the Rademacher-type
inequality with the same constant. -/
lemma isRademacherType_of_isEnfloType (C : ℝ≥0∞) (p : ℝ) :
    IsEnfloType X C p → IsRademacherType X C p := by
  intro hC n hn x
  have hEn := hC n hn (lin (X := X) x)
  -- RHS of the Enflo inequality equals the Rademacher RHS
  have hRHS : (∑ j : Fin n, (∫⁻ (ε : Ω n), ‖D j (lin (X := X) x) ε‖ₑ ^ p
      ∂rademacherProductDistribution (Fin n))) =
      ∑ j : Fin n, ‖x j‖ₑ ^ p := by
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (∫⁻ (ε : Ω n), ‖D j (lin (X := X) x) ε‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n))
          = ∫⁻ (ε : Ω n), ‖x j‖ₑ ^ p ∂rademacherProductDistribution (Fin n) := by
            apply lintegral_congr
            intro ε
            rw [D_lin]
            congr 1
            exact ennorm_scalar (ε j) (x j)
      _ = ‖x j‖ₑ ^ p := by
        have huniv : (rademacherProductDistribution (Fin n)) Set.univ = 1 := by simp
        rw [lintegral_const, huniv, mul_one]
  -- LHS of the Enflo inequality equals the Rademacher LHS
  have hLHS : (∫⁻ (ε : Ω n), ‖(1 / 2 : ℝ) • (lin (X := X) x ε - lin (X := X) x (-ε))‖ₑ ^ p
      ∂rademacherProductDistribution (Fin n)) =
      ∫⁻ (ε : Ω n), ‖∑ j : Fin n, (((ε j : RadType.C) : ℝ) • x j)‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n) := by
    apply lintegral_congr
    intro ε
    have hneg : (-ε : Ω n) = negΩ ε := rfl
    rw [hneg, lin_sub_neg]
    unfold lin
    rfl
  rw [← hLHS, ← hRHS]
  exact hEn

/-- If every Enflo constant is a Rademacher constant, then `TR ≤ TE`. -/
theorem TR_le_TE (p : ℝ) : TR X p ≤ TE X p := by
  change sInf {C | IsRademacherType X C p} ≤ sInf {C | IsEnfloType X C p}
  apply sInf_le_sInf
  intro C hC
  exact isRademacherType_of_isEnfloType (X := X) C p hC

end RadType
