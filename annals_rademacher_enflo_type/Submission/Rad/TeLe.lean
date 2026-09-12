import Submission.Rad.EnnRad
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure NNReal
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- `TE ≤ (π/√2) · TR` for `p ∈ [1, 2]` (coefficient as a single `ℝ≥0` division). -/
lemma TE_le_rad_mul' (p : ℝ) (h1p : 1 ≤ p) (hp2 : p ≤ 2) :
    TE X p ≤ ((pi / sqrt 2 : ℝ≥0) : ℝ≥0∞) * TR X p := by
  let k : ℝ≥0∞ := ((pi / sqrt 2 : ℝ≥0) : ℝ≥0∞)
  let R : Set ℝ≥0∞ := {C : ℝ≥0∞ | IsRademacherType X C p}
  let E : Set ℝ≥0∞ := {C : ℝ≥0∞ | IsEnfloType X C p}
  have hident : ((pi / sqrt 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (Real.pi / Real.sqrt 2) := by
    symm
    rw [← ENNReal.ofReal_coe_nnreal (p := (pi / sqrt 2 : ℝ≥0))]
    congr 1
    rw [NNReal.coe_div, NNReal.coe_real_pi]
    congr 1
    symm
    exact Real.coe_sqrt (x := (2 : ℝ≥0))
  have hk0 : k ≠ 0 := by
    unfold k
    rw [hident]
    exact (ENNReal.ofReal_eq_zero (p := Real.pi / Real.sqrt 2)).not.mpr
      (not_le_of_gt (div_pos Real.pi_pos (Real.sqrt_pos.2 (by norm_num))))
  have hktop : k ≠ ⊤ := by
    unfold k
    exact ne_of_lt (ENNReal.coe_lt_top (r := (pi / sqrt 2 : ℝ≥0)))
  have hfinite : ∀ C : ℝ≥0∞, C ∈ R → C ≠ ⊤ → k * C ∈ E := by
    intro C hC hCtop
    have hIs : IsEnfloType X (ENNReal.ofReal ((Real.pi / Real.sqrt 2) * C.toReal)) p :=
      enflo_of_rad (p := p) h1p hp2 hCtop hC
    have hEq : ENNReal.ofReal ((Real.pi / Real.sqrt 2) * C.toReal) = k * C := by
      unfold k
      exact rad_const_enn hCtop
    exact hEq ▸ hIs
  calc
    TE X p = sInf E := rfl
    _ ≤ sInf ((fun x : ℝ≥0∞ => k * x) '' R) := by
          apply le_sInf
          intro b hb
          rcases hb with ⟨C, hC, rfl⟩
          by_cases hCtop : C = ⊤
          · subst hCtop
            -- TE ≤ k * ⊤ = ⊤
            change sInf E ≤ k * ⊤
            rw [ENNReal.mul_top hk0]
            exact le_top
          · exact sInf_le (hfinite C hC hCtop)
    _ = k * sInf R := by
          exact (Commons.Analysis.ENNReal.mul_sInf_image hk0 hktop R).symm
    _ = k * TR X p := rfl

/-- `TE ≤ (π/√2) · TR` for `p ∈ [1, 2]` in the form used in the theorem statement. -/
theorem TE_le_rad_mul (p : ℝ) (h1p : 1 ≤ p) (hp2 : p ≤ 2) :
    TE X p ≤ (pi / sqrt 2) * TR X p := by
  have hmain := TE_le_rad_mul' (X := X) p h1p hp2
  rw [← ENNReal.coe_div (p := pi) (r := sqrt 2)]
  · exact hmain
  · -- sqrt 2 ≠ 0 in ℝ≥0
    exact ne_of_gt ((NNReal.sqrt_pos (x := (2 : ℝ≥0))).2 (by norm_num))

end RadType
