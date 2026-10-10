import Mathlib.Analysis.Polynomial.Norm
import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.Polynomial.aeval_bound_at_root
import Submission.Commons.Analysis.Polynomial.norm_coeff_ge_sub_supNorm
import Submission.Commons.Analysis.Polynomial.supNorm_neg
import Submission.Commons.Analysis.Real.exists_eps_lt_mul_pow
import Submission.Commons.Analysis.Real.mul_le_mul_pow_of_le
import Submission.Commons.FieldTheory.Polynomial.natDegree_eq_of_supNorm_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

theorem value_lt_leadingCoeff_mul_pow {K L : Type*} [NormedField K] [NormedField L]
    [Algebra K L] (h_ext : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖)
    (f₁ : Polynomial K) (hf₁ : 1 ≤ f₁.natDegree) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ‖f₁.coeff f₁.natDegree‖ ∧
      ∀ (f₂ : Polynomial K), f₂.natDegree ≤ f₁.natDegree →
        (f₂ - f₁).supNorm < ε → ∀ {α : L}, (Polynomial.aeval α) f₁ = 0 →
          ‖(Polynomial.aeval α) f₂‖ < ‖f₂.coeff f₂.natDegree‖ * δ ^ f₂.natDegree := by
  have hf0 : f₁ ≠ 0 := by
    rintro rfl
    simp at hf₁
  have hcne : f₁.coeff f₁.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hApos : 0 < ‖f₁.coeff f₁.natDegree‖ := norm_pos_iff.mpr hcne
  set M : ℝ := max 1 (max 1 ((f₁.natDegree : ℝ) * f₁.supNorm / ‖f₁.coeff f₁.natDegree‖)) with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact le_max_left _ _
  have hMnn : 0 ≤ M := by linarith
  set C : ℝ := (f₁.natDegree + 1 : ℝ) * M ^ f₁.natDegree with hC
  have hCnn : 0 ≤ C := by rw [hC]; exact mul_nonneg (by positivity) (pow_nonneg hMnn _)
  obtain ⟨ε₀, hε₀pos, hε₀⟩ :=
    Commons.Analysis.Real.exists_eps_lt_mul_pow
      (A := ‖f₁.coeff f₁.natDegree‖) (δ := δ) (C := C) (d := f₁.natDegree)
      hApos hδ hCnn
  refine ⟨min ε₀ ‖f₁.coeff f₁.natDegree‖, ?_, ?_, ?_⟩
  · exact lt_min hε₀pos hApos
  · exact min_le_right _ _
  · intro f₂ hdeg hclose α hα
    have hεle : min ε₀ ‖f₁.coeff f₁.natDegree‖ ≤ ‖f₁.coeff f₁.natDegree‖ :=
      min_le_right _ _
    have hεlee₀ : min ε₀ ‖f₁.coeff f₁.natDegree‖ ≤ ε₀ := min_le_left _ _
    have hεpos : 0 < min ε₀ ‖f₁.coeff f₁.natDegree‖ := lt_min hε₀pos hApos
    have hlt : (f₁ - f₂).supNorm < min ε₀ ‖f₁.coeff f₁.natDegree‖ := by
      have h : f₁ - f₂ = -(f₂ - f₁) := by ring
      rw [h, supNorm_neg]
      exact hclose
    have hdeg_eq : f₂.natDegree = f₁.natDegree :=
      Commons.FieldTheory.Polynomial.natDegree_eq_of_supNorm_lt f₁ f₂
        (min ε₀ ‖f₁.coeff f₁.natDegree‖) hdeg hεpos hεle hlt
    have hbnd := aeval_bound_at_root h_ext f₁ f₂ hf₁ hα
    rw [← hM] at hbnd
    have hd_le : (f₂ - f₁).natDegree ≤ f₁.natDegree := by
      calc (f₂ - f₁).natDegree ≤ max f₂.natDegree f₁.natDegree :=
            Polynomial.natDegree_sub_le f₂ f₁
        _ = f₁.natDegree := max_eq_right hdeg
    have hstep := Commons.Analysis.Real.mul_le_mul_pow_of_le
      (n := (f₂ - f₁).natDegree) (d := f₁.natDegree) (s := (f₂ - f₁).supNorm)
      (ε := min ε₀ ‖f₁.coeff f₁.natDegree‖) (M := M)
      hd_le hclose.le hM1 (Polynomial.supNorm_nonneg _) hεpos.le
    have hb : ‖(Polynomial.aeval α) f₂‖ ≤ min ε₀ ‖f₁.coeff f₁.natDegree‖ * C := by
      calc ‖(Polynomial.aeval α) f₂‖
          ≤ ((f₂ - f₁).natDegree + 1 : ℝ) * (f₂ - f₁).supNorm * M ^ (f₂ - f₁).natDegree :=
            hbnd
        _ ≤ (f₁.natDegree + 1 : ℝ) * (min ε₀ ‖f₁.coeff f₁.natDegree‖) *
              M ^ f₁.natDegree := hstep
        _ = min ε₀ ‖f₁.coeff f₁.natDegree‖ * C := by rw [hC]; ring
    have hbε₀ : ‖(Polynomial.aeval α) f₂‖ ≤ ε₀ * C :=
      hb.trans (mul_le_mul_of_nonneg_right hεlee₀ hCnn)
    have ha' : ‖f₁.coeff f₁.natDegree‖ - ε₀ ≤ ‖f₂.coeff f₁.natDegree‖ := by
      have h1 : ‖f₁.coeff f₁.natDegree‖ - (f₁ - f₂).supNorm ≤ ‖f₂.coeff f₁.natDegree‖ :=
        norm_coeff_ge_sub_supNorm f₁ f₂ f₁.natDegree
      have h2 : (f₁ - f₂).supNorm < ε₀ := lt_of_lt_of_le hlt hεlee₀
      linarith
    have hfinal := hε₀ ‖f₂.coeff f₁.natDegree‖ ‖(Polynomial.aeval α) f₂‖ ha' hbε₀
    simpa [hdeg_eq] using hfinal

end Commons.Analysis.Polynomial
