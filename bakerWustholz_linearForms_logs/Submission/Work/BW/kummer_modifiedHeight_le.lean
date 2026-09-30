import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.kummer_logHeight_le
import Submission.Work.BW.kummer_log_norm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option linter.unusedVariables false

open Complex

/-- If `Complex.exp (2⁻ᵛ * ∑ i, L i * log (φ (α i))) = φ β` with all `α i ≠ 0` and `β ≠ 0`, then the
modified height of `β` is at most `max (1/d) (2⁻ᵛ * ∑ i, |L i| * h'(α i))` where `d = finrank ℚ K`. -/
theorem kummer_modifiedHeight_le {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) {n : ℕ}
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0) (L : Fin n → ℤ) (v : ℕ) (β : K) (hβ0 : β ≠ 0)
    (h : Complex.exp (((2 : ℂ) ^ v)⁻¹ * ∑ i, (L i : ℂ) * Complex.log (φ (α i))) = φ β) :
    BakerWustholz.modifiedHeight φ β ≤
      max (1 / (Module.finrank ℚ K : ℝ))
        ((((2 : ℝ) ^ v)⁻¹) * ∑ i, |(L i : ℝ)| * BakerWustholz.modifiedHeight φ (α i)) := by
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hddef
  have hd : 0 < d := by rw [hddef]; exact_mod_cast Module.finrank_pos
  set P : ℝ := ((2 : ℝ) ^ v)⁻¹ with hPdef
  have hP : 0 < P := by rw [hPdef]; positivity
  set B : ℝ := ∑ i, |(L i : ℝ)| * BakerWustholz.modifiedHeight φ (α i) with hBdef
  -- `logHeight₁ (α i)` and `‖log (φ (α i))‖` are bounded by `d · h'(α i)`.
  have hh_le : ∀ i, Height.logHeight₁ (α i) ≤ d * BakerWustholz.modifiedHeight φ (α i) := by
    intro i
    have hle : Height.logHeight₁ (α i) / d ≤ BakerWustholz.modifiedHeight φ (α i) := by
      dsimp only [BakerWustholz.modifiedHeight]
      exact le_max_left _ _
    rw [div_le_iff₀ hd] at hle
    rw [mul_comm (BakerWustholz.modifiedHeight φ (α i)) d] at hle
    exact hle
  have hlogn_le : ∀ i, ‖Complex.log (φ (α i))‖ ≤ d * BakerWustholz.modifiedHeight φ (α i) := by
    intro i
    have hle : ‖Complex.log (φ (α i))‖ / d ≤ BakerWustholz.modifiedHeight φ (α i) := by
      dsimp only [BakerWustholz.modifiedHeight]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    rw [div_le_iff₀ hd] at hle
    rw [mul_comm (BakerWustholz.modifiedHeight φ (α i)) d] at hle
    exact hle
  have hB_eq : (∑ i, |(L i : ℝ)| * (d * BakerWustholz.modifiedHeight φ (α i))) = d * B := by
    rw [hBdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- Height part: from `β ^ 2^v = ∏ α ^ L` and subadditivity of the height.
  have hH : Height.logHeight₁ β / d ≤ P * B := by
    rw [div_le_iff₀ hd]
    have hkl := kummer_logHeight_le φ α hα L v β h
    have hs : (∑ i, ((L i).natAbs : ℝ) * Height.logHeight₁ (α i)) ≤ d * B := by
      rw [← hB_eq]
      apply Finset.sum_le_sum
      intro i _
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact mul_le_mul_of_nonneg_left (hh_le i) (abs_nonneg ((L i : ℝ)))
    have hstep : Height.logHeight₁ β ≤ P * (d * B) := by
      calc Height.logHeight₁ β
          ≤ ((2 : ℝ) ^ v)⁻¹ * ∑ i, ((L i).natAbs : ℝ) * Height.logHeight₁ (α i) := hkl
        _ = P * ∑ i, ((L i).natAbs : ℝ) * Height.logHeight₁ (α i) := by rw [hPdef]
        _ ≤ P * (d * B) := mul_le_mul_of_nonneg_left hs (le_of_lt hP)
    calc Height.logHeight₁ β ≤ P * (d * B) := hstep
      _ = (P * B) * d := by ring
  -- Logarithmic part: the principal logarithm has least norm among all determinations.
  have hN : ‖Complex.log (φ β)‖ / d ≤ P * B := by
    rw [div_le_iff₀ hd]
    have hS_le : ‖∑ i, (L i : ℂ) * Complex.log (φ (α i))‖
        ≤ ∑ i, |(L i : ℝ)| * (d * BakerWustholz.modifiedHeight φ (α i)) := by
      calc ‖∑ i, (L i : ℂ) * Complex.log (φ (α i))‖
          ≤ ∑ i, ‖(L i : ℂ) * Complex.log (φ (α i))‖ := norm_sum_le _ _
        _ = ∑ i, |(L i : ℝ)| * ‖Complex.log (φ (α i))‖ := by
              apply Finset.sum_congr rfl
              intro i _
              rw [norm_mul, norm_intCast]
        _ ≤ ∑ i, |(L i : ℝ)| * (d * BakerWustholz.modifiedHeight φ (α i)) := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_left (hlogn_le i) (abs_nonneg ((L i : ℝ)))
    have hnorm_eq : ‖((2 : ℂ) ^ v)⁻¹ * ∑ i, (L i : ℂ) * Complex.log (φ (α i))‖
        = P * ‖∑ i, (L i : ℂ) * Complex.log (φ (α i))‖ := by
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat, ← hPdef]
    calc ‖Complex.log (φ β)‖
        ≤ ‖((2 : ℂ) ^ v)⁻¹ * ∑ i, (L i : ℂ) * Complex.log (φ (α i))‖ := kummer_log_norm_le h
      _ = P * ‖∑ i, (L i : ℂ) * Complex.log (φ (α i))‖ := hnorm_eq
      _ ≤ P * (∑ i, |(L i : ℝ)| * (d * BakerWustholz.modifiedHeight φ (α i))) :=
            mul_le_mul_of_nonneg_left hS_le (le_of_lt hP)
      _ = (P * B) * d := by rw [hB_eq]; ring
  have hmod : BakerWustholz.modifiedHeight φ β
      = max (Height.logHeight₁ β / d) (max (‖Complex.log (φ β)‖ / d) (1 / d)) := by
    dsimp only [BakerWustholz.modifiedHeight]
  rw [hmod]
  exact max_le (le_trans hH (le_max_right _ _))
    (max_le (le_trans hN (le_max_right _ _)) (le_max_left _ _))

end Work.BW
