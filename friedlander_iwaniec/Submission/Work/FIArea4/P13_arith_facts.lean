import Mathlib
import Submission.Work.FIArea4.P13Scale

namespace Work.FIArea4

noncomputable section

/-- For `x ≥ 1` and `ε > 0`, `log x ≤ (8/ε) · x^{ε/8}`. -/
private lemma log_le_const_mul_rpow {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (8/ε) * x^(ε/8) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hu1 : 1 ≤ x^(ε/8) := Real.one_le_rpow (z := ε/8) hx (by linarith)
  have hu0 : 0 < x^(ε/8) := lt_of_lt_of_le zero_lt_one hu1
  have h1 : Real.log (x^(ε/8)) ≤ x^(ε/8) - 1 := Real.log_le_sub_one_of_pos hu0
  have h2 : Real.log (x^(ε/8)) ≤ x^(ε/8) := by linarith
  have h3 : Real.log (x^(ε/8)) = (ε/8) * Real.log x := Real.log_rpow hx0 (ε/8)
  have h4 : (ε/8) * Real.log x ≤ x^(ε/8) := by rw [← h3]; exact h2
  calc Real.log x = (8/ε) * ((ε/8) * Real.log x) := by field_simp
    _ ≤ (8/ε) * x^(ε/8) := by apply mul_le_mul_of_nonneg_left h4; positivity

/-- The first summand of `p14T13` is a lower bound for `p14T13` (the second summand is `≥ 0`). -/
private lemma T13_ge_first (D R S : ℕ) (ε : ℝ) :
    (D:ℝ) * (((R:ℝ)+(S:ℝ))^((1:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^((1:ℝ)/4)) ≤ p14T13 D R S ε := by
  have h2 : (0:ℝ) ≤ (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((9:ℝ)/8) := by positivity
  rw [show p14T13 D R S ε = (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4)
      + (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((9:ℝ)/8) from rfl]
  exact le_add_of_nonneg_right h2

theorem P13_arith_facts (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D R S : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      1 < p13P D R S →
      (D:ℝ) / p13P D R S ≤ p14T13 D R S ε ∧
      1 / p13P D R S ≤ p14T13 D R S ε ∧
      ((R:ℝ)*(S:ℝ)) / (p13P D R S)^2 ≤ p14T13 D R S ε ∧
      Real.log (4 * p13P D R S) ≤ K * (((R:ℝ)*(S:ℝ))^(ε/8)) ∧
      (∀ x : ℝ, 1 ≤ x → x ≤ 32 * (((R:ℝ)*(S:ℝ))^(3/4)) →
          Real.log x ≤ K * (((R:ℝ)*(S:ℝ))^(ε/8))) := by
  refine ⟨Real.log 32 + (3/4)*(8/ε), ?_, ?_⟩
  · have h1 : 0 < Real.log 32 := Real.log_pos (by norm_num)
    have h2 : 0 < (3/4)*(8/ε) := by positivity
    linarith
  · intro D R S hD hR hS hP
    have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
    have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hX1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) := by nlinarith [hR1, hS1]
    have hX0 : (0:ℝ) < (R:ℝ)*(S:ℝ) := lt_of_lt_of_le zero_lt_one hX1
    have hY1 : (1:ℝ) ≤ (R:ℝ)+(S:ℝ) := by
      have : (0:ℝ) ≤ (S:ℝ) := Nat.cast_nonneg S
      linarith
    have hY0 : (0:ℝ) < (R:ℝ)+(S:ℝ) := lt_of_lt_of_le zero_lt_one hY1
    have hP0 : (0:ℝ) < p13P D R S := p13P_pos D R S hD hR hS
    have hP1le : (1:ℝ) ≤ p13P D R S := hP.le
    have hYr1 : (1:ℝ) ≤ ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) := Real.one_le_rpow (z := (1:ℝ)/4) hY1 (by norm_num)
    have hXr1 : (1:ℝ) ≤ ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := Real.one_le_rpow (z := (1:ℝ)/4) hX1 (by norm_num)
    have hprod : (1:ℝ) ≤ ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * (((R:ℝ)*(S:ℝ))^((1:ℝ)/4)) := by nlinarith [hYr1, hXr1]
    have hA_ge_D : (D:ℝ) ≤ (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := by
      have := le_mul_of_one_le_right hD0.le hprod
      simpa only [mul_assoc] using this
    have hA_ge_1 : (1:ℝ) ≤ (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := by
      have hDp : (1:ℝ) ≤ (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) := by nlinarith [hD1, hYr1]
      have := mul_le_mul hDp hXr1 zero_le_one (le_trans zero_le_one hDp)
      simpa only [mul_one, mul_assoc] using this
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc (D:ℝ) / p13P D R S ≤ (D:ℝ) := by
            rw [div_le_iff₀ hP0]
            exact le_mul_of_one_le_right hD0.le hP1le
        _ ≤ _ := hA_ge_D
        _ ≤ p14T13 D R S ε := T13_ge_first D R S ε
    · calc 1 / p13P D R S ≤ (1:ℝ) := by
            rw [div_le_iff₀ hP0]; simpa using hP1le
        _ ≤ _ := hA_ge_1
        _ ≤ p14T13 D R S ε := T13_ge_first D R S ε
    · have hkey : (p13P D R S)^2 * ((D:ℝ)*((R:ℝ)+(S:ℝ))^((1:ℝ)/4)*((R:ℝ)*(S:ℝ))^((1:ℝ)/4)) = (R:ℝ)*(S:ℝ) := by
        have hmul := p13P_mul_sq D R S hD hR hS
        have hy : ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/4) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) = 1 := by
          rw [← Real.rpow_add hY0]; norm_num
        have hx : ((R:ℝ)*(S:ℝ))^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) = (R:ℝ)*(S:ℝ) := by
          rw [← Real.rpow_add hX0]; norm_num
        calc (p13P D R S)^2 * ((D:ℝ)*((R:ℝ)+(S:ℝ))^((1:ℝ)/4)*((R:ℝ)*(S:ℝ))^((1:ℝ)/4))
            = ((D:ℝ) * (p13P D R S)^2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := by ring
          _ = (((R:ℝ)+(S:ℝ))^(-(1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((3:ℝ)/4)) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := by rw [hmul]
          _ = (((R:ℝ)+(S:ℝ))^(-(1:ℝ)/4) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^((3:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4)) := by ring
          _ = 1 * ((R:ℝ)*(S:ℝ)) := by rw [hy, hx]
          _ = (R:ℝ)*(S:ℝ) := by ring
      have hP2ne : (p13P D R S)^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hP0)
      have hEq : ((R:ℝ)*(S:ℝ)) / (p13P D R S)^2 = (D:ℝ)*((R:ℝ)+(S:ℝ))^((1:ℝ)/4)*((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := by
        rw [div_eq_iff hP2ne]
        conv_rhs => rw [mul_comm]
        exact hkey.symm
      calc ((R:ℝ)*(S:ℝ)) / (p13P D R S)^2
          = (D:ℝ)*((R:ℝ)+(S:ℝ))^((1:ℝ)/4)*((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := hEq
        _ ≤ p14T13 D R S ε := T13_ge_first D R S ε
    · have hPle := p13P_le D R S hD hR hS
      have h4P0 : (0:ℝ) < 4 * p13P D R S := by linarith
      have h4Ple : 4 * p13P D R S ≤ 4 * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8) := by
        have := mul_le_mul_of_nonneg_left hPle (by norm_num : (0:ℝ) ≤ 4); linarith
      have hlog1 : Real.log (4 * p13P D R S) ≤ Real.log (4 * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8)) :=
        Real.log_le_log h4P0 h4Ple
      have hlog2 : Real.log (4 * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8))
          = Real.log 4 + (3/8) * Real.log ((R:ℝ)*(S:ℝ)) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hX0 _)), Real.log_rpow hX0]
      have hXe1 : (1:ℝ) ≤ ((R:ℝ)*(S:ℝ))^(ε/8) := Real.one_le_rpow (z := ε/8) hX1 (by linarith)
      have hXe0 : (0:ℝ) ≤ ((R:ℝ)*(S:ℝ))^(ε/8) := le_trans zero_le_one hXe1
      have hlogX := log_le_const_mul_rpow hε hX1
      have hstep : Real.log 4 + (3/8) * Real.log ((R:ℝ)*(S:ℝ))
          ≤ Real.log 4 + (3/8) * ((8/ε) * ((R:ℝ)*(S:ℝ))^(ε/8)) := by
        have hc : (3/8) * Real.log ((R:ℝ)*(S:ℝ)) ≤ (3/8) * ((8/ε) * ((R:ℝ)*(S:ℝ))^(ε/8)) :=
          mul_le_mul_of_nonneg_left hlogX (by norm_num)
        linarith
      have hlog4nneg : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hfinal : Real.log 4 + (3/8) * ((8/ε) * ((R:ℝ)*(S:ℝ))^(ε/8))
          ≤ (Real.log 32 + (3/4)*(8/ε)) * ((R:ℝ)*(S:ℝ))^(ε/8) := by
        have hc : Real.log 4 + (3/8)*(8/ε) ≤ Real.log 32 + (3/4)*(8/ε) := by
          have h32 : Real.log 4 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
          have h34 : (3:ℝ)/8*(8/ε) ≤ (3/4)*(8/ε) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          linarith
        have h1 : Real.log 4 ≤ (Real.log 4) * ((R:ℝ)*(S:ℝ))^(ε/8) := by
          have := mul_le_mul_of_nonneg_left hXe1 hlog4nneg
          simpa using this
        have h2 := mul_le_mul_of_nonneg_right hc hXe0
        nlinarith [h1, h2]
      calc Real.log (4 * p13P D R S) ≤ Real.log (4 * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8)) := hlog1
        _ = Real.log 4 + (3/8) * Real.log ((R:ℝ)*(S:ℝ)) := hlog2
        _ ≤ Real.log 4 + (3/8) * ((8/ε) * ((R:ℝ)*(S:ℝ))^(ε/8)) := hstep
        _ ≤ (Real.log 32 + (3/4)*(8/ε)) * ((R:ℝ)*(S:ℝ))^(ε/8) := hfinal
    · intro x hx1 hxle
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
      have h32 : 32 * (((R:ℝ)*(S:ℝ))^(3/4)) = (32:ℝ) := by norm_num
      have hx32 : x ≤ (32:ℝ) := by rw [h32] at hxle; exact hxle
      have hlog : Real.log x ≤ Real.log 32 := Real.log_le_log hx0 hx32
      have hKpos : (0:ℝ) < Real.log 32 + (3/4)*(8/ε) := by
        have h1 : (0:ℝ) < Real.log 32 := Real.log_pos (by norm_num)
        have h2 : (0:ℝ) < (3/4)*(8/ε) := by positivity
        linarith
      have hXe1 : (1:ℝ) ≤ ((R:ℝ)*(S:ℝ))^(ε/8) := Real.one_le_rpow (z := ε/8) hX1 (by linarith)
      have hlog32le : Real.log 32 ≤ Real.log 32 + (3/4)*(8/ε) := by
        have : (0:ℝ) ≤ (3/4)*(8/ε) := by positivity
        linarith
      have hKle : Real.log 32 + (3/4)*(8/ε) ≤ (Real.log 32 + (3/4)*(8/ε)) * ((R:ℝ)*(S:ℝ))^(ε/8) :=
        le_mul_of_one_le_right hKpos.le hXe1
      linarith [hlog, hlog32le, hKle]

end

end Work.FIArea4
