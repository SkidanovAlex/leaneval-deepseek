import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-! ## Auxiliary bounds for the proof of `gTest_zpz`

We bound the radial factor `z ↦ z · ∂_z gPhi z` using the elementary inequality
`1 + t ≤ e^t`, and the angular factor by `1 ≤ 1` on the quadrant.  The numerical
constant is deliberately crude; only its existence matters. -/

/-- `z² e^{-z} ≤ 4` for `z ≥ 0`, from `1 + z/2 ≤ e^{z/2}`. -/
lemma zsq_exp_neg_le (z : ℝ) (hz : 0 ≤ z) : z ^ 2 * Real.exp (-z) ≤ 4 := by
  have h := Real.add_one_le_exp (z/2)
  have hpos : 0 ≤ z/2 + 1 := by linarith
  have hz2 : 0 ≤ z/2 := by linarith
  have h2 : (z/2)^2 ≤ (Real.exp (z/2))^2 :=
    (pow_le_pow_left₀ hz2 (by linarith : z/2 ≤ z/2 + 1) 2).trans (pow_le_pow_left₀ hpos h 2)
  have hexp : (Real.exp (z/2))^2 = Real.exp z := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : (z/2)^2 ≤ Real.exp z := hexp ▸ h2
  have h4 : z^2 ≤ 4 * Real.exp z := by
    have hh : (4:ℝ) * (z/2)^2 = z^2 := by ring
    linarith [h3, hh.symm.le]
  calc z^2 * Real.exp (-z) ≤ (4 * Real.exp z) * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 4 := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- `z³ e^{-z} ≤ 27` for `z ≥ 0`, from `1 + z/3 ≤ e^{z/3}`. -/
lemma zcu_exp_neg_le (z : ℝ) (hz : 0 ≤ z) : z ^ 3 * Real.exp (-z) ≤ 27 := by
  have h := Real.add_one_le_exp (z/3)
  have hpos : 0 ≤ z/3 + 1 := by linarith
  have hz3 : 0 ≤ z/3 := by linarith
  have h2 : (z/3)^3 ≤ (Real.exp (z/3))^3 :=
    (pow_le_pow_left₀ hz3 (by linarith : z/3 ≤ z/3 + 1) 3).trans (pow_le_pow_left₀ hpos h 3)
  have hexp : (Real.exp (z/3))^3 = Real.exp z := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : (z/3)^3 ≤ Real.exp z := hexp ▸ h2
  have h4 : z^3 ≤ 27 * Real.exp z := by
    have hh : (27:ℝ) * (z/3)^3 = z^3 := by ring
    linarith [h3, hh.symm.le]
  calc z^3 * Real.exp (-z) ≤ (27 * Real.exp z) * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 27 := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- `|sin(2θ)| ≤ 1` on the angular interval `[0, π/2]`. -/
lemma abs_gPsi_le_one (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) : |gPsi θ| ≤ 1 := by
  have h0 : 0 ≤ θ := hθ.1
  have h1 : θ ≤ Real.pi/2 := hθ.2
  have h2θ0 : 0 ≤ 2*θ := by linarith
  have h2θpi : 2*θ ≤ Real.pi := by linarith
  have hsin0 : 0 ≤ Real.sin (2*θ) := Real.sin_nonneg_of_nonneg_of_le_pi h2θ0 h2θpi
  rw [gPsi, abs_of_nonneg hsin0]
  exact Real.sin_le_one (2*θ)

/-- `|z · ∂_z gPhi z| ≤ 35` for `z ≥ 0`, where `gPhi z = z² e^{-z}`. -/
lemma abs_z_mul_gPhi1_le (z : ℝ) (hz : 0 ≤ z) : |z * gPhi1 z| ≤ 35 := by
  have hexpnn : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  have heq : z * gPhi1 z = (2*z^2 - z^3) * Real.exp (-z) := by
    unfold gPhi1; ring
  rw [heq, abs_mul, abs_of_nonneg hexpnn]
  calc |2*z^2 - z^3| * Real.exp (-z)
      ≤ (2*z^2 + z^3) * Real.exp (-z) := by
        apply mul_le_mul_of_nonneg_right _ hexpnn
        calc |2*z^2 - z^3| = |2*z^2 + -(z^3)| := by ring_nf
          _ ≤ |2*z^2| + |-(z^3)| := abs_add_le _ _
          _ = 2*z^2 + z^3 := by
              rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*z^2), abs_neg,
                  abs_of_nonneg (by positivity : (0:ℝ) ≤ z^3)]
    _ = 2*(z^2 * Real.exp (-z)) + z^3 * Real.exp (-z) := by ring
    _ ≤ 35 := by
        have h2 := zsq_exp_neg_le z hz
        have h3 := zcu_exp_neg_le z hz
        linarith [h2, h3]

/-- **Bound on `z ∂_z g`**: the weighted past-perturbation is bounded on the quadrant. -/
theorem gTest_zpz (ε : ℝ) :
    ∃ Cg' : ℝ, 0 ≤ Cg' ∧ ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z * Work.Spaces.pz (gTest ε) z θ| ≤ Cg' := by
  refine ⟨35 * |ε|, by positivity, ?_⟩
  intro z θ hz hθ
  rw [pz_gTest ε]
  simp only []
  have hzpart : |z * gPhi1 z| ≤ 35 := abs_z_mul_gPhi1_le z hz
  have hθpart : |gPsi θ| ≤ 1 := abs_gPsi_le_one θ hθ
  calc |z * (ε * gPhi1 z * gPsi θ)|
      = |ε| * |z * gPhi1 z| * |gPsi θ| := by simp only [abs_mul]; ring
    _ ≤ |ε| * 35 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hzpart (abs_nonneg ε)
        · exact hθpart
        · exact abs_nonneg _
        · positivity
    _ = 35 * |ε| := by ring

end Work.R1G
