import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.chCslot_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Scratch: the assembly of `chCslot_le` from the two pieces (hypotheses `hA`, `hB` here). -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The pure-real arithmetic of the final assembly. -/
theorem cslot_arith {a R μ ℓ C_A C_B K0 η ε₀ : ℝ} (ha : 0 < a) (hR : 0 < R) (hμ : 0 < μ)
    (hℓ : 0 < ℓ) (hε₀ : 0 < ε₀) (hCA : 0 ≤ C_A) (hCB : 0 ≤ C_B)
    (hkey1 : μ * (ℓ ^ 3)⁻¹ / a ≤ ε₀ / (a ^ 4 * (2 * R) ^ 3))
    (hkey2 : μ * (ℓ ^ 9)⁻¹ / a ≤ ε₀ / (a ^ 4 * (2 * R) ^ 9))
    (hK0 : K0 = 64 * (max C_A 1) * (max C_B 1) * R ^ 12 *
        (ε₀ / (a ^ 4 * (2 * R) ^ 3) + ε₀ / (a ^ 4 * (2 * R) ^ 9)) + 1)
    (hη : η = K0 * a / (16 * max C_A 1 * μ * (1 + ℓ ^ 3) ^ 2 * ℓ ^ 3)) :
    0 < K0 ∧ 0 < η ∧
      C_A * (η * ℓ ^ 3 + C_B * ℓ ^ 3 * (R / ℓ) ^ 12) * (1 + ℓ ^ 3)
        ≤ K0 * a / (8 * μ * (1 + ℓ ^ 3)) := by
  have hA1 : 0 < max C_A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hAle : C_A ≤ max C_A 1 := le_max_left _ _
  have hB1 : 0 < max C_B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hBle : C_B ≤ max C_B 1 := le_max_left _ _
  have hK0pos : 0 < K0 := by
    rw [hK0]
    have h1 : 0 < ε₀ / (a ^ 4 * (2 * R) ^ 3) + ε₀ / (a ^ 4 * (2 * R) ^ 9) := by positivity
    positivity
  have hηpos : 0 < η := by rw [hη]; positivity
  have hR12n : 0 ≤ R ^ 12 := by positivity
  have hmaxAn : 0 ≤ max C_A 1 := le_of_lt hA1
  have hmaxBn : 0 ≤ max C_B 1 := le_of_lt hB1
  refine ⟨hK0pos, hηpos, ?_⟩
  have hpart1 : C_A * (η * ℓ ^ 3) * (1 + ℓ ^ 3) ≤ K0 * a / (16 * μ * (1 + ℓ ^ 3)) := by
    have hEq : C_A * (η * ℓ ^ 3) * (1 + ℓ ^ 3)
        = C_A * (K0 * a / (16 * max C_A 1 * μ * (1 + ℓ ^ 3))) := by
      first | (rw [hη]; field_simp) | (rw [hη]; field_simp; ring)
    rw [hEq]
    have h2 : C_A / max C_A 1 ≤ 1 := (div_le_one hA1).mpr hAle
    have h3 : 0 ≤ K0 * a / (16 * μ * (1 + ℓ ^ 3)) := by positivity
    have hsplit : C_A * (K0 * a / (16 * max C_A 1 * μ * (1 + ℓ ^ 3)))
        = (C_A / max C_A 1) * (K0 * a / (16 * μ * (1 + ℓ ^ 3))) := by
      first | (field_simp; ring) | field_simp
    rw [hsplit]
    exact le_trans (mul_le_mul_of_nonneg_right h2 h3) (le_of_eq (one_mul _))
  have hpart2 : C_A * (C_B * ℓ ^ 3 * (R / ℓ) ^ 12) * (1 + ℓ ^ 3)
      ≤ K0 * a / (16 * μ * (1 + ℓ ^ 3)) := by
    have h16 : (0:ℝ) < 16 * μ * (1 + ℓ ^ 3) := by positivity
    rw [le_div_iff₀ h16]
    have hstep : C_A * (C_B * ℓ ^ 3 * (R / ℓ) ^ 12) * (1 + ℓ ^ 3) * (16 * μ * (1 + ℓ ^ 3))
        = 16 * C_A * C_B * R ^ 12 * μ * ((ℓ ^ 9)⁻¹ * (1 + ℓ ^ 3) ^ 2) := by
      rw [div_pow, div_eq_mul_inv]; field_simp
    rw [hstep]
    have hu : (1 + ℓ ^ 3) ^ 2 ≤ 4 * (1 + (ℓ ^ 3) ^ 2) := by nlinarith [sq_nonneg (ℓ^3 - 1)]
    have hmul : (ℓ ^ 9)⁻¹ * (1 + ℓ ^ 3) ^ 2 ≤ 4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹) := by
      have h1 : (ℓ ^ 9)⁻¹ * (1 + ℓ ^ 3) ^ 2 ≤ (ℓ ^ 9)⁻¹ * (4 * (1 + (ℓ ^ 3) ^ 2)) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      have h2 : (ℓ ^ 9)⁻¹ * (4 * (1 + (ℓ ^ 3) ^ 2)) = 4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹) := by
        first | (field_simp; ring) | field_simp
      linarith [h1, h2.le, h2.ge]
    have hchain : 16 * C_A * C_B * R ^ 12 * μ * ((ℓ ^ 9)⁻¹ * (1 + ℓ ^ 3) ^ 2)
        ≤ 64 * max C_A 1 * max C_B 1 * R ^ 12 * a *
            (ε₀ / (a ^ 4 * (2 * R) ^ 9) + ε₀ / (a ^ 4 * (2 * R) ^ 3)) := by
      have hstep1 : 16 * C_A * C_B * R ^ 12 * μ * ((ℓ ^ 9)⁻¹ * (1 + ℓ ^ 3) ^ 2)
          ≤ 16 * C_A * C_B * R ^ 12 * μ * (4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹)) := by
        have : (0:ℝ) ≤ 16 * C_A * C_B * R ^ 12 * μ := by positivity
        exact mul_le_mul_of_nonneg_left hmul this
      have hstep2 : 16 * C_A * C_B * R ^ 12 * μ * (4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹))
          ≤ 16 * max C_A 1 * max C_B 1 * R ^ 12 * μ * (4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹)) := by
        have hb : C_A * C_B ≤ max C_A 1 * max C_B 1 :=
          mul_le_mul hAle hBle hCB (le_of_lt hA1)
        have : 0 ≤ R ^ 12 * μ * (4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹)) := by positivity
        nlinarith [hb, this, hR12n]
      have h3 : μ * (ℓ ^ 9)⁻¹ ≤ a * (ε₀ / (a ^ 4 * (2 * R) ^ 9)) := by
        have key := mul_le_mul_of_nonneg_left hkey2 ha.le
        have e : a * (μ * (ℓ ^ 9)⁻¹ / a) = μ * (ℓ ^ 9)⁻¹ := by field_simp
        rwa [e] at key
      have h4 : μ * (ℓ ^ 3)⁻¹ ≤ a * (ε₀ / (a ^ 4 * (2 * R) ^ 3)) := by
        have key := mul_le_mul_of_nonneg_left hkey1 ha.le
        have e : a * (μ * (ℓ ^ 3)⁻¹ / a) = μ * (ℓ ^ 3)⁻¹ := by field_simp
        rwa [e] at key
      have h5 : μ * (4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹))
          ≤ a * (4 * (ε₀ / (a ^ 4 * (2 * R) ^ 9) + ε₀ / (a ^ 4 * (2 * R) ^ 3))) := by
        nlinarith [h3, h4]
      have h6 : 16 * max C_A 1 * max C_B 1 * R ^ 12 * μ * (4 * ((ℓ ^ 9)⁻¹ + (ℓ ^ 3)⁻¹))
          ≤ 16 * max C_A 1 * max C_B 1 * R ^ 12 *
              (a * (4 * (ε₀ / (a ^ 4 * (2 * R) ^ 9) + ε₀ / (a ^ 4 * (2 * R) ^ 3)))) := by
        have h6' := mul_le_mul_of_nonneg_left h5
          (by positivity : (0:ℝ) ≤ 16 * max C_A 1 * max C_B 1 * R ^ 12)
        simpa only [mul_assoc] using h6'
      have h7 : 16 * max C_A 1 * max C_B 1 * R ^ 12 *
            (a * (4 * (ε₀ / (a ^ 4 * (2 * R) ^ 9) + ε₀ / (a ^ 4 * (2 * R) ^ 3))))
          = 64 * max C_A 1 * max C_B 1 * R ^ 12 * a *
              (ε₀ / (a ^ 4 * (2 * R) ^ 9) + ε₀ / (a ^ 4 * (2 * R) ^ 3)) := by ring
      linarith [hstep1, hstep2, h6, h7.le, h7.ge]
    have h8 : 64 * max C_A 1 * max C_B 1 * R ^ 12 * a *
          (ε₀ / (a ^ 4 * (2 * R) ^ 9) + ε₀ / (a ^ 4 * (2 * R) ^ 3)) ≤ K0 * a := by
      have h9 : K0 = 64 * max C_A 1 * max C_B 1 * R ^ 12 *
          (ε₀ / (a ^ 4 * (2 * R) ^ 3) + ε₀ / (a ^ 4 * (2 * R) ^ 9)) + 1 := hK0
      nlinarith [h9, ha, hR12n, hmaxAn, hmaxBn, hA1, hB1]
    linarith [hchain, h8]
  have hsum : C_A * (η * ℓ ^ 3 + C_B * ℓ ^ 3 * (R / ℓ) ^ 12) * (1 + ℓ ^ 3)
      = C_A * (η * ℓ ^ 3) * (1 + ℓ ^ 3) + C_A * (C_B * ℓ ^ 3 * (R / ℓ) ^ 12) * (1 + ℓ ^ 3) := by
    ring
  rw [hsum]
  have hdouble : K0 * a / (16 * μ * (1 + ℓ ^ 3)) + K0 * a / (16 * μ * (1 + ℓ ^ 3))
      = K0 * a / (8 * μ * (1 + ℓ ^ 3)) := by
    first | (field_simp; ring) | field_simp
  linarith [hpart1, hpart2, hdouble]

end Work.BoseBoxFock.PCFU
