import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseFixB1.MDelta.chiSmallScaledModulus
import Submission.Work.BoseFixB1.MDelta.flatWindowMassCompareAux
import Submission.Work.BoseFixB1B.chiB_abs_le_boxMargin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The elementary Young inequality `(a + b)² ≤ 2a² + 2b²`. -/
private lemma sqAddLeTwoB {a b : ℝ} : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Scalar core of the shift bound: if the "big-box" factor `A` is bounded by `cs` in absolute
value (`A² ≤ cs²`) and the variation of `A` along the shift is bounded by `X`
(`(A - C)² ≤ X`), then the variation of the product `A·B` (with both factors varying) is
controlled by the two variations:

    (A·B - C·D)² ≤ 2·cs²·(B - D)² + 2·X·D² . -/
private lemma shiftSqLeB {A B C D cs X : ℝ} (hA : A ^ 2 ≤ cs ^ 2) (hB : (A - C) ^ 2 ≤ X) :
    (A * B - C * D) ^ 2 ≤ 2 * cs ^ 2 * (B - D) ^ 2 + 2 * X * D ^ 2 := by
  have h1 : A * B - C * D = A * (B - D) + (A - C) * D := by ring
  rw [h1]
  have h3 : 2 * (A * (B - D)) ^ 2 ≤ 2 * cs ^ 2 * (B - D) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hA (sq_nonneg (B - D))
    nlinarith [h]
  have h4 : 2 * ((A - C) * D) ^ 2 ≤ 2 * X * D ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hB (sq_nonneg D)
    nlinarith [h]
  have h5 := sqAddLeTwoB (a := A * (B - D)) (b := (A - C) * D)
  linarith [h5, h3, h4]

theorem chiSmallBShiftSqLE {M : ℕ} (hM : 1 ≤ M) {ℓ d R L C3 : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hR : 0 ≤ R) (hL : 0 ≤ L) (hC3 : 0 ≤ C3)
    (hLip : ∀ x y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiScale ℓ x - Submission.BoseGases.chiScale ℓ y| ≤ L * ‖x - y‖ / ℓ)
    (hmod : ∀ (w t : EuclideanSpace ℝ (Fin 3)),
      ∫ x : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x - w))
          - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x - t - w)))^2
        ≤ C3 * (ℓ * d) * ‖t‖^2)
    (u : EuclideanSpace ℝ (Fin 3)) {z : EuclideanSpace ℝ (Fin 3)} (hz : ‖z‖ ≤ R) :
    ∫ y : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiSmallB M ℓ d u (z + y) - Submission.BoseGases.chiSmallB M ℓ d u y)^2
      ≤ 2 * (L / ℓ)^2 * R^2 * (ℓ * d)^3 + 2 * Submission.BoseGases.chiSupAbs^2 * C3 * (ℓ * d) * R^2 := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  -- the two rewriting identities for the scaled variable
  have hsub1 : ∀ x : E3, (ℓ * d)⁻¹ • (x - (ℓ * d) • u) = (ℓ * d)⁻¹ • x - u := by
    intro x
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  have hsub2 : ∀ x : E3, (ℓ * d)⁻¹ • (x - z - (ℓ * d) • u) = (ℓ * d)⁻¹ • (x - z) - u := by
    intro x
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  -- continuity of the small-box factor, plain and shifted
  have hcf : Continuous fun y : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u) :=
    (Submission.BoseGases.chiSmall_continuous (M := M) hM).comp (by fun_prop)
  have hcfz : Continuous fun y : E3 =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u) :=
    (Submission.BoseGases.chiSmall_continuous (M := M) hM).comp (by fun_prop)
  -- integrability of the squares of the shifted bump
  have hbase : Integrable fun t : E3 => (Submission.BoseGases.chiSmall M t) ^ 2 := by
    have hcs : HasCompactSupport fun t : E3 => (Submission.BoseGases.chiSmall M t) ^ 2 := by
      refine (Submission.BoseGases.chiSmall_hasCompactSupport (M := M) hM).mono ?_
      intro t ht
      rw [Function.mem_support] at ht ⊢
      intro h0
      exact ht (by rw [h0]; norm_num)
    exact ((Submission.BoseGases.chiSmall_continuous (M := M) hM).pow 2)
      |>.integrable_of_hasCompactSupport hcs
  have hIf : Integrable fun y : E3 => (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2 := by
    have h1 : Integrable fun t : E3 =>
        (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (t - (ℓ * d) • u))) ^ 2 :=
      (hbase.comp_smul (inv_ne_zero (ne_of_gt hc))).comp_sub_right ((ℓ * d) • u)
    refine h1.congr (ae_of_all _ (fun t => ?_))
    show (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (t - (ℓ * d) • u))) ^ 2
        = (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t - u)) ^ 2
    rw [hsub1 t]
  have hIfz : Integrable fun y : E3 =>
      (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)) ^ 2 :=
    hIf.comp_add_left z
  have hIabs : Integrable fun y : E3 =>
      (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
        - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2 := by
    have hmaj : Integrable fun y : E3 =>
        2 * ((Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)) ^ 2
          + (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2) :=
      (hIfz.add hIf).const_mul 2
    refine hmaj.mono' ((hcfz.sub hcf).pow 2).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
      + Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u))]
  -- the pointwise bound
  have hpt : ∀ y : E3,
      (Submission.BoseGases.chiSmallB M ℓ d u (z + y)
        - Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2
      ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2
        + 2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2)
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2 := by
    intro y
    have h1 : Submission.BoseGases.chiSmallB M ℓ d u (z + y)
        = Submission.BoseGases.chiScale ℓ (z + y)
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u) := rfl
    have h2 : Submission.BoseGases.chiSmallB M ℓ d u y
        = Submission.BoseGases.chiScale ℓ y
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u) := rfl
    rw [h1, h2]
    refine shiftSqLeB ?_ ?_
    · calc (Submission.BoseGases.chiScale ℓ (z + y)) ^ 2
          = |Submission.BoseGases.chiScale ℓ (z + y)| ^ 2 := (sq_abs _).symm
        _ ≤ Submission.BoseGases.chiSupAbs ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (Submission.BoseGases.chiScale_abs_le_sup ℓ (z + y)) 2
    · have h := hLip (z + y) y
      rw [add_sub_cancel_right] at h
      calc (Submission.BoseGases.chiScale ℓ (z + y) - Submission.BoseGases.chiScale ℓ y) ^ 2
          = |Submission.BoseGases.chiScale ℓ (z + y) - Submission.BoseGases.chiScale ℓ y| ^ 2 :=
            (sq_abs _).symm
        _ ≤ (L * ‖z‖ / ℓ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = (L / ℓ) ^ 2 * ‖z‖ ^ 2 := by ring
  -- integrability of the majorant and the passage to the integral
  have hImaj2 : Integrable fun y : E3 =>
      2 * Submission.BoseGases.chiSupAbs ^ 2
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2
        + 2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2)
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2 :=
    (hIabs.const_mul (2 * Submission.BoseGases.chiSupAbs ^ 2)).add
      (hIf.const_mul (2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2)))
  have hmono : (∫ y : E3, (Submission.BoseGases.chiSmallB M ℓ d u (z + y)
        - Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2)
      ≤ ∫ y : E3, (2 * Submission.BoseGases.chiSupAbs ^ 2
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
                - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2
          + 2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2)
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2) :=
    integral_mono_of_nonneg (ae_of_all _ (fun y => sq_nonneg _)) hImaj2 (ae_of_all _ hpt)
  rw [integral_add (hIabs.const_mul (2 * Submission.BoseGases.chiSupAbs ^ 2))
      (hIf.const_mul (2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2))),
    integral_const_mul, integral_const_mul] at hmono
  -- the modulus bound on the shifted bump, converted to the `y ↦ y + z` shape
  have hI1 : (∫ y : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
        - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2)
      ≤ C3 * (ℓ * d) * ‖z‖ ^ 2 := by
    have htrans : (∫ y : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
          - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2)
        = ∫ v : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • v - u)
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - z) - u)) ^ 2 := by
      have h := integral_add_left_eq_self (μ := (volume : Measure E3))
        (fun v : E3 => (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • v - u)
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - z) - u)) ^ 2) z
      simpa [add_sub_cancel_left] using h
    have hcongr : (∫ v : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • v - u)
          - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - z) - u)) ^ 2)
        = ∫ v : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - (ℓ * d) • u))
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - z - (ℓ * d) • u))) ^ 2 :=
      integral_congr_ae (ae_of_all _ (fun v => by
        show (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • v - u)
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - z) - u)) ^ 2
            = (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - (ℓ * d) • u))
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - z - (ℓ * d) • u))) ^ 2
        rw [hsub1 v, hsub2 v]))
    rw [htrans, hcongr]
    exact hmod ((ℓ * d) • u) z
  -- the L²-normalisation of the shifted bump
  have hI2 : (∫ y : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2)
      = (ℓ * d) ^ 3 := by
    rw [← Work.BoseFixB1.MDelta.integral_chiSmall_scale_sq (M := M) hM hc ((ℓ * d) • u)]
    exact integral_congr_ae (ae_of_all _ (fun v => by
      show (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • v - u)) ^ 2
          = (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (v - (ℓ * d) • u))) ^ 2
      rw [hsub1 v]))
  refine le_trans hmono ?_
  rw [hI2]
  -- the arithmetic
  have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hA1 : 2 * Submission.BoseGases.chiSupAbs ^ 2
        * (∫ y : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2)
      ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * R ^ 2 := by
    have h1 : 2 * Submission.BoseGases.chiSupAbs ^ 2
        * (∫ y : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2)
        ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * (C3 * (ℓ * d) * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hI1 (by positivity)
    have h2 : 2 * Submission.BoseGases.chiSupAbs ^ 2 * (C3 * (ℓ * d) * ‖z‖ ^ 2)
        ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * (C3 * (ℓ * d) * R ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz2 (by positivity)) (by positivity)
    have h3 : 2 * Submission.BoseGases.chiSupAbs ^ 2 * (C3 * (ℓ * d) * R ^ 2)
        = 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * R ^ 2 := by ring
    linarith [h1, h2, h3]
  have hA2 : 2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2) * (ℓ * d) ^ 3
      ≤ 2 * ((L / ℓ) ^ 2 * R ^ 2) * (ℓ * d) ^ 3 := by
    have hzt : (L / ℓ) ^ 2 * ‖z‖ ^ 2 ≤ (L / ℓ) ^ 2 * R ^ 2 :=
      mul_le_mul_of_nonneg_left hz2 (by positivity)
    have h1 : 2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2) ≤ 2 * ((L / ℓ) ^ 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left hzt (by norm_num)
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc 2 * Submission.BoseGases.chiSupAbs ^ 2
        * (∫ y : E3, (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (z + y) - u)
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2)
      + 2 * ((L / ℓ) ^ 2 * ‖z‖ ^ 2) * (ℓ * d) ^ 3
      ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * R ^ 2
        + 2 * ((L / ℓ) ^ 2 * R ^ 2) * (ℓ * d) ^ 3 := add_le_add hA1 hA2
    _ = 2 * (L / ℓ) ^ 2 * R ^ 2 * (ℓ * d) ^ 3
        + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * R ^ 2 := by ring

end Work.BoseB1Cube
