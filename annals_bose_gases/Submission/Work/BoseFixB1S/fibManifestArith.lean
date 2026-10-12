import Mathlib.Analysis.Real.Sqrt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- The manifest-square arithmetic used by the fibre/Sq arm: given `Y ≤ κ a Q`
(the manifest bound on the second moment with the fibre weight), the manifest square
`X + 2√(YX) + Y` is dominated by `X` plus the credit `M a (√(QX) + Q)`, where
`M = max κ (2√κ/√a)` is exactly the constant produced by the two possible routes
(`Y ≤ κ a Q` directly, and `√(YX) ≤ √κ √a √(QX)`). -/
theorem fibManifestArith {κ a X Y Q : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hX : 0 ≤ X)
    (hQ : 0 ≤ Q) (hY : 0 ≤ Y) (hYle : Y ≤ κ * a * Q) :
    X + 2 * Real.sqrt (Y * X) + Y
      ≤ X + max κ (2 * Real.sqrt κ / Real.sqrt a) * a * (Real.sqrt (Q * X) + Q) := by
  set M := max κ (2 * Real.sqrt κ / Real.sqrt a) with hM
  have ha0 : 0 ≤ a := le_of_lt ha
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos_of_pos ha
  have hsq : Real.sqrt a * Real.sqrt a = a := by
    rw [← sq]; exact Real.sq_sqrt ha0
  have hMk : κ ≤ M := le_max_left _ _
  have hMs : 2 * Real.sqrt κ / Real.sqrt a ≤ M := le_max_right _ _
  -- `a / √a = √a`, hence `(2√κ/√a) * a = 2√κ√a`
  have hdiv : a / Real.sqrt a = Real.sqrt a := by
    rw [div_eq_iff hsa.ne']
    exact hsq.symm
  have hMs' : (2 * Real.sqrt κ / Real.sqrt a) * a ≤ M * a :=
    mul_le_mul_of_nonneg_right hMs ha0
  have hMa : 2 * Real.sqrt κ * Real.sqrt a ≤ M * a := by
    rwa [show (2 * Real.sqrt κ / Real.sqrt a) * a = 2 * Real.sqrt κ * Real.sqrt a by
      rw [show (2 * Real.sqrt κ / Real.sqrt a) * a = 2 * Real.sqrt κ * (a / Real.sqrt a) by ring,
        hdiv]] at hMs'
  have hκa : 0 ≤ κ * a := mul_nonneg hκ ha0
  have hYX : Y * X ≤ (κ * a) * (Q * X) := by
    have h := mul_le_mul_of_nonneg_right hYle hX
    nlinarith [h]
  -- the square-root half
  have h1 : 2 * Real.sqrt (Y * X) ≤ 2 * (Real.sqrt (κ * a) * Real.sqrt (Q * X)) := by
    have h := Real.sqrt_le_sqrt hYX
    rw [Real.sqrt_mul hκa (Q * X)] at h
    linarith
  have h2 : 2 * Real.sqrt (Y * X) ≤ M * a * Real.sqrt (Q * X) := by
    calc 2 * Real.sqrt (Y * X) ≤ 2 * (Real.sqrt (κ * a) * Real.sqrt (Q * X)) := h1
      _ = 2 * Real.sqrt κ * Real.sqrt a * Real.sqrt (Q * X) := by
            rw [Real.sqrt_mul hκ a]; ring
      _ ≤ M * a * Real.sqrt (Q * X) := mul_le_mul_of_nonneg_right hMa (Real.sqrt_nonneg _)
  -- the `Y` half
  have h3 : Y ≤ M * a * Q := by
    have h : κ * a ≤ M * a := mul_le_mul_of_nonneg_right hMk ha0
    have h' : (κ * a) * Q ≤ (M * a) * Q := mul_le_mul_of_nonneg_right h hQ
    nlinarith [hYle, h']
  nlinarith [h2, h3]

end Work.BoseFixB1S
