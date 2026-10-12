import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

set_option maxHeartbeats 1000000 in
/-- Arithmetic step: the three-row estimate for the `chi`-row is absorbed by
`(1/2) C μ² R² ℓ³ t / a` for a constant `C` depending only on
`a, R, CA, CW, Cd, L`.

The proof decomposes the left-hand side into its three parts and bounds:
* `4A + δ(|W₁| + |W₁w|) ≤ 4CA(R/ℓ)²a + 2CdCW a⁴μ` (from `A ≤ CA(R/ℓ)²a`, `|W₁|,|W₁w| ≤ CW a`
  and `δ ≤ Cd t^L ≤ Cd μa³`, the last from `t ≤ 1`, `L ≥ 1`, `t = μa³`);
* `n² ≤ 4μ²ℓ⁶` and `√(n𝓜) ≤ 2μℓ³` (from `n ≤ 2μℓ³`, `𝓜 ≤ μℓ³`);
* `A + δ|W₁| ≤ CA(R/ℓ)²a + CdCW a⁴μ`.
After clearing the powers of `ℓ` (using `(R/ℓ)²ℓ² = R²`) each row becomes a fixed multiple of
`R²aμ²ℓ` resp. `CdCW a⁴μ³ℓ³`; the hypothesis `1 ≤ μaℓ²` converts `μ²ℓ⁴` into `μ³aℓ⁶`, and the
finite constant absorbs the `R⁻²` factor. -/
theorem chiRow_arith_step {a R : ℝ} (ha : 0 < a) (hR : 0 < R) {CA CW Cd L : ℝ}
    (hCA : 0 ≤ CA) (hCW : 0 ≤ CW) (hCd : 0 ≤ Cd) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {μ ℓ 𝓜 A W1 W1w δ t : ℝ} {n : ℕ},
        0 < μ → 0 < ℓ → t = μ * a ^ 3 → 0 < t → t ≤ 1 →
        1 ≤ μ * a * ℓ ^ 2 → (n : ℝ) ≤ 2 * μ * ℓ ^ 3 → 𝓜 ≤ μ * ℓ ^ 3 → 0 ≤ 𝓜 →
        A ≤ CA * (R / ℓ) ^ 2 * a → |W1| ≤ CW * a → |W1w| ≤ CW * a →
        δ ≤ Cd * t ^ L → 0 ≤ δ →
        2 * (ℓ ^ 3)⁻¹ * (4 * A + δ * (|W1| + |W1w|)) * (n : ℝ) ^ 2
          + 2 * μ * (A + δ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜)
          + 2 * μ * |W1| * δ * (n : ℝ)
        ≤ (1 / 2) * C * μ ^ 2 * R ^ 2 * ℓ ^ 3 * t / a := by
  refine ⟨1000 * (CA + Cd * CW * a ^ 2 / R ^ 2 + 1), by positivity, ?_⟩
  intro μ ℓ 𝓜 A W1 W1w δ t n hμ hℓ ht htpos htle h1 h2 h3 h4 hA hW1 hW1w hδ hδnn
  have hμ0 : 0 ≤ μ := hμ.le
  have hℓ0 : 0 ≤ ℓ := hℓ.le
  have ha0 : 0 ≤ a := ha.le
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hane : a ≠ 0 := ne_of_gt ha
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hℓinv3 : 0 ≤ (ℓ^3)⁻¹ := by positivity
  -- `t ^ L ≤ μ * a ^ 3`
  have htL : t ^ L ≤ t := Real.rpow_le_self_of_le_one htpos.le htle hL
  have htLμ : t ^ L ≤ μ * a^3 := by rw [← ht]; exact htL
  have hδ' : δ ≤ Cd * (μ * a^3) := le_trans hδ (mul_le_mul_of_nonneg_left htLμ hCd)
  -- `n ^ 2` and `√(n 𝓜)` bounds
  have h2nn : 0 ≤ 2*μ*ℓ^3 := by positivity
  have hn2 : (n:ℝ)^2 ≤ 4*μ^2*ℓ^6 := by
    have hsq : (n:ℝ)^2 ≤ (2*μ*ℓ^3)^2 := pow_le_pow_left₀ hn0 h2 2
    have heq : (2*μ*ℓ^3)^2 = 4*μ^2*ℓ^6 := by ring
    linarith [hsq, heq]
  have hsqr : Real.sqrt ((n:ℝ)*𝓜) ≤ 2*μ*ℓ^3 := by
    have hstep : (n:ℝ)*𝓜 ≤ (2*μ*ℓ^3)*(μ*ℓ^3) := mul_le_mul h2 h3 h4 h2nn
    have hnM : (n:ℝ)*𝓜 ≤ (2*μ*ℓ^3)^2 := by nlinarith [hstep]
    calc Real.sqrt ((n:ℝ)*𝓜) ≤ Real.sqrt ((2*μ*ℓ^3)^2) := Real.sqrt_le_sqrt hnM
      _ = 2*μ*ℓ^3 := Real.sqrt_sq h2nn
  -- the `δ`-weighted absolute-value bounds
  have habs : |W1| + |W1w| ≤ 2*(CW*a) := by linarith [hW1, hW1w]
  have hδabs : δ*(|W1| + |W1w|) ≤ 2*Cd*CW*a^4*μ := by
    have hCD : 0 ≤ Cd*(μ*a^3) := by positivity
    have h := mul_le_mul hδ' habs (by positivity : 0 ≤ |W1| + |W1w|) hCD
    calc δ*(|W1| + |W1w|) ≤ (Cd*(μ*a^3))*(2*(CW*a)) := h
      _ = 2*Cd*CW*a^4*μ := by ring
  have hδW1 : δ * |W1| ≤ Cd*CW*a^4*μ := by
    have hCD : 0 ≤ Cd*(μ*a^3) := by positivity
    have h := mul_le_mul hδ' hW1 (abs_nonneg W1) hCD
    calc δ * |W1| ≤ (Cd*(μ*a^3))*(CW*a) := h
      _ = Cd*CW*a^4*μ := by ring
  -- bounds on the two brackets
  have hA1 : 4*A + δ*(|W1| + |W1w|) ≤ 4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ := by
    have h4 : 4*A ≤ 4*(CA*(R/ℓ)^2*a) := by linarith [hA]
    linarith [h4, hδabs]
  have hV1 : A + δ * |W1| ≤ CA*(R/ℓ)^2*a + Cd*CW*a^4*μ := by linarith [hA, hδW1]
  -- ROW 1
  have hT1 : 2 * (ℓ^3)⁻¹ * (4*A + δ*(|W1| + |W1w|)) * (n:ℝ)^2
      ≤ 32*CA*R^2*a*μ^2*ℓ + 16*Cd*CW*a^4*μ^3*ℓ^3 := by
    have h1a : 2*(ℓ^3)⁻¹*(4*A + δ*(|W1| + |W1w|))*(n:ℝ)^2
        ≤ 2*(ℓ^3)⁻¹*(4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ)*(n:ℝ)^2 := by
      have h := mul_le_mul_of_nonneg_right hA1 (by positivity : 0 ≤ 2*(n:ℝ)^2)
      have h2' := mul_le_mul_of_nonneg_left h hℓinv3
      linarith [h2']
    have h1b : 2*(ℓ^3)⁻¹*(4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ)*(n:ℝ)^2
        ≤ 8*μ^2*ℓ^3*(4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ) := by
      have h := mul_le_mul_of_nonneg_left hn2
        (by positivity : 0 ≤ 2*(ℓ^3)⁻¹*(4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ))
      have heq : 2*(ℓ^3)⁻¹*(4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ)*(4*μ^2*ℓ^6)
          = 8*μ^2*ℓ^3*(4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ) := by
        field_simp; ring
      linarith [h, heq]
    have heq2 : 8*μ^2*ℓ^3*(4*(CA*(R/ℓ)^2*a) + 2*Cd*CW*a^4*μ)
        = 32*CA*R^2*a*μ^2*ℓ + 16*Cd*CW*a^4*μ^3*ℓ^3 := by
      field_simp; ring
    exact le_trans h1a (le_trans h1b heq2.le)
  -- ROW 2
  have hT2 : 2*μ*(A + δ * |W1|)*Real.sqrt ((n:ℝ)*𝓜)
      ≤ 4*CA*R^2*a*μ^2*ℓ + 4*Cd*CW*a^4*μ^3*ℓ^3 := by
    have h1a : (A + δ * |W1|)*Real.sqrt ((n:ℝ)*𝓜)
        ≤ (CA*(R/ℓ)^2*a + Cd*CW*a^4*μ)*(2*μ*ℓ^3) :=
      mul_le_mul hV1 hsqr (Real.sqrt_nonneg _) (by positivity)
    have h1b : 2*μ*(A + δ * |W1|)*Real.sqrt ((n:ℝ)*𝓜)
        ≤ 2*μ*((CA*(R/ℓ)^2*a + Cd*CW*a^4*μ)*(2*μ*ℓ^3)) := by
      have h := mul_le_mul_of_nonneg_left h1a (by positivity : 0 ≤ 2*μ)
      linarith [h]
    have heq : 2*μ*((CA*(R/ℓ)^2*a + Cd*CW*a^4*μ)*(2*μ*ℓ^3))
        = 4*CA*R^2*a*μ^2*ℓ + 4*Cd*CW*a^4*μ^3*ℓ^3 := by
      field_simp; ring
    exact le_trans h1b heq.le
  -- ROW 3
  have hT3 : 2*μ*|W1| * δ*(n:ℝ) ≤ 4*Cd*CW*a^4*μ^3*ℓ^3 := by
    have hCD : 0 ≤ Cd*(μ*a^3) := by positivity
    have hnδ : δ*(n:ℝ) ≤ (Cd*(μ*a^3))*(2*μ*ℓ^3) := mul_le_mul hδ' h2 hn0 hCD
    have h1a : |W1| * (δ*(n:ℝ)) ≤ (CW*a)*((Cd*(μ*a^3))*(2*μ*ℓ^3)) :=
      mul_le_mul hW1 hnδ (by positivity : 0 ≤ δ*(n:ℝ)) (by positivity : 0 ≤ CW*a)
    have h1b : 2*μ*(|W1| * (δ*(n:ℝ))) ≤ 2*μ*((CW*a)*((Cd*(μ*a^3))*(2*μ*ℓ^3))) :=
      mul_le_mul_of_nonneg_left h1a (by positivity : 0 ≤ 2*μ)
    have heq : 2*μ*((CW*a)*((Cd*(μ*a^3))*(2*μ*ℓ^3))) = 4*Cd*CW*a^4*μ^3*ℓ^3 := by ring
    linarith [h1b, heq]
  -- sum of the three rows
  have hLHS : 2 * (ℓ^3)⁻¹ * (4*A + δ*(|W1| + |W1w|)) * (n:ℝ)^2
      + 2*μ*(A + δ * |W1|)*Real.sqrt ((n:ℝ)*𝓜) + 2*μ*|W1| * δ*(n:ℝ)
      ≤ 36*CA*R^2*a*μ^2*ℓ + 24*Cd*CW*a^4*μ^3*ℓ^3 := by linarith [hT1, hT2, hT3]
  -- the `CA` block, using `1 ≤ μ a ℓ²`
  have hP1 : 36*CA*R^2*a*μ^2*ℓ ≤ 500*CA*μ^3*R^2*a^2*ℓ^3 := by
    have hbase : 0 ≤ CA*R^2*a*μ^2*ℓ := by positivity
    have h36 : 36 ≤ 500*(μ*a*ℓ^2) := by nlinarith [h1]
    have h := mul_le_mul_of_nonneg_right h36 hbase
    linarith [h]
  -- the `Cd CW` block, using `(a²/R²) R² = a²`
  have hP2 : 24*Cd*CW*a^4*μ^3*ℓ^3 ≤ 500*(Cd*CW*a^2/R^2)*μ^3*R^2*a^2*ℓ^3 := by
    have hRR : (a^2/R^2)*R^2 = a^2 := div_mul_cancel₀ _ (by positivity : R^2 ≠ 0)
    have heq : 500*(Cd*CW*a^2/R^2)*μ^3*R^2*a^2*ℓ^3 = 500*(Cd*CW*a^4*μ^3*ℓ^3) := by
      calc 500*(Cd*CW*a^2/R^2)*μ^3*R^2*a^2*ℓ^3
          = 500*Cd*CW*((a^2/R^2)*R^2)*a^2*μ^3*ℓ^3 := by ring
        _ = 500*Cd*CW*a^2*a^2*μ^3*ℓ^3 := by rw [hRR]
        _ = 500*(Cd*CW*a^4*μ^3*ℓ^3) := by ring
    rw [heq]
    have hbase : 0 ≤ Cd*CW*a^4*μ^3*ℓ^3 := by positivity
    nlinarith [hbase]
  have hFin : 36*CA*R^2*a*μ^2*ℓ + 24*Cd*CW*a^4*μ^3*ℓ^3
      ≤ 500*(CA + Cd*CW*a^2/R^2 + 1)*μ^3*R^2*a^2*ℓ^3 := by
    have hB : 0 ≤ μ^3*R^2*a^2*ℓ^3 := by positivity
    have hsum : 500*CA*μ^3*R^2*a^2*ℓ^3 + 500*(Cd*CW*a^2/R^2)*μ^3*R^2*a^2*ℓ^3
        ≤ 500*(CA + Cd*CW*a^2/R^2 + 1)*μ^3*R^2*a^2*ℓ^3 := by nlinarith [hB]
    linarith [hP1, hP2, hsum]
  -- rewrite the right-hand side with `t = μ a³`
  have hgoalRHS : (1/2)*(1000*(CA + Cd*CW*a^2/R^2 + 1))*μ^2*R^2*ℓ^3*t/a
      = 500*(CA + Cd*CW*a^2/R^2 + 1)*μ^3*R^2*a^2*ℓ^3 := by
    rw [ht]
    field_simp; ring
  rw [hgoalRHS]
  exact le_trans hLHS hFin

end Work.BoseBoxFock
