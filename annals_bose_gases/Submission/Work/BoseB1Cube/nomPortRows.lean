import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.BoseB1Cube

/-- **The nominal port rows** — the pure-real ledger of
`Submission/Work/BoseB1Cube/FINDING_nomRowSqWindowRow_session4.md` §0/(E), consumed by
`Work.BoseB1Cube.nomRowSqWindowRow` (large-window branch).

With `N = n/V` and `s = S/V` (so `Q = n - S`, hence `n - s V = Q`), the difference of the two
sides is, after multiplication by `V ^ 3`, the sum of the seven rows

* `-(W Q V / 4)·(S + n - 2 μ V)`      (the demand/`a0Main` shift),
* `-(W V / 2)·(2 S + μ V)`, `-W V / 4` (the `a0MainLocBox` rows),
* `-((2+κ) Γ G χ n² + 2 G χ n Q + 2 G χ n + κ Γ G χ n)·V / 2` (the crux's residual),
* `Q·(bg V³ - Cr a (2 μ V³ + (S+n) V²))` (the gap),
* `-Cr a c³ n χ V²`                    (the port's band row),
* `Ct (μ² a Γ' χ + μ a) V³`            (the credit).

Each row is paid by exactly one group of the constants:

* the two `Q`-rows (the first one, since `S + n ≤ 2 Cn μ V` and `χ ≤ Cs V`, and the `2 G χ n Q`
  piece of the crux row) are paid by the gap's `16 π Cn Cs · a μ Q`, which is `≥ 8 + 8` of them —
  the factor `2` in `16 π Cn Cs = 2 · 8 π Cn Cs` is what makes the doubled `Kg` of the statement
  necessary; the remaining `2 Cr (1 + Cn) a μ` of the gap pays `-Cr a (2μ + s + n) Q`;
* the `a μ`-rows (second, third, `2 G χ n` and `κ Γ G χ n` pieces of the crux row) are paid by
  `Ct μ a ≥ (8 π Cs (2 Cn + 1) + 4 π Cs + 8 π Cn Cs + 4 π κ Cn Cs) a μ` via
  `χ ≤ Cs V`, `n ≤ Cn μ V`, `S ≤ Cn μ V`, `1 ≤ μ V = (μ V)`, `Γ ≤ 1` (the last one is what keeps
  the `κ Γ G χ n` row from being proportional to the unbounded `Γ'`);
* the `Γ' χ μ²`-rows (`(2+κ) Γ G χ n²` piece of the crux row, using `Γ ≤ Γ'`, `G ≤ 8 π a` and
  `n ≤ Cn μ V`, and the band row, using `c³ ≤ μ Γ'`) are paid by
  `Ct μ² a Γ' χ ≥ (4 π (2+κ) Cn² + Cr Cn) μ² a Γ' χ`. -/
theorem nomPortRows {Cn Cs Cr Ct κ bg V μ a W χ G Γ Γ' S Q n c : ℝ}
    (hCn : 3 ≤ Cn) (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hκ : 0 ≤ κ)
    (ha : 0 ≤ a) (hV : 0 < V) (hμ : 0 < μ) (hn1 : 1 ≤ n)
    (hW : 0 ≤ W) (hχ : 0 ≤ χ) (hG : 0 ≤ G) (hc0 : 0 ≤ c)
    (hΓ0 : 0 ≤ Γ) (hΓ1 : Γ ≤ 1) (hΓ'0 : 0 ≤ Γ') (hΓle : Γ ≤ Γ')
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hSQ : S + Q = n)
    (hGle : G ≤ 8 * Real.pi * a)
    (hWle : W ≤ 16 * Real.pi * a * χ)
    (hχV : χ ≤ Cs * V)
    (hμV : 1 ≤ μ * V)
    (hτ : n ≤ Cn * μ * V)
    (hcube : c ^ 3 ≤ μ * Γ')
    (hGap : (16 * Real.pi * Cn * Cs + 2 * Cr * (1 + Cn)) * (a * μ) ≤ bg)
    (hC : 8 * Real.pi * Cs * (2 * Cn + 1) + 4 * Real.pi * Cs + 8 * Real.pi * Cn * Cs
            + 4 * Real.pi * κ * Cn * Cs + 4 * Real.pi * (2 + κ) * Cn ^ 2 + Cr * Cn ≤ Ct) :
    (1 / 4) * ((n / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W
      ≤ ((1 / 4) * ((S / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W
            - (W / (2 * V)) * (2 * (S / V) + μ) - W / (4 * V ^ 2))
          - (((2 + κ) * Γ * G * χ * n ^ 2 + 2 * G * χ * n * Q + 2 * G * χ * n
                + κ * Γ * G * χ * n) / (2 * V ^ 2))
          + bg * Q
          - Cr * a * (μ + S / V) * Q - Cr * a * (μ + n / V) * Q
          - Cr * a * c ^ 3 * (n / V) * χ
          + Ct * (μ ^ 2 * a * Γ' * χ + μ * a) := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hV3 : (0 : ℝ) < V ^ 3 := by positivity
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hSle : S ≤ Cn * μ * V := by linarith
  -- The cleared (multiplied by `V^3`) difference of the two sides, split into the seven rows.
  have hid : V ^ 3 * ((((1 / 4) * ((S / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W
            - (W / (2 * V)) * (2 * (S / V) + μ) - W / (4 * V ^ 2))
          - (((2 + κ) * Γ * G * χ * n ^ 2 + 2 * G * χ * n * Q + 2 * G * χ * n
                + κ * Γ * G * χ * n) / (2 * V ^ 2))
          + bg * Q
          - Cr * a * (μ + S / V) * Q - Cr * a * (μ + n / V) * Q
          - Cr * a * c ^ 3 * (n / V) * χ
          + Ct * (μ ^ 2 * a * Γ' * χ + μ * a))
        - ((1 / 4) * ((n / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W))
      = (-(W * Q * V / 4) * (S + n - 2 * μ * V))
        + (-(W * V / 2) * (2 * S + μ * V))
        + (-W * V / 4)
        + (-(((2 + κ) * Γ * G * χ * n ^ 2 + 2 * G * χ * n * Q + 2 * G * χ * n
              + κ * Γ * G * χ * n) * V / 2))
        + (Q * (bg * V ^ 3 - Cr * a * (2 * μ * V ^ 3 + (S + n) * V ^ 2)))
        + (-Cr * a * c ^ 3 * n * χ * V ^ 2)
        + (Ct * (μ ^ 2 * a * Γ' * χ + μ * a) * V ^ 3) := by
    rw [← hSQ]
    field_simp
    ring
  -- ## the seven rows
  have hb1 : -(8 * Real.pi * Cn * Cs * a * μ * Q * V ^ 3)
      ≤ -(W * Q * V / 4) * (S + n - 2 * μ * V) := by
    have hXZ : S + n - 2 * μ * V ≤ 2 * Cn * μ * V := by nlinarith [hSle, hτ, mul_pos hμ hV]
    rcases le_or_gt (S + n - 2 * μ * V) 0 with h | h
    · have h1 : (0 : ℝ) ≤ W * Q * V / 4 := by positivity
      have h2 : (W * Q * V / 4) * (S + n - 2 * μ * V) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h1 h
      have h3 : (0 : ℝ) ≤ 8 * Real.pi * Cn * Cs * a * μ * Q * V ^ 3 := by positivity
      linarith
    · have hkey : W * Q * V * (S + n - 2 * μ * V)
          ≤ 32 * Real.pi * Cn * Cs * a * μ * Q * V ^ 3 := by
        calc W * Q * V * (S + n - 2 * μ * V)
            = W * (Q * V * (S + n - 2 * μ * V)) := by ring
          _ ≤ 16 * Real.pi * a * χ * (Q * V * (S + n - 2 * μ * V)) := by gcongr
          _ = 16 * Real.pi * a * (χ * (Q * V * (S + n - 2 * μ * V))) := by ring
          _ ≤ 16 * Real.pi * a * ((Cs * V) * (Q * V * (S + n - 2 * μ * V))) := by gcongr
          _ ≤ 16 * Real.pi * a * ((Cs * V) * (Q * V * (2 * Cn * μ * V))) := by gcongr
          _ = 32 * Real.pi * Cn * Cs * a * μ * Q * V ^ 3 := by ring
      linarith
  have hb2 : -(8 * Real.pi * Cs * (2 * Cn + 1) * a * μ) * V ^ 3
      ≤ -(W * V / 2) * (2 * S + μ * V) := by
    have h3 : 2 * S + μ * V ≤ (2 * Cn + 1) * μ * V := by nlinarith [hSle, mul_pos hμ hV]
    have hkey : W * V * (2 * S + μ * V)
        ≤ 16 * Real.pi * Cs * (2 * Cn + 1) * a * μ * V ^ 3 := by
      calc W * V * (2 * S + μ * V)
          = W * (V * (2 * S + μ * V)) := by ring
        _ ≤ 16 * Real.pi * a * χ * (V * (2 * S + μ * V)) := by gcongr
        _ = 16 * Real.pi * a * (χ * (V * (2 * S + μ * V))) := by ring
        _ ≤ 16 * Real.pi * a * ((Cs * V) * (V * (2 * S + μ * V))) := by gcongr
        _ ≤ 16 * Real.pi * a * ((Cs * V) * (V * ((2 * Cn + 1) * μ * V))) := by gcongr
        _ = 16 * Real.pi * Cs * (2 * Cn + 1) * a * μ * V ^ 3 := by ring
    linarith
  have hb3 : -(4 * Real.pi * Cs * a * μ) * V ^ 3 ≤ -W * V / 4 := by
    have hsq : V ^ 2 ≤ V ^ 2 * (μ * V) := by
      have h := mul_le_mul_of_nonneg_left hμV (by positivity : (0 : ℝ) ≤ V ^ 2)
      simpa using h
    have hkey : W * V ≤ 16 * Real.pi * Cs * a * μ * V ^ 3 := by
      calc W * V ≤ 16 * Real.pi * a * χ * V := by gcongr
        _ = 16 * Real.pi * a * (χ * V) := by ring
        _ ≤ 16 * Real.pi * a * ((Cs * V) * V) := by gcongr
        _ = 16 * Real.pi * Cs * a * V ^ 2 := by ring
        _ ≤ 16 * Real.pi * Cs * a * (V ^ 2 * (μ * V)) := by gcongr
        _ = 16 * Real.pi * Cs * a * μ * V ^ 3 := by ring
    linarith
  have hb4 : -(4 * Real.pi * (2 + κ) * Cn ^ 2 * a * Γ' * χ * μ ^ 2 + 8 * Real.pi * Cn * Cs * a * μ * Q
        + 8 * Real.pi * Cn * Cs * a * μ + 4 * Real.pi * κ * Cn * Cs * a * μ) * V ^ 3
      ≤ -(((2 + κ) * Γ * G * χ * n ^ 2 + 2 * G * χ * n * Q + 2 * G * χ * n
            + κ * Γ * G * χ * n) * V / 2) := by
    have hncm : (0 : ℝ) ≤ Cn * μ * V := by positivity
    have hsq : n ^ 2 ≤ Cn ^ 2 * μ ^ 2 * V ^ 2 := by nlinarith [hτ, hn0, hncm]
    have hA : (2 + κ) * Γ * G * χ * n ^ 2
        ≤ 8 * Real.pi * (2 + κ) * Cn ^ 2 * a * Γ' * χ * μ ^ 2 * V ^ 2 := by
      calc (2 + κ) * Γ * G * χ * n ^ 2 ≤ (2 + κ) * Γ' * G * χ * n ^ 2 := by gcongr
        _ ≤ (2 + κ) * Γ' * (8 * Real.pi * a) * χ * n ^ 2 := by gcongr
        _ = 8 * Real.pi * (2 + κ) * Γ' * a * χ * n ^ 2 := by ring
        _ ≤ 8 * Real.pi * (2 + κ) * Γ' * a * χ * (Cn ^ 2 * μ ^ 2 * V ^ 2) := by gcongr
        _ = 8 * Real.pi * (2 + κ) * Cn ^ 2 * a * Γ' * χ * μ ^ 2 * V ^ 2 := by ring
    have hB : 2 * G * χ * n * Q ≤ 16 * Real.pi * Cn * Cs * a * μ * Q * V ^ 2 := by
      calc 2 * G * χ * n * Q ≤ 2 * (8 * Real.pi * a) * χ * n * Q := by gcongr
        _ = 16 * Real.pi * a * χ * n * Q := by ring
        _ ≤ 16 * Real.pi * a * (Cs * V) * n * Q := by gcongr
        _ = 16 * Real.pi * a * Cs * V * n * Q := by ring
        _ ≤ 16 * Real.pi * a * Cs * V * (Cn * μ * V) * Q := by gcongr
        _ = 16 * Real.pi * Cn * Cs * a * μ * Q * V ^ 2 := by ring
    have hB' : 2 * G * χ * n ≤ 16 * Real.pi * Cn * Cs * a * μ * V ^ 2 := by
      calc 2 * G * χ * n ≤ 2 * (8 * Real.pi * a) * χ * n := by gcongr
        _ = 16 * Real.pi * a * χ * n := by ring
        _ ≤ 16 * Real.pi * a * (Cs * V) * n := by gcongr
        _ = 16 * Real.pi * a * Cs * V * n := by ring
        _ ≤ 16 * Real.pi * a * Cs * V * (Cn * μ * V) := by gcongr
        _ = 16 * Real.pi * Cn * Cs * a * μ * V ^ 2 := by ring
    have hD : κ * Γ * G * χ * n ≤ 8 * Real.pi * κ * Cn * Cs * a * μ * V ^ 2 := by
      calc κ * Γ * G * χ * n ≤ κ * 1 * G * χ * n := by gcongr
        _ ≤ κ * 1 * (8 * Real.pi * a) * χ * n := by gcongr
        _ = 8 * Real.pi * κ * a * χ * n := by ring
        _ ≤ 8 * Real.pi * κ * a * (Cs * V) * n := by gcongr
        _ = 8 * Real.pi * κ * a * Cs * V * n := by ring
        _ ≤ 8 * Real.pi * κ * a * Cs * V * (Cn * μ * V) := by gcongr
        _ = 8 * Real.pi * κ * Cn * Cs * a * μ * V ^ 2 := by ring
    nlinarith [hA, hB, hB', hD, hV]
  have hb5 : 16 * Real.pi * Cn * Cs * a * μ * Q * V ^ 3
      ≤ Q * (bg * V ^ 3 - Cr * a * (2 * μ * V ^ 3 + (S + n) * V ^ 2)) := by
    have hSneq : S + n ≤ 2 * Cn * μ * V := by nlinarith [hSle, hτ, mul_pos hμ hV]
    have h2 : Cr * a * (2 * μ * V ^ 3 + (S + n) * V ^ 2)
        ≤ 2 * Cr * a * μ * V ^ 3 + 2 * Cr * Cn * a * μ * V ^ 3 := by
      have h2a : Cr * a * (2 * μ * V ^ 3 + (S + n) * V ^ 2)
          ≤ Cr * a * (2 * μ * V ^ 3 + (2 * Cn * μ * V) * V ^ 2) := by gcongr
      have h2b : Cr * a * (2 * μ * V ^ 3 + (2 * Cn * μ * V) * V ^ 2)
          = 2 * Cr * a * μ * V ^ 3 + 2 * Cr * Cn * a * μ * V ^ 3 := by ring
      linarith
    have h1 : 16 * Real.pi * Cn * Cs * a * μ * V ^ 3 + 2 * Cr * (1 + Cn) * a * μ * V ^ 3
        ≤ bg * V ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hGap (by positivity : (0 : ℝ) ≤ V ^ 3)
      linarith [h]
    have hkey : 16 * Real.pi * Cn * Cs * a * μ * V ^ 3
        ≤ bg * V ^ 3 - Cr * a * (2 * μ * V ^ 3 + (S + n) * V ^ 2) := by linarith
    have h := mul_le_mul_of_nonneg_left hkey hQ
    linarith [h]
  have hb6 : -(Cr * Cn * a * Γ' * χ * μ ^ 2) * V ^ 3 ≤ -Cr * a * c ^ 3 * n * χ * V ^ 2 := by
    have h1 : c ^ 3 * n ≤ (μ * Γ') * (Cn * μ * V) :=
      mul_le_mul hcube hτ hn0 (mul_nonneg (le_of_lt hμ) hΓ'0)
    have h2 : Cr * a * c ^ 3 * n * χ * V ^ 2
        ≤ Cr * a * (μ * Γ') * (Cn * μ * V) * χ * V ^ 2 := by gcongr
    have h3 : Cr * a * (μ * Γ') * (Cn * μ * V) * χ * V ^ 2
        = Cr * Cn * a * Γ' * χ * μ ^ 2 * V ^ 3 := by ring
    linarith
  have hb7 : Ct * (μ ^ 2 * a * Γ' * χ + μ * a) * V ^ 3
      ≤ Ct * (μ ^ 2 * a * Γ' * χ + μ * a) * V ^ 3 := le_refl _
  -- the payer: `Ct` minus the two groups of `hC`
  have hsum : (0 : ℝ) ≤ V ^ 3 * (a * μ * (Ct - (8 * Real.pi * Cs * (2 * Cn + 1) + 4 * Real.pi * Cs
        + 8 * Real.pi * Cn * Cs + 4 * Real.pi * κ * Cn * Cs))
      + a * Γ' * χ * μ ^ 2 * (Ct - (4 * Real.pi * (2 + κ) * Cn ^ 2 + Cr * Cn))) := by
    have hba : (0 : ℝ) ≤ 8 * Real.pi * Cs * (2 * Cn + 1) + 4 * Real.pi * Cs + 8 * Real.pi * Cn * Cs
        + 4 * Real.pi * κ * Cn * Cs := by positivity
    have hbb : (0 : ℝ) ≤ 4 * Real.pi * (2 + κ) * Cn ^ 2 + Cr * Cn := by positivity
    have hA1 : (0 : ℝ) ≤ Ct - (8 * Real.pi * Cs * (2 * Cn + 1) + 4 * Real.pi * Cs
        + 8 * Real.pi * Cn * Cs + 4 * Real.pi * κ * Cn * Cs) := by linarith
    have hA2 : (0 : ℝ) ≤ Ct - (4 * Real.pi * (2 + κ) * Cn ^ 2 + Cr * Cn) := by linarith
    have h1 : (0 : ℝ) ≤ a * μ * (Ct - (8 * Real.pi * Cs * (2 * Cn + 1) + 4 * Real.pi * Cs
        + 8 * Real.pi * Cn * Cs + 4 * Real.pi * κ * Cn * Cs)) :=
      mul_nonneg (mul_nonneg ha hμ.le) hA1
    have h2 : (0 : ℝ) ≤ a * Γ' * χ * μ ^ 2 * (Ct - (4 * Real.pi * (2 + κ) * Cn ^ 2 + Cr * Cn)) :=
      mul_nonneg (by positivity) hA2
    exact mul_nonneg (by positivity) (add_nonneg h1 h2)
  have key : (0 : ℝ) ≤ V ^ 3 * ((((1 / 4) * ((S / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W
            - (W / (2 * V)) * (2 * (S / V) + μ) - W / (4 * V ^ 2))
          - (((2 + κ) * Γ * G * χ * n ^ 2 + 2 * G * χ * n * Q + 2 * G * χ * n
                + κ * Γ * G * χ * n) / (2 * V ^ 2))
          + bg * Q
          - Cr * a * (μ + S / V) * Q - Cr * a * (μ + n / V) * Q
          - Cr * a * c ^ 3 * (n / V) * χ
          + Ct * (μ ^ 2 * a * Γ' * χ + μ * a))
        - ((1 / 4) * ((n / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W)) := by
    rw [hid]
    linarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hsum]
  have hRL : (0 : ℝ) ≤ (((1 / 4) * ((S / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W
            - (W / (2 * V)) * (2 * (S / V) + μ) - W / (4 * V ^ 2))
          - (((2 + κ) * Γ * G * χ * n ^ 2 + 2 * G * χ * n * Q + 2 * G * χ * n
                + κ * Γ * G * χ * n) / (2 * V ^ 2))
          + bg * Q
          - Cr * a * (μ + S / V) * Q - Cr * a * (μ + n / V) * Q
          - Cr * a * c ^ 3 * (n / V) * χ
          + Ct * (μ ^ 2 * a * Γ' * χ + μ * a))
        - ((1 / 4) * ((n / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W) :=
    nonneg_of_mul_nonneg_right key hV3
  linarith

end Work.BoseB1Cube
