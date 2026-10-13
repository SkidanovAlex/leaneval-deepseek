import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- `y ≤ z → α^z ≤ α^y` for `0 < α ≤ 1`; a private copy of
`Work.Construction.rpow_le_of_le_one` to avoid importing the `Apriori` chapter. -/
private theorem rpow_le_of_le_one' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {y z : ℝ}
    (hyz : y ≤ z) : α ^ z ≤ α ^ y := by
  have h : α ^ z = α ^ y * α ^ (z - y) := by
    rw [← Real.rpow_add hα]
    ring_nf
  rw [h]
  calc α ^ y * α ^ (z - y) ≤ α ^ y * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hα.le y)
        exact Real.rpow_le_one hα.le hα1 (by linarith)
    _ = α ^ y := by ring

/-- `1 ≤ α^c` for `c ≤ 0` when `0 < α ≤ 1`. -/
private theorem one_le_rpow_of_nonpos {α c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : c ≤ 0) :
    1 ≤ α ^ c := by
  have h := rpow_le_of_le_one' hα hα1 (show c ≤ (0 : ℝ) from hc)
  rwa [Real.rpow_zero] at h

/-- The pure arithmetic of the *scaled* `muestimate`: for `0 < α ≤ 1` and `X ≥ 0`,
`(1/(2α))(2α² + 2α^{-1/2}X + 2α^{-3/2}X² + X) ≤ 4(α + α^{-3/2}X + α^{-5/2}X²)`.
The middle factor `α^{-1/2}X` is the `√α·X` of the scaled hypothesis, since
`√α = α^{1/2} ≤ α^{-1/2}` for `α ≤ 1`. -/
private theorem mu_arith_scaled {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    (1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)
      ≤ 4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hone1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) :=
    one_le_rpow_of_nonpos hα hα1 (by norm_num)
  have e1 : α * α ^ (-(3 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one α]
    rw [← Real.rpow_add hα]
    norm_num
  have e2 : α * α ^ (-(5 / 2 : ℝ)) = α ^ (-(3 / 2 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one α]
    rw [← Real.rpow_add hα]
    norm_num
  have hA : 2 * α ^ 2 ≤ 8 * α ^ 2 := by linarith [sq_nonneg α]
  have hXle : X ≤ α ^ (-(1 / 2 : ℝ)) * X := by
    calc X = 1 * X := by ring
      _ ≤ α ^ (-(1 / 2 : ℝ)) * X := mul_le_mul_of_nonneg_right hone1 hX
  have hB : 2 * (α ^ (-(1 / 2 : ℝ)) * X) + X ≤ 8 * (α ^ (-(1 / 2 : ℝ)) * X) := by
    linarith
  have hC : 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) ≤ 8 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    have hW : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) hX2
    exact mul_le_mul_of_nonneg_right (by norm_num) hW
  have hfin : 8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
      = 8 * α ^ 2 + 8 * (α ^ (-(1 / 2 : ℝ)) * X) + 8 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    rw [show α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)
        = α * α + (α * α ^ (-(3 / 2 : ℝ))) * X + (α * α ^ (-(5 / 2 : ℝ))) * X ^ 2 by ring]
    rw [e1, e2]
    ring
  have hB8 : 2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X) + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X
      ≤ 8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) := by
    linarith [hA, hB, hC, hfin]
  have hkey : (1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)
      ≤ (1 / (2 * α))
        * (8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))) :=
    mul_le_mul_of_nonneg_left hB8 (by positivity)
  have hsimp : (1 / (2 * α))
        * (8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)))
      = 4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    field_simp
    ring
  linarith [hkey, hsimp]

/-- The triangle inequality `|(1/(2α))((A+B) - Cc)| ≤ (1/(2α)) C₀ (2α² + 2α^{-1/2}X + 2α^{-3/2}X² + X)`
with `X ≥ 0`, from the three scaled hypotheses. -/
private theorem core (C₀ α A B Cc X : ℝ) (hC₀ : 0 < C₀) (hα : 0 < α) (hα1 : α ≤ 1)
    (hX : 0 ≤ X)
    (h1 : |A| ≤ C₀ * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h2 : |B| ≤ C₀ * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h3 : |Cc| ≤ C₀ * X) :
    |(1 / (2 * α)) * (A + B) - (1 / (2 * α)) * Cc|
      ≤ 4 * C₀ * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
  -- `√α = α^{1/2} ≤ α^{-1/2}` for `0 < α ≤ 1`
  have hsqrt : Real.sqrt α ≤ α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact rpow_le_of_le_one' hα hα1 (by norm_num)
  have hSX : Real.sqrt α * X ≤ α ^ (-(1 / 2 : ℝ)) * X :=
    mul_le_mul_of_nonneg_right hsqrt hX
  have h1' : |A| ≤ C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
    le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) hC₀.le)
  have h2' : |B| ≤ C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
    le_trans h2 (mul_le_mul_of_nonneg_left (by linarith) hC₀.le)
  -- triangle inequality for the three integrals
  have htri : |A + B - Cc| ≤ |A| + |B| + |Cc| := by
    calc |A + B - Cc| = |(A + B) + -Cc| := by ring_nf
      _ ≤ |A + B| + |-Cc| := abs_add_le _ _
      _ ≤ |A| + |B| + |Cc| := by
          rw [abs_neg]
          linarith [abs_add_le A B]
  have hstep : |A + B - Cc|
      ≤ C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
          + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X) := by
    have hsum : |A| + |B| + |Cc|
        ≤ C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
          + C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
          + C₀ * X := by
      linarith [h1', h2', h3]
    have heq : C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
          + C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) + C₀ * X
        = C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
            + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X) := by ring
    linarith [htri, hsum, heq]
  have hbound : |(1 / (2 * α)) * (A + B) - (1 / (2 * α)) * Cc|
      ≤ (1 / (2 * α)) * (C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
          + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)) := by
    have hrs : (1 / (2 * α)) * (A + B) - (1 / (2 * α)) * Cc
        = (1 / (2 * α)) * ((A + B) - Cc) := by ring
    rw [hrs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  have harith := mu_arith_scaled hα hα1 hX
  have hfac : (1 / (2 * α)) * (C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X))
      = C₀ * ((1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)) := by ring
  have hfinal : C₀ * ((1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X))
      ≤ 4 * C₀ * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_left harith hC₀.le
    calc C₀ * ((1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
          + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X))
        ≤ C₀ * (4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) := h
      _ = 4 * C₀ * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by ring
  linarith [hbound, hfac, hfinal]

/-- Elgindi, Proposition `muestimate` (tex 1508) with a *scaled* input bound, which is the form
in which §Modulation consumes it: the three `L₁₂(·)(0)`-estimates for `N₀`, `N` and `3 D_θ g/(1+z)`
produced by Propositions `N0Estimate`/`NEstimate` (via `Work.FTS.H2.L12ZeroLe`) carry a universal
constant `C₀`, so the estimate on `μ` must be stated with that constant readable off:

`|μ| ≤ C · C₀ · (α + α^{-3/2}|g|_{ℋ⁴} + α^{-5/2}|g|²_{ℋ⁴})`.

`Work.Construction.mufunS α N0v Nv g = (1/(2α))(L₁₂ N0v 0 + L₁₂ Nv 0) + (1/(2α)) L₁₂(3 D_θ g/(1+z))(0)`,
and the proof is the triangle inequality followed by the monotonicity of `α ↦ α^z` (for `0 < α ≤ 1`):
`α^{-1/2} ≤ α^{-3/2}`, `α^{-1} ≤ α^{-3/2}` and `1 ≤ α^{-3/2}`, so that
`C₀(α + α^{-1/2}X + α^{-5/2}X² + X/(2α)) ≤ C₀·2·(α + α^{-3/2}X + α^{-5/2}X²)` for `X = |g|_{ℋ⁴} ≥ 0`.
The unscaled version (hypotheses without `C₀`) is `Work.FTS.H2.MuEstimate`. -/
theorem MuEstimateScaled : ∀ (C₀ : ℝ), 0 < C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    |Work.Construction.L12 N0v 0| ≤ C₀ * (α ^ 2 + Real.sqrt α * Work.Spaces.HkNorm α 4 g
        + α ^ (-(3 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g ^ 2) →
    |Work.Construction.L12 Nv 0| ≤ C₀ * (α ^ 2 + Real.sqrt α * Work.Spaces.HkNorm α 4 g
        + α ^ (-(3 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g ^ 2) →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
        ≤ C₀ * Work.Spaces.HkNorm α 4 g →
    |Work.Construction.mufunS α N0v Nv g|
      ≤ C * C₀ * (α + α ^ (-(3 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g
        + α ^ (-(5 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g ^ 2) := by
  intro C₀ hC₀
  refine ⟨4, by norm_num, ?_⟩
  intro α N0v Nv g hα hα1 h1 h2 h3
  have hX : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  -- `mufunS = (1/(2α))((A + B) + Cc)`: feed `core` the argument `-Cc` (its own sign is unused)
  have hcore := core C₀ α (Work.Construction.L12 N0v 0) (Work.Construction.L12 Nv 0)
    (-(Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0))
    (Work.Spaces.HkNorm α 4 g) hC₀ hα hα1 hX h1 h2 (by simpa using h3)
  have hmu : Work.Construction.mufunS α N0v Nv g
      = (1 / (2 * α)) * (Work.Construction.L12 N0v 0 + Work.Construction.L12 Nv 0)
        - (1 / (2 * α))
          * (-(Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0)) := by
    rw [Work.Construction.mufunS]
    ring
  rw [hmu]
  exact hcore

end Work.FTS.H2
