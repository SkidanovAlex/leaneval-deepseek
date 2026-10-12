import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Goal-3 core of thm:smallbox — the final convexity (FS "this easily implies")

(Work-in-progress module; Session-196.  Self-contained pure-real lemmas,
no corpus objects — the Goal-3 content of the `smallbox_dl_energy_bound`
body decomposition recorded in SmallBoxDesignNote.md Session-196.)

FS `final_v2.tex` thm:smallbox proof ends (lines ~4050–4065) with the block
bound, in densities `x := n/|B|`, `y := n''/|B|` (`n = m·n′+n″`,
`n′/|B| ∈ [C_n·μ,(C_n+1)·μ)`, `n″ < n′`), after the m=0 (n = n″) and
m ≥ 1 (n = m·n′+n″, `x − y ≥ C_n·μ`) cases:

    ¼(y−μ)² + (1/18)·μ·(x−y)  ≥  c·(x−μ)²/(1+x/μ)        (some universal c)

— then multiplied by `∬w_{1,B} ≥ 0` and combined with the `−½μ²·∬w₁`
block (present on both sides) gives the theorem's density term
`c·(x−μ)²/(1+x/μ)·∬w₁ − ½μ²·∬w₁`.  This module proves that convexity step
with explicit universal constants (`C_n := 8`, `c := 1/50`, `0 < c < 1/2`):

  * `smallboxConvex_count`  (m = 0: `y = x`):
    `¼(x−μ)² ≥ c·(x−μ)²/(1+x/μ)` for `μ > 0`, `x ≥ 0`, `0 ≤ c ≤ 1/4`;
  * `smallboxConvex_block_lin`  (m ≥ 1, denominator-free):
    `¼(y−μ)² + (1/18)μ(x−y) ≥ (1/50)·μ·(x−μ)` for `μ > 0`, `0 ≤ y`,
    `x − y ≥ C·μ` with `C ≥ 8`;
  * `smallboxConvex_block`  (m ≥ 1): with the same hypotheses
    `¼(y−μ)² + (1/18)μ(x−y) ≥ (1/50)·(x−μ)²/(1+x/μ)` (uses `x ≥ 8μ` so
    `(x−μ)²/(1+x/μ) ≤ μ(x−μ)`).

Margins (on paper): the block case reduces to a quadratic in `y`
(`¼(y−μ)² − (1/50)μ(y−μ) ≥ −μ²/2500` by completing the square) plus
`(8/225)μ(x−y) ≥ (64/225)μ²` — slack `(64/225 − 1/2500)μ² > 0`.  The
exact `C_n`/`c` may be retuned when the Goal-1/2 assembly freezes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Real

namespace Submission.BoseGases

/-- **m = 0 arm of the final convexity**: `¼(x−μ)² ≥ c·(x−μ)²/(1+x/μ)`
for `μ > 0`, `x ≥ 0`, `0 ≤ c ≤ 1/4` — since `(x−μ)² ≥ 0`,
`1/(1+x/μ) ≤ 1` and `c ≤ 1/4`. -/
lemma smallboxConvex_count {μ x c : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 / 4) :
    (1 / 4 : ℝ) * (x - μ) ^ 2 ≥ c * ((x - μ) ^ 2 / (1 + x / μ)) := by
  have hden_ge : 1 ≤ 1 + x / μ := by
    exact le_add_of_nonneg_right (div_nonneg hx (le_of_lt hμ))
  have hden_pos : 0 < 1 + x / μ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hden_ge
  have hinv : (1 + x / μ)⁻¹ ≤ 1 := by
    have h := (inv_le_inv₀ hden_pos (by norm_num : (0 : ℝ) < 1)).mpr hden_ge
    simpa using h
  have hsq : 0 ≤ (x - μ) ^ 2 := sq_nonneg (x - μ)
  have hmain : (1 / 4 : ℝ) * (x - μ) ^ 2 ≥ c * (x - μ) ^ 2 := by
    have hd : 0 ≤ (1 / 4 : ℝ) - c := by linarith
    have h' : (1 / 4 : ℝ) * (x - μ) ^ 2 - c * (x - μ) ^ 2 ≥ 0 := by
      have h : (1 / 4 : ℝ) * (x - μ) ^ 2 - c * (x - μ) ^ 2
          = ((1 / 4 : ℝ) - c) * (x - μ) ^ 2 := by ring
      rw [h]
      exact mul_nonneg hd hsq
    linarith
  calc
    (1 / 4 : ℝ) * (x - μ) ^ 2 ≥ c * (x - μ) ^ 2 := hmain
    _ = c * ((x - μ) ^ 2 * 1) := by ring
    _ ≥ c * ((x - μ) ^ 2 * (1 + x / μ)⁻¹) := by
        have h1 : (x - μ) ^ 2 * 1 ≥ (x - μ) ^ 2 * (1 + x / μ)⁻¹ := by
          simpa using (mul_le_mul_of_nonneg_left hinv hsq)
        exact mul_le_mul_of_nonneg_left h1 hc0
    _ = c * ((x - μ) ^ 2 / (1 + x / μ)) := by
        rfl

/-- **m ≥ 1 arm of the final convexity, denominator-free form**: with
`x − y ≥ C·μ` (`C ≥ 8`, `y ≥ 0`, `μ > 0`), the block bound dominates the
linear comparison `(1/50)·μ·(x−μ)`:

    ¼(y−μ)² + (1/18)·μ·(x−y) ≥ (1/50)·μ·(x−μ).  -/
lemma smallboxConvex_block_lin {μ C x y : ℝ} (hμ : 0 < μ) (hC : 8 ≤ C)
    (hy : 0 ≤ y) (hxy : C * μ ≤ x - y) :
    (1 / 4 : ℝ) * (y - μ) ^ 2 + (1 / 18 : ℝ) * μ * (x - y)
      ≥ (1 / 50 : ℝ) * μ * (x - μ) := by
  have hC8 : 0 ≤ C - 8 := by linarith
  have hCμ : 8 * μ ≤ C * μ := by
    nlinarith [mul_nonneg hC8 (le_of_lt hμ)]
  have hxy8 : 8 * μ ≤ x - y := le_trans hCμ hxy
  have hx : μ ≤ x := by nlinarith [hxy8, hy, hμ]
  -- completing the square in y: ¼(y−μ)² − (1/50)μ(y−μ) ≥ −μ²/2500
  have hsq : (1 / 4 : ℝ) * (y - μ) ^ 2 - (1 / 50 : ℝ) * μ * (y - μ)
      ≥ - (1 / 2500 : ℝ) * μ ^ 2 := by
    have hsq' : (1 / 4 : ℝ) * (y - μ) ^ 2 - (1 / 50 : ℝ) * μ * (y - μ)
        = (1 / 4 : ℝ) * ((y - μ) - (1 / 25 : ℝ) * μ) ^ 2 - (1 / 2500 : ℝ) * μ ^ 2 := by ring
    rw [hsq']
    nlinarith [sq_nonneg ((y - μ) - (1 / 25 : ℝ) * μ)]
  -- (8/225)·μ·(x−y) ≥ (64/225)·μ² from x−y ≥ 8μ
  have hz : (1 / 18 : ℝ) * μ * (x - y) - (1 / 50 : ℝ) * μ * (x - y)
      ≥ (64 / 225 : ℝ) * μ ^ 2 := by
    have hz1 : (8 / 225 : ℝ) * μ * (8 * μ) ≤ (8 / 225 : ℝ) * μ * (x - y) := by
      exact mul_le_mul_of_nonneg_left hxy8 (by positivity : 0 ≤ (8 / 225 : ℝ) * μ)
    have hz1' : (8 / 225 : ℝ) * μ * (x - y) ≥ (64 / 225 : ℝ) * μ ^ 2 := by
      nlinarith [hz1]
    have hc : (1 / 18 : ℝ) - (1 / 50 : ℝ) = 8 / 225 := by norm_num
    nlinarith [hz1', hc]
  -- assemble: LHS − RHS = [¼(y−μ)² − (1/50)μ(y−μ)] + (8/225)μ(x−y)
  have hμ2 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have hμcoef : 0 ≤ (64 / 225 : ℝ) - (1 / 2500 : ℝ) := by norm_num
  nlinarith [hsq, hz, mul_nonneg hμcoef hμ2]

/-- **m ≥ 1 arm of the final convexity**: `¼(y−μ)² + (1/18)·μ·(x−y) ≥
(1/50)·(x−μ)²/(1+x/μ)` for `μ > 0`, `0 ≤ y`, `x − y ≥ C·μ` with `C ≥ 8`
(so `x ≥ 8μ ≥ μ`, and `(x−μ)²/(1+x/μ) = μ(x−μ)²/(x+μ) ≤ μ(x−μ)`). -/
lemma smallboxConvex_block {μ C x y : ℝ} (hμ : 0 < μ) (hC : 8 ≤ C)
    (hy : 0 ≤ y) (hxy : C * μ ≤ x - y) :
    (1 / 4 : ℝ) * (y - μ) ^ 2 + (1 / 18 : ℝ) * μ * (x - y)
      ≥ (1 / 50 : ℝ) * ((x - μ) ^ 2 / (1 + x / μ)) := by
  have hlin := smallboxConvex_block_lin hμ hC hy hxy
  have hC8 : 0 ≤ C - 8 := by linarith
  have hCμ : 8 * μ ≤ C * μ := by
    nlinarith [mul_nonneg hC8 (le_of_lt hμ)]
  have hxy8 : 8 * μ ≤ x - y := le_trans hCμ hxy
  have hx : μ ≤ x := by nlinarith [hxy8, hy, hμ]
  have hx0 : 0 ≤ x := le_trans (le_of_lt hμ) hx
  have hden_pos : 0 < 1 + x / μ := by
    exact add_pos_of_pos_of_nonneg (by norm_num) (div_nonneg hx0 (le_of_lt hμ))
  have hxμ0 : 0 ≤ x - μ := sub_nonneg.mpr hx
  have hbnd : (x - μ) ^ 2 / (1 + x / μ) ≤ μ * (x - μ) := by
    rw [div_le_iff₀ hden_pos]
    calc
      (x - μ) ^ 2 = (x - μ) * (x - μ) := by ring
      _ ≤ (x - μ) * (x + μ) := by
          exact mul_le_mul_of_nonneg_left (by nlinarith [hμ]) hxμ0
      _ = μ * (x - μ) * (1 + x / μ) := by
          field_simp [ne_of_gt hμ]
          ring
  have hlinR : (1 / 50 : ℝ) * ((x - μ) ^ 2 / (1 + x / μ)) ≤ (1 / 50 : ℝ) * μ * (x - μ) := by
    have hb' : (1 / 50 : ℝ) * ((x - μ) ^ 2 / (1 + x / μ)) ≤ (1 / 50 : ℝ) * (μ * (x - μ)) :=
      mul_le_mul_of_nonneg_left hbnd (by norm_num : 0 ≤ (1 / 50 : ℝ))
    simpa [mul_assoc] using hb'
  exact le_trans hlinR hlin

end BoseGases

end Submission
