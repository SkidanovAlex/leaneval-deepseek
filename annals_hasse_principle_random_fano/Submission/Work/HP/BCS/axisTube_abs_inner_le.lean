import Mathlib

/-!
# The axis-tube inequality `Work.HP.BCS.axisTube_abs_inner_le`

For a unit vector `w` and a point `y` on the cone surface
`{|⟪y,w⟫| = γ‖y‖}` (`0 ≤ γ < 1`), the quantity

`f(z) = |⟪z,w⟫| - β‖z - ⟪z,w⟫ • w‖`,   with   `β = γ / √(1 - γ²)`,

vanishes at `y`, and is `(1 + β)`-Lipschitz on the whole space.  Hence on an
`r`-neighbourhood of `y` (the axis tube) one has `|f(x)| ≤ r(1 + β)`.

The proof rests on two elementary facts about the orthogonal projection
`z ↦ z - ⟪z,w⟫ • w` onto the hyperplane orthogonal to `w`:

* `axisTube_proj_norm_sq` : `‖z - ⟪z,w⟫ • w‖² = ‖z‖² - ⟪z,w⟫²`;
* `axisTube_proj_norm_le` : `‖z - ⟪z,w⟫ • w‖ ≤ ‖z‖` (a consequence via Pythagoras),
  which is really the statement that the projection is a contraction.

Together with `f(y) = 0` this gives the Lipschitz estimate by the reverse
triangle inequality.
-/

namespace Work.HP.BCS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pythagoras for the orthogonal projection onto `wᗮ` (with `‖w‖ = 1`):
`‖z - ⟪z,w⟫ • w‖² = ‖z‖² - ⟪z,w⟫²`. -/
lemma axisTube_proj_norm_sq (w : E) (hw : ‖w‖ = 1) (z : E) :
    ‖z - (inner ℝ z w) • w‖ ^ 2 = ‖z‖ ^ 2 - (inner ℝ z w) ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hw, mul_one, sq_abs]
  ring

/-- The orthogonal projection onto `wᗮ` is a contraction (with `‖w‖ = 1`). -/
lemma axisTube_proj_norm_le (w : E) (hw : ‖w‖ = 1) (z : E) :
    ‖z - (inner ℝ z w) • w‖ ≤ ‖z‖ := by
  have h := axisTube_proj_norm_sq w hw z
  have hle : ‖z - (inner ℝ z w) • w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (inner ℝ z w)]
  have := (sq_le_sq.mp hle)
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this

/-- The projection onto `wᗮ` is additive: `proj x - proj y = proj (x - y)`. -/
lemma axisTube_proj_sub (w : E) (x y : E) :
    (x - (inner ℝ x w) • w) - (y - (inner ℝ y w) • w)
      = (x - y) - (inner ℝ (x - y) w) • w := by
  rw [inner_sub_left]
  module

theorem axisTube_abs_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) (hw : ‖w‖ = 1) {γ β r : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hβ : β = γ / Real.sqrt (1 - γ ^ 2)) (hr : 0 ≤ r)
    {x y : E} (hy : |inner ℝ y w| = γ * ‖y‖) (hxy : ‖x - y‖ ≤ r) :
    abs (abs (inner ℝ x w) - β * ‖x - (inner ℝ x w) • w‖) ≤ r * (1 + β) := by
  have hγsq : γ ^ 2 < 1 := by nlinarith
  have hsqrt_pos : 0 < Real.sqrt (1 - γ ^ 2) := by
    rw [Real.sqrt_pos]; linarith
  have hs : Real.sqrt (1 - γ ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  have hβ0 : 0 ≤ β := by rw [hβ]; exact div_nonneg hγ0 hsqrt_pos.le
  -- `y` lies on the cone surface: `‖y - ⟪y,w⟫ • w‖ = √(1 - γ²) ‖y‖`.
  have hproj_norm_y : ‖y - (inner ℝ y w) • w‖ = Real.sqrt (1 - γ ^ 2) * ‖y‖ := by
    have hcy : (inner ℝ y w) ^ 2 = γ ^ 2 * ‖y‖ ^ 2 := by
      have h2 := congrArg (fun t : ℝ => t ^ 2) hy
      rw [sq_abs] at h2
      rw [h2]; ring
    have hkey : ‖y - (inner ℝ y w) • w‖ ^ 2 = (1 - γ ^ 2) * ‖y‖ ^ 2 := by
      rw [axisTube_proj_norm_sq w hw y, hcy]; ring
    rw [← Real.sqrt_sq (norm_nonneg (y - (inner ℝ y w) • w)), hkey,
      Real.sqrt_mul (x := 1 - γ ^ 2) (by linarith) (‖y‖ ^ 2),
      Real.sqrt_sq (norm_nonneg y)]
  -- Consequently `f y = 0`.
  have hfy : abs (inner ℝ y w) - β * ‖y - (inner ℝ y w) • w‖ = 0 := by
    have hfy' : β * ‖y - (inner ℝ y w) • w‖ = γ * ‖y‖ := by
      rw [hβ, hproj_norm_y, ← mul_assoc, div_mul_cancel₀ _ hs]
    rw [hy, hfy']; ring
  -- The projection is a contraction, hence `|‖proj x‖ - ‖proj y‖| ≤ ‖x - y‖`.
  have hproj_lip : ‖(x - (inner ℝ x w) • w) - (y - (inner ℝ y w) • w)‖ ≤ ‖x - y‖ := by
    rw [axisTube_proj_sub w x y]
    exact axisTube_proj_norm_le w hw (x - y)
  -- `| |⟪x,w⟫| - |⟪y,w⟫| | ≤ ‖x - y‖`.
  have h1 : abs (abs (inner ℝ x w) - abs (inner ℝ y w)) ≤ ‖x - y‖ := by
    have h := abs_abs_sub_abs_le_abs_sub (inner ℝ x w) (inner ℝ y w)
    have h2 : abs (inner ℝ x w - inner ℝ y w) ≤ ‖x - y‖ := by
      rw [← inner_sub_left]
      calc abs (inner ℝ (x - y) w) ≤ ‖x - y‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ = ‖x - y‖ := by rw [hw, mul_one]
    linarith
  -- `| ‖proj x‖ - ‖proj y‖ | ≤ ‖x - y‖`.
  have h2 : abs (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖) ≤ ‖x - y‖ := by
    have h := abs_norm_sub_norm_le (x - (inner ℝ x w) • w) (y - (inner ℝ y w) • w)
    linarith [h, hproj_lip]
  -- Lipschitz estimate for `f`.
  have hlip : abs ((abs (inner ℝ x w) - β * ‖x - (inner ℝ x w) • w‖)
      - (abs (inner ℝ y w) - β * ‖y - (inner ℝ y w) • w‖)) ≤ (1 + β) * ‖x - y‖ := by
    have hkey : abs (inner ℝ x w) - β * ‖x - (inner ℝ x w) • w‖
        - (abs (inner ℝ y w) - β * ‖y - (inner ℝ y w) • w‖)
        = (abs (inner ℝ x w) - abs (inner ℝ y w))
          - β * (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖) := by ring
    rw [hkey]
    have hAB : abs ((abs (inner ℝ x w) - abs (inner ℝ y w))
        - β * (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖))
        ≤ abs (abs (inner ℝ x w) - abs (inner ℝ y w))
          + abs (β * (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖)) := by
      have h := abs_add_le (abs (inner ℝ x w) - abs (inner ℝ y w))
        (-(β * (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖)))
      rwa [abs_neg, ← sub_eq_add_neg] at h
    have habsb : abs (β * (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖))
        = β * abs (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖) := by
      rw [abs_mul, abs_of_nonneg hβ0]
    rw [habsb] at hAB
    have h3 : β * abs (‖x - (inner ℝ x w) • w‖ - ‖y - (inner ℝ y w) • w‖) ≤ β * ‖x - y‖ :=
      mul_le_mul_of_nonneg_left h2 hβ0
    linarith [hAB, h1, h3]
  calc abs (abs (inner ℝ x w) - β * ‖x - (inner ℝ x w) • w‖)
      = abs ((abs (inner ℝ x w) - β * ‖x - (inner ℝ x w) • w‖)
          - (abs (inner ℝ y w) - β * ‖y - (inner ℝ y w) • w‖)) := by rw [hfy, sub_zero]
    _ ≤ (1 + β) * ‖x - y‖ := hlip
    _ ≤ (1 + β) * r := mul_le_mul_of_nonneg_left hxy (by linarith)
    _ = r * (1 + β) := by ring

end Work.HP.BCS
