import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_local
import Submission.Work.EQ.loc_model

set_option maxHeartbeats 6000000

namespace Work.EQ

/-! ## Identities relating the `loc*` functions to the model functions of
`Submission/Work/EQ/loc_model` -/

theorem locR_eq_model (a x y : ℝ) : locR a x y = LocEst.mR (locW a) x y := rfl

theorem locLy_eq_model (a x y : ℝ) : locLy a x y = LocEst.mE (locW a) x y := rfl

theorem locY_eq_model (a x y : ℝ) (hR : locR a x y ≠ 0) :
    locY a x y = LocEst.mY (locW a) x y := by
  rw [locY_eq_mul a x y hR, locLy_eq_model, LocEst.mY, LocEst.mE]

/-- `1 + (x-w)/R = y²/(R(R+w-x))` for `R = locR a x y > 0` and `x ≤ w`. -/
theorem eqU_one_add (a x y : ℝ) (hx : x ≤ locW a) (hR : 0 < locR a x y) :
    (1 : ℝ) + (x - locW a)/locR a x y
      = y^2/(locR a x y * (locR a x y + locW a - x)) := by
  set R := locR a x y
  set w := locW a
  have hden : R + w - x ≠ 0 := ne_of_gt (by linarith)
  have hsq : R^2 = (x - w)^2 + y^2 := Real.sq_sqrt (by positivity)
  have hkey : R + x - w = y^2/(R + w - x) := by
    rw [eq_div_iff hden]; nlinarith [hsq]
  have hstep : 1 + (x - w)/R = (R + x - w)/R := by field_simp; ring
  rw [hstep, hkey, div_div]
  ring

theorem locX_eq_model (a x y : ℝ) (hx : x ≤ locW a) (hR : 0 < locR a x y) :
    locX a x y = LocEst.mX (locW a) x y := by
  rw [locX, LocEst.mX, LocEst.mA, locR_eq_model]
  have h2 : (1 : ℝ) + (x - locW a)/LocEst.mR (locW a) x y
      = y^2/(LocEst.mR (locW a) x y * (LocEst.mR (locW a) x y + locW a - x)) := by
    have h := eqU_one_add a x y hx hR
    rw [locR_eq_model] at h
    exact h
  rw [show (1:ℝ) - x + (x - locW a)/LocEst.mR (locW a) x y
      = -x + (1 + (x - locW a)/LocEst.mR (locW a) x y) by ring, h2]

/-- The two-step `x`-displacement in model coordinates. -/
theorem mX_two_step (w x y : ℝ) :
    LocEst.mX w (LocEst.mX w x y) (LocEst.mY w x y) - x
      = y^2 * ((LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)
        - LocEst.mIA w x y) := by
  have hmX : ∀ u v, LocEst.mX w u v = -u + v^2 * LocEst.mIA w u v := fun u v => by
    rw [LocEst.mX, LocEst.mIA, div_eq_mul_inv]
  rw [hmX (LocEst.mX w x y) (LocEst.mY w x y), hmX x y]
  rw [LocEst.mY, LocEst.mE]
  ring

theorem locA_eq_model (a x y : ℝ) (hx : x ≤ locW a) (hX : LocEst.mX (locW a) x y ≤ locW a)
    (hR : 0 < locR a x y)
    (hmA : 0 < LocEst.mA (locW a) (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y)) :
    locA a (x, y) = y^2 * ((LocEst.mE (locW a) x y)^2
      * LocEst.mIA (locW a) (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y)
      - LocEst.mIA (locW a) x y) := by
  have hR' : 0 < locR a (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y) := by
    rw [locR_eq_model]
    have hmA' : 0 < LocEst.mR (locW a) (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y)
        * (LocEst.mR (locW a) (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y)
          + locW a - LocEst.mX (locW a) x y) := by
      rw [LocEst.mA] at hmA; exact hmA
    have h1 : 0 ≤ locW a - LocEst.mX (locW a) x y := by linarith
    have h2 : 0 ≤ LocEst.mR (locW a) (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y) :=
      Real.sqrt_nonneg _
    nlinarith [hmA', h1, h2]
  have hXid := locX_eq_model a x y hx hR
  have hYid := locY_eq_model a x y (ne_of_gt hR)
  have hXid' := locX_eq_model a (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y) hX hR'
  show locX a (locX a x y) (locY a x y) - x = _
  rw [hXid, hYid, hXid', mX_two_step]

theorem locM_eq_model (a x y : ℝ) (hx : x ≤ locW a) (hR : 0 < locR a x y) :
    locM a (x, y) = LocEst.mE (locW a) x y
      * LocEst.mE (locW a) (LocEst.mX (locW a) x y) (LocEst.mY (locW a) x y) := by
  have hXid := locX_eq_model a x y hx hR
  have hYid := locY_eq_model a x y (ne_of_gt hR)
  show locLy a x y * locLy a (locX a x y) (locY a x y) = _
  rw [hXid, hYid, locLy_eq_model, locLy_eq_model]

/-! ## Elementary helpers for combining Lipschitz bounds -/

section Helpers

/-- Difference of products: `|f₁g₁ - f₂g₂| ≤ A₁M₁ + M₂A₂` when `|g₁| ≤ M₁`, `|f₂| ≤ M₂`,
`|f₁-f₂| ≤ A₁`, `|g₁-g₂| ≤ A₂`. -/
theorem abs_mul_sub_mul_le {f₁ f₂ g₁ g₂ M₁ M₂ A₁ A₂ : ℝ}
    (hg₁ : |g₁| ≤ M₁) (hf₂ : |f₂| ≤ M₂) (hf : |f₁ - f₂| ≤ A₁) (hg : |g₁ - g₂| ≤ A₂) :
    |f₁ * g₁ - f₂ * g₂| ≤ A₁ * M₁ + M₂ * A₂ := by
  have hA₁ : 0 ≤ A₁ := le_trans (abs_nonneg _) hf
  have hM₂ : 0 ≤ M₂ := le_trans (abs_nonneg _) hf₂
  have heq : f₁ * g₁ - f₂ * g₂ = (f₁ - f₂) * g₁ + f₂ * (g₁ - g₂) := by ring
  rw [heq]
  have h1 : |(f₁ - f₂) * g₁| ≤ A₁ * M₁ := by
    rw [abs_mul]; exact mul_le_mul hf hg₁ (abs_nonneg _) hA₁
  have h2 : |f₂ * (g₁ - g₂)| ≤ M₂ * A₂ := by
    rw [abs_mul]; exact mul_le_mul hf₂ hg (abs_nonneg _) hM₂
  have := abs_add_le ((f₁ - f₂) * g₁) (f₂ * (g₁ - g₂))
  linarith [this, h1, h2]

/-- Difference of squares: `|f₁² - f₂²| ≤ A(2M)` when `|f₁|,|f₂| ≤ M` and `|f₁-f₂| ≤ A`. -/
theorem abs_sq_sub_sq_le {f₁ f₂ M A : ℝ} (h₁ : |f₁| ≤ M) (h₂ : |f₂| ≤ M) (hf : |f₁ - f₂| ≤ A) :
    |f₁^2 - f₂^2| ≤ A * (2*M) := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hf
  have hM : 0 ≤ M := le_trans (abs_nonneg _) h₁
  have heq : f₁^2 - f₂^2 = (f₁ - f₂) * (f₁ + f₂) := by ring
  rw [heq, abs_mul]
  have hsum : |f₁ + f₂| ≤ 2*M := by
    calc |f₁ + f₂| ≤ |f₁| + |f₂| := abs_add_le _ _
      _ ≤ M + M := by linarith
      _ = 2*M := by ring
  calc |f₁ - f₂| * |f₁ + f₂| ≤ A * (2*M) := mul_le_mul hf hsum (abs_nonneg _) (by linarith)
    _ = A * (2*M) := rfl

end Helpers

/-- `|a-b| ≤ A`, `|c-d| ≤ B`, `A+B ≤ C` give `|(a-c)-(b-d)| ≤ C`. -/
theorem abs_sub_sub_le {a b c d A B Cc : ℝ} (h1 : |a - b| ≤ A) (h2 : |c - d| ≤ B)
    (h3 : A + B ≤ Cc) : |(a - c) - (b - d)| ≤ Cc := by
  have hsplit : (a - c) - (b - d) = (a - b) + (-(c - d)) := by ring
  rw [hsplit]
  have h4 := abs_add_le (a - b) (-(c - d))
  rw [abs_neg] at h4
  linarith [h4, h1, h2, h3]

/-- `A + B ≤ C` gives `A*X + B*X ≤ C*X` for `X ≥ 0`. -/
theorem coef_mul_le {A B C X : ℝ} (h : A + B ≤ C) (hX : 0 ≤ X) : A * X + B * X ≤ C * X := by
  rw [← add_mul]; exact mul_le_mul_of_nonneg_right h hX

/-- `y₁²F₁ - y₂²F₂` estimate used in the `y`-Lipschitz clause. -/
theorem abs_sq_mul_sub {F₁ F₂ y₁ y₂ h C : ℝ} (hF : |F₁ - F₂| ≤ C * |y₁ - y₂|)
    (hF2 : |F₂| ≤ 8) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hy₁h : y₁ ≤ h) (hC0 : 0 ≤ C)
    (hC8 : h * C + 8 ≤ C) :
    |y₁^2 * F₁ - y₂^2 * F₂| ≤ C * (y₁ + y₂) * |y₁ - y₂| := by
  have heq : y₁^2 * F₁ - y₂^2 * F₂ = y₁^2 * (F₁ - F₂) + (y₁^2 - y₂^2) * F₂ := by ring
  rw [heq]
  have hb1 : |y₁^2 * (F₁ - F₂)| ≤ y₁^2 * (C * |y₁ - y₂|) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y₁)]
    exact mul_le_mul_of_nonneg_left hF (sq_nonneg y₁)
  have hb2 : |(y₁^2 - y₂^2) * F₂| ≤ (y₁ + y₂) * |y₁ - y₂| * 8 := by
    have hy : (0:ℝ) ≤ y₁ + y₂ := by linarith
    rw [show y₁^2 - y₂^2 = (y₁ - y₂) * (y₁ + y₂) by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg hy]
    calc |y₁ - y₂| * (y₁ + y₂) * |F₂| ≤ |y₁ - y₂| * (y₁ + y₂) * 8 :=
          mul_le_mul_of_nonneg_left hF2 (by positivity)
      _ = (y₁ + y₂) * |y₁ - y₂| * 8 := by ring
  have hsum := abs_add_le (y₁^2 * (F₁ - F₂)) ((y₁^2 - y₂^2) * F₂)
  have hy1' : y₁^2 ≤ h * (y₁ + y₂) := by nlinarith [hy₁, hy₂, hy₁h]
  have h1 : y₁^2 * (C * |y₁ - y₂|) ≤ (y₁ + y₂) * |y₁ - y₂| * (h * C) := by
    have hxy : (0:ℝ) ≤ C * |y₁ - y₂| := mul_nonneg hC0 (abs_nonneg _)
    calc y₁^2 * (C * |y₁ - y₂|) ≤ h * (y₁ + y₂) * (C * |y₁ - y₂|) :=
          mul_le_mul_of_nonneg_right hy1' hxy
      _ = (y₁ + y₂) * |y₁ - y₂| * (h * C) := by ring
  have hnn : (0:ℝ) ≤ (y₁ + y₂) * |y₁ - y₂| := by positivity
  calc |y₁^2 * (F₁ - F₂) + (y₁^2 - y₂^2) * F₂|
      ≤ y₁^2 * (C * |y₁ - y₂|) + (y₁ + y₂) * |y₁ - y₂| * 8 := by linarith [hsum, hb1, hb2]
    _ ≤ C * (y₁ + y₂) * |y₁ - y₂| := by
        calc y₁^2 * (C * |y₁ - y₂|) + (y₁ + y₂) * |y₁ - y₂| * 8
            ≤ (y₁ + y₂) * |y₁ - y₂| * (h * C) + (y₁ + y₂) * |y₁ - y₂| * 8 := by linarith [h1]
          _ = (y₁ + y₂) * |y₁ - y₂| * (h * C + 8) := by ring
          _ ≤ (y₁ + y₂) * |y₁ - y₂| * C := mul_le_mul_of_nonneg_left hC8 hnn
          _ = C * (y₁ + y₂) * |y₁ - y₂| := by ring

/-- `|x| ≤ M` gives `|x²| ≤ M²`. -/
theorem abs_sq_le_of {x M : ℝ} (h : |x| ≤ M) : |x^2| ≤ M^2 := by
  rw [abs_of_nonneg (sq_nonneg x)]
  rcases abs_le.mp h with ⟨h1, h2⟩
  nlinarith

/-- `|E²Q - J| ≤ 8` when `|E| ≤ 1`, `|Q| ≤ 4`, `|J| ≤ 4`. -/
theorem abs_prod_sub_le {E Q J : ℝ} (hE : |E| ≤ 1) (hQ : |Q| ≤ 4) (hJ : |J| ≤ 4) :
    |E^2 * Q - J| ≤ 8 := by
  have h1 : |E^2 * Q| ≤ 4 := by
    rw [abs_mul]
    have h2 : |E^2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg E)]
      rcases abs_le.mp hE with ⟨h1, h2⟩
      nlinarith
    calc |E^2| * |Q| ≤ 1 * 4 := mul_le_mul h2 hQ (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hsplit : E^2 * Q - J = E^2 * Q + (-J) := by ring
  rw [hsplit]
  have h4 := abs_add_le (E^2 * Q) (-J)
  rw [abs_neg] at h4
  linarith [h4, h1, hJ]

/-- `96/w² + 576/w⁴ + 16/w⁴ ≤ C` when `1000/w⁴ ≤ C`, `0 < w < 1`. -/
theorem coefX1 {w C : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hC : 1000/w^4 ≤ C) :
    96/w^2 + 576/w^4 + 16/w^4 ≤ C := by
  have hw2 : w^2 ≤ 1 := by nlinarith [hw0, hw1]
  have hw4 : w^4 ≤ w^2 := by nlinarith [hw2, sq_nonneg w]
  have hw : (96:ℝ)/w^2 ≤ 96/w^4 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < w^2) (by positivity : (0:ℝ) < w^4)]
    linarith
  have h2 : (688:ℝ)/w^4 ≤ 1000/w^4 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  calc 96/w^2 + 576/w^4 + 16/w^4 ≤ 96/w^4 + 576/w^4 + 16/w^4 := by linarith
    _ = 688/w^4 := by ring
    _ ≤ 1000/w^4 := h2
    _ ≤ C := hC

/-- `96/w² + 720/w⁴ + 16/w⁴ ≤ C` when `1000/w⁴ ≤ C`, `0 < w < 1`. -/
theorem coefY1 {w C : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hC : 1000/w^4 ≤ C) :
    96/w^2 + 720/w^4 + 16/w^4 ≤ C := by
  have hw2 : w^2 ≤ 1 := by nlinarith [hw0, hw1]
  have hw4 : w^4 ≤ w^2 := by nlinarith [hw2, sq_nonneg w]
  have hw : (96:ℝ)/w^2 ≤ 96/w^4 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < w^2) (by positivity : (0:ℝ) < w^4)]
    linarith
  have h2 : (832:ℝ)/w^4 ≤ 1000/w^4 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  calc 96/w^2 + 720/w^4 + 16/w^4 ≤ 96/w^4 + 720/w^4 + 16/w^4 := by linarith
    _ = 832/w^4 := by ring
    _ ≤ 1000/w^4 := h2
    _ ≤ C := hC

/-- `4/w²*3 + 3*(4/w²*(2+2)) ≤ C` when `1000/w⁴ ≤ C`, `0 < w < 1`. -/
theorem coefX2 {w C : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hC : 1000/w^4 ≤ C) :
    4/w^2 * 3 + 3 * (4/w^2 * (2 + 2)) ≤ C := by
  have h1 : (60:ℝ)/w^2 ≤ 1000/w^4 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < w^2) (by positivity : (0:ℝ) < w^4)]
    have hw2 : w^2 ≤ 1 := by nlinarith [hw0, hw1]
    nlinarith [hw2, sq_nonneg w]
  have h2 : (4/w^2 * 3 + 3 * (4/w^2 * (2 + 2))) = 60/w^2 := by ring
  linarith [h1, hC]

/-- `4/w²*3 + 3*(4/w²*(1+4)) ≤ C` when `1000/w⁴ ≤ C`, `0 < w < 1`. -/
theorem coefY2 {w C : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hC : 1000/w^4 ≤ C) :
    4/w^2 * 3 + 3 * (4/w^2 * (1 + 4)) ≤ C := by
  have h1 : (72:ℝ)/w^2 ≤ 1000/w^4 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < w^2) (by positivity : (0:ℝ) < w^4)]
    have hw2 : w^2 ≤ 1 := by nlinarith [hw0, hw1]
    nlinarith [hw2, sq_nonneg w]
  have h2 : (4/w^2 * 3 + 3 * (4/w^2 * (1 + 4))) = 72/w^2 := by ring
  linarith [h1, hC]


/-- Quantitative estimates for the two-step equichordal half-map `T = eqU ∘ eqU` near its fixed
point `A₁ = -1/2`, in the coordinates `ζ = P - A₁ = x + i y` of `Submission/Work/EQ/hetero_local`.

`locR a x y = ‖(x + i y) - w‖` with `w = (1+a)/2`, `locLy a x y = (1 - locR)/locR` is the
`y`-multiplier of one step of `eqU` (`locY = y * locLy`, hence `locLy > 0` keeps the point in the
upper half plane), and the two-step map is written
`locT a (x,y) = (x + locA a (x,y), y * locM a (x,y))`.

Geometrically, near `A₁`: one step of `eqU` is `(x,y) ↦ (-x + O(y²), λy + O(y³))` with
`λ = (1-a)/(1+a) = (1-w)/w`, so the two-step map `T` has eigenvalues `1` (horizontal) and
`λ²` (vertical): it contracts the `y`-coordinate with rate `λ² < 1` and changes the `x`-coordinate
only by `O(y²)`.  The estimates below are the crude quantitative form of this, on a box small
enough that `locLy ≤ κ < 1` there.  (The image of `|x| ≤ 3ρ` under one step still has
`|x| ≤ 3ρ + C h² ≤ 4ρ`, which is why the first clause is asked on the slightly larger box.) -/

theorem loc_estimates {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ ρ h κ C : ℝ, 0 < ρ ∧ 0 < h ∧ 0 < κ ∧ κ < 1 ∧ 0 < C ∧
      C * h ^ 2 ≤ 1 / 2 ∧ C * h ^ 2 / (1 - κ ^ 2) ≤ ρ ∧
      (∀ x y : ℝ, |x| ≤ 4 * ρ → 0 < y → y ≤ h →
        0 < locR a x y ∧ 0 < locLy a x y ∧ locLy a x y ≤ κ ∧
        locY a x y = y * locLy a x y) ∧
      (∀ x y : ℝ, |x| ≤ 3 * ρ → 0 < y → y ≤ h →
        (locT a (x, y)).1 = x + locA a (x, y) ∧ (locT a (x, y)).2 = y * locM a (x, y) ∧
        |locA a (x, y)| ≤ C * y ^ 2 ∧ 0 < locM a (x, y) ∧ locM a (x, y) ≤ κ) ∧
      (∀ x₁ x₂ y : ℝ, |x₁| ≤ 3 * ρ → |x₂| ≤ 3 * ρ → 0 < y → y ≤ h →
        |locA a (x₁, y) - locA a (x₂, y)| ≤ C * y ^ 2 * |x₁ - x₂| ∧
        |locM a (x₁, y) - locM a (x₂, y)| ≤ C * |x₁ - x₂|) ∧
      (∀ x y₁ y₂ : ℝ, |x| ≤ 3 * ρ → 0 < y₁ → y₁ ≤ h → 0 < y₂ → y₂ ≤ h →
        |locA a (x, y₁) - locA a (x, y₂)| ≤ C * (y₁ + y₂) * |y₁ - y₂| ∧
        |locM a (x, y₁) - locM a (x, y₂)| ≤ C * |y₁ - y₂|) := by
  ------------------------------------------------------------------ basic facts
  set w : ℝ := locW a with hwdef
  have hwval : w = (1 + a)/2 := by rw [hwdef, locW]
  have hw0 : (1:ℝ)/2 ≤ w := by rw [hwval]; linarith
  have hwlt : w < 1 := by rw [hwval]; linarith
  have hwpos : 0 < w := by linarith
  have hwnz : w ≠ 0 := ne_of_gt hwpos
  set κ : ℝ := (1 + (1 - w)/w)/2 with hκdef
  have hlam : (1 - w)/w = (1 - a)/(1 + a) := by rw [hwval]; field_simp; ring
  have hlam_pos : 0 < (1 - w)/w := by rw [hlam]; positivity
  have htw : (1 - w)/w < 1 := by rw [div_lt_one hwpos]; linarith
  have hκgt : (1 - w)/w < κ := by rw [hκdef]; linarith
  have hκpos : 0 < κ := by rw [hκdef]; linarith
  have hκlt : κ < 1 := by
    rw [hκdef]
    have : (1 - w)/w < 1 := by rw [div_lt_one hwpos]; linarith
    linarith
  have h1mκ2 : 0 < 1 - κ^2 := by nlinarith
  ------------------------------------------------------------------ the constants
  set C : ℝ := (10:ℝ)^4/w^4 + (10:ℝ)^4 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCbig : (10:ℝ)^4/w^4 ≤ C := by rw [hCdef]; linarith
  set η : ℝ := w - 1/(1 + κ) with hηdef
  have hηpos : 0 < η := by
    have h1 : 1 < w * (1 + κ) := by
      have h2 : w * ((1 - w)/w) < w * κ := mul_lt_mul_of_pos_left hκgt hwpos
      have h3 : w * ((1 - w)/w) = 1 - w := by field_simp
      linarith
    rw [hηdef, sub_pos, div_lt_iff₀ (by linarith : (0:ℝ) < 1 + κ)]
    linarith
  set ρ₀ : ℝ := min ((1 - w)/16) (η/4) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀def]; apply lt_min <;> linarith
  set h : ℝ := min 1 (min (w^2/100) (min (Real.sqrt ((1 - w)*(5*w + 3)/16))
      (min (Real.sqrt (ρ₀*(1 - κ^2)/C)) (Real.sqrt (1/(2*C)))))) with hhdef
  set ρ : ℝ := C * h^2/(1 - κ^2) with hρdef
  have hhpos : 0 < h := by
    rw [hhdef]
    apply lt_min; · norm_num
    apply lt_min
    · positivity
    apply lt_min
    · apply Real.sqrt_pos.mpr; nlinarith
    apply lt_min
    · apply Real.sqrt_pos.mpr; exact div_pos (mul_pos hρ₀pos h1mκ2) hCpos
    · apply Real.sqrt_pos.mpr; positivity
  have hh1 : h ≤ 1 := by
    rw [hhdef]; exact min_le_iff.mpr (Or.inl le_rfl)
  have hh_w : h ≤ w^2/100 := by
    rw [hhdef]; exact min_le_iff.mpr (Or.inr (min_le_iff.mpr (Or.inl le_rfl)))
  have hh_sqrt : h ≤ Real.sqrt ((1 - w)*(5*w + 3)/16) := by
    rw [hhdef]
    exact min_le_iff.mpr (Or.inr (min_le_iff.mpr (Or.inr (min_le_iff.mpr (Or.inl le_rfl)))))
  have hh_sqrt2 : h ≤ Real.sqrt (ρ₀*(1 - κ^2)/C) := by
    rw [hhdef]
    exact min_le_iff.mpr (Or.inr (min_le_iff.mpr (Or.inr (min_le_iff.mpr
      (Or.inr (min_le_iff.mpr (Or.inl le_rfl)))))))
  have hh_sqrt3 : h ≤ Real.sqrt (1/(2*C)) := by
    rw [hhdef]
    exact min_le_iff.mpr (Or.inr (min_le_iff.mpr (Or.inr (min_le_iff.mpr
      (Or.inr (min_le_iff.mpr (Or.inr le_rfl)))))))
  have sq_le_of_le_sqrt : ∀ {x B : ℝ}, 0 < x → x ≤ Real.sqrt B → x^2 ≤ B := by
    intro x B hx h
    have hB : 0 ≤ B := le_of_lt (Real.sqrt_pos.mp (lt_of_lt_of_le hx h))
    calc x^2 ≤ (Real.sqrt B)^2 := pow_le_pow_left₀ (le_of_lt hx) h 2
      _ = B := Real.sq_sqrt hB
  have hh_s : h^2 ≤ (1 - w)*(5*w + 3)/16 := sq_le_of_le_sqrt hhpos hh_sqrt
  have hh_s2 : h^2 ≤ ρ₀*(1 - κ^2)/C := sq_le_of_le_sqrt hhpos hh_sqrt2
  have hh_c : C * h^2 ≤ 1/2 := by
    have h2 : h^2 ≤ 1/(2*C) := sq_le_of_le_sqrt hhpos hh_sqrt3
    calc C * h^2 ≤ C * (1/(2*C)) := mul_le_mul_of_nonneg_left h2 (le_of_lt hCpos)
      _ = 1/2 := by field_simp
  have hρle₀ : ρ ≤ ρ₀ := by
    rw [hρdef, div_le_iff₀ h1mκ2]
    have h3 : h^2 ≤ ρ₀*(1 - κ^2)/C := hh_s2
    rw [le_div_iff₀ hCpos] at h3
    linarith [h3]
  have hρ1 : 4*ρ ≤ (1 - w)/4 := by
    have h1 : ρ ≤ (1 - w)/16 := by
      refine le_trans hρle₀ ?_
      rw [hρ₀def]
      exact min_le_iff.mpr (Or.inl le_rfl)
    linarith
  have hρ2 : 4*ρ ≤ η := by
    have h1 : ρ ≤ η/4 := by
      refine le_trans hρle₀ ?_
      rw [hρ₀def]
      exact min_le_iff.mpr (Or.inr le_rfl)
    linarith
  have hρ7 : 2*h^2/w^2 ≤ ρ := by
    have h2 : 2*(1 - κ^2) ≤ C*w^2 := by
      have h1 : 2 ≤ C*w^2 := by
        have hcw : (10:ℝ)^4/w^4 * w^2 ≤ C * w^2 :=
          mul_le_mul_of_nonneg_right hCbig (sq_nonneg w)
        have hsimp : (10:ℝ)^4/w^4 * w^2 = (10:ℝ)^4/w^2 := by field_simp
        have h3 : (2:ℝ) ≤ (10:ℝ)^4/w^2 := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < w^2)]
          nlinarith [hwpos, hwlt]
        linarith
      nlinarith [h1, h1mκ2]
    rw [hρdef, div_le_div_iff₀ (by positivity : (0:ℝ) < w^2) h1mκ2]
    nlinarith [h2, hhpos]
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact div_pos (mul_pos hCpos (pow_pos hhpos 2)) h1mκ2
  have hρ2' : C * h^2/(1 - κ^2) ≤ ρ := le_of_eq hρdef.symm
  have hC40 : 40 ≤ C := by
    have h1 : (40:ℝ) ≤ (10:ℝ)^4/w^4 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < w^4)]
      nlinarith [hwpos, hwlt]
    linarith [hCbig]
  have hC1000 : 1000/w^4 ≤ C := by
    have h1 : (1000:ℝ)/w^4 ≤ (10:ℝ)^4/w^4 :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith [hCbig]
  ------------------------------------------------------------------ boxes
  have hMBox : ∀ x y : ℝ, |x| ≤ 4*ρ → 0 ≤ y → y ≤ h → LocEst.MBox w h x y :=
    fun x y hx hy0 hyh => ⟨hw0, hwlt, le_trans hx hρ1, hy0, hyh, hh_w, hh_s⟩
  have hxw_of : ∀ {x : ℝ}, |x| ≤ 4*ρ → x ≤ w := by
    intro x hx
    have h1 : x ≤ 4*ρ := le_trans (le_abs_self x) hx
    linarith [hρ1, hwpos]
  ------------------------------------------------------------------ clause 1 (box)
  have hbox1 : ∀ x y : ℝ, |x| ≤ 4*ρ → 0 < y → y ≤ h →
      0 < locR a x y ∧ 0 < locLy a x y ∧ locLy a x y ≤ κ ∧ locY a x y = y * locLy a x y := by
    intro x y hx hy0 hyh
    have hM := hMBox x y hx (le_of_lt hy0) hyh
    have hxw : x ≤ w := hxw_of hx
    have hRpos : 0 < locR a x y := by
      rw [locR_eq_model]
      exact lt_of_lt_of_le (by linarith : (0:ℝ) < 3*w/4) (LocEst.mR_bounds hM).1
    have hEpos : 0 < locLy a x y := by
      rw [locLy_eq_model]; exact (LocEst.mE_bounds hM).1
    have hRge : w - x ≤ locR a x y := by
      rw [locR_eq_model, LocEst.mR, ← hwdef]
      have h1 : Real.sqrt ((x - w)^2) ≤ Real.sqrt ((x - w)^2 + y^2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
      rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith)] at h1
      linarith [h1]
    have hq : 1/(1 + κ) ≤ locR a x y := by
      have hx4 : x ≤ 4*ρ := le_trans (le_abs_self x) hx
      linarith [hRge, hρ2, hηdef]
    have hEκ : locLy a x y ≤ κ := by
      have hmRpos : 0 < LocEst.mR w x y := by rw [← locR_eq_model]; exact hRpos
      have hq' : 1/(1 + κ) ≤ LocEst.mR w x y := by rw [← locR_eq_model]; exact hq
      rw [locLy_eq_model, LocEst.mE, div_le_iff₀ hmRpos]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + κ)] at hq'
      linarith [hq']
    exact ⟨hRpos, hEpos, hEκ, locY_eq_mul a x y (ne_of_gt hRpos)⟩
  ------------------------------------------------------------------ point data
  have point_data : ∀ x y : ℝ, |x| ≤ 3*ρ → 0 < y → y ≤ h →
      (locA a (x, y) = y^2 * ((LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y)
          (LocEst.mY w x y) - LocEst.mIA w x y)) ∧
      (locM a (x, y) = LocEst.mE w x y * LocEst.mE w (LocEst.mX w x y) (LocEst.mY w x y)) ∧
      LocEst.MBox w h x y ∧ LocEst.MBox w h (LocEst.mX w x y) (LocEst.mY w x y) ∧
      |LocEst.mX w x y| ≤ 4*ρ ∧ 0 < LocEst.mY w x y ∧ LocEst.mY w x y ≤ h ∧
      0 < LocEst.mE w x y ∧ LocEst.mE w x y ≤ κ ∧
      0 < LocEst.mE w (LocEst.mX w x y) (LocEst.mY w x y) ∧
      LocEst.mE w (LocEst.mX w x y) (LocEst.mY w x y) ≤ κ := by
    intro x y hx hy0 hyh
    have hx4 : |x| ≤ 4*ρ := by linarith [hx, hρpos]
    obtain ⟨hRpos, hEpos, hEκ, -⟩ := hbox1 x y hx4 hy0 hyh
    have hxw : x ≤ w := hxw_of hx4
    have hM := hMBox x y hx4 (le_of_lt hy0) hyh
    have hXb : |LocEst.mX w x y| ≤ |x| + 2*h^2/w^2 := LocEst.mX_bound hM
    have hX4 : |LocEst.mX w x y| ≤ 4*ρ := by linarith [hXb, hx, hρ7]
    have hXw : LocEst.mX w x y ≤ w := by
      have h1 : LocEst.mX w x y ≤ 4*ρ := le_trans (le_abs_self _) hX4
      linarith [hρ1, hwpos]
    have hYpos : 0 < LocEst.mY w x y := by
      rw [LocEst.mY]; exact mul_pos hy0 (LocEst.mE_bounds hM).1
    have hYle : LocEst.mY w x y ≤ h := by
      rw [LocEst.mY]
      calc y * LocEst.mE w x y ≤ y * κ := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hy0)
            rw [← locLy_eq_model]; exact hEκ
        _ ≤ h * κ := mul_le_mul_of_nonneg_right hyh (le_of_lt hκpos)
        _ ≤ h * 1 := mul_le_mul_of_nonneg_left (le_of_lt hκlt) (le_of_lt hhpos)
        _ = h := mul_one h
    have hM' : LocEst.MBox w h (LocEst.mX w x y) (LocEst.mY w x y) :=
      ⟨hw0, hwlt, le_trans hX4 hρ1, le_of_lt hYpos, hYle, hh_w, hh_s⟩
    have hmA' : 0 < LocEst.mA w (LocEst.mX w x y) (LocEst.mY w x y) := by
      have := (LocEst.mA_bounds hM').1
      nlinarith [hwpos]
    have hAid := locA_eq_model a x y hxw hXw hRpos hmA'
    have hMid := locM_eq_model a x y hxw hRpos
    have hEκ' : LocEst.mE w (LocEst.mX w x y) (LocEst.mY w x y) ≤ κ := by
      have := (hbox1 _ _ hX4 hYpos hYle).2.2.1
      rw [locLy_eq_model] at this
      exact this
    refine ⟨hAid, hMid, hM, hM', hX4, hYpos, hYle, (LocEst.mE_bounds hM).1, ?_, ?_, hEκ'⟩
    · rw [← locLy_eq_model]; exact hEκ
    · exact (LocEst.mE_bounds hM').1
  ------------------------------------------------------------------ clause 2 (step)
  have hstep : ∀ x y : ℝ, |x| ≤ 3*ρ → 0 < y → y ≤ h →
      (locT a (x, y)).1 = x + locA a (x, y) ∧ (locT a (x, y)).2 = y * locM a (x, y) ∧
      |locA a (x, y)| ≤ C * y^2 ∧ 0 < locM a (x, y) ∧ locM a (x, y) ≤ κ := by
    intro x y hx hy0 hyh
    obtain ⟨hAid, hMid, hM, hM', hX4, hYpos, hYle, hEpos, hEκ, hEpos', hEκ'⟩ :=
      point_data x y hx hy0 hyh
    have hx4 : |x| ≤ 4*ρ := by linarith [hx, hρpos]
    have hRpos : 0 < locR a x y := (hbox1 x y hx4 hy0 hyh).1
    have hRne : locR a x y ≠ 0 := ne_of_gt hRpos
    have hRne' : locR a (locFn a (x, y)).1 (locFn a (x, y)).2 ≠ 0 := by
      simp only [locFn]
      have hxw : x ≤ w := hxw_of hx4
      have hXid := locX_eq_model a x y hxw hRpos
      have hYid := locY_eq_model a x y (ne_of_gt hRpos)
      rw [hXid, hYid, locR_eq_model]
      exact ne_of_gt (lt_of_lt_of_le (by linarith : (0:ℝ) < 3*w/4) (LocEst.mR_bounds hM').1)
    refine ⟨locT_fst a (x, y), ?_, ?_, ?_, ?_⟩
    · exact locT_snd a (x, y) hRne hRne'
    · rw [hAid, abs_mul, abs_of_nonneg (sq_nonneg y)]
      have hb : |(LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)
          - LocEst.mIA w x y| ≤ 40 := by
        have hE3 : |LocEst.mE w x y| ≤ 3 := by
          rw [abs_of_pos hEpos]; exact (LocEst.mE_bounds hM).2
        have hIA4 : |LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)| ≤ 4 := by
          rw [abs_of_pos (LocEst.mIA_bounds hM').1]; exact (LocEst.mIA_bounds hM').2
        have hIA4' : |LocEst.mIA w x y| ≤ 4 := by
          rw [abs_of_pos (LocEst.mIA_bounds hM).1]; exact (LocEst.mIA_bounds hM).2
        have h2 : |(LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)| ≤ 36 := by
          rw [abs_mul, abs_pow]
          have h36 : (3:ℝ)^2 = 9 := by norm_num
          calc |LocEst.mE w x y| ^ 2 * |LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)|
              ≤ 3^2 * 4 := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hE3 2) hIA4 (abs_nonneg _) (by norm_num)
            _ = 36 := by norm_num
        have hsplit : (LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)
            - LocEst.mIA w x y
            = (LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)
              + -(LocEst.mIA w x y) := by ring
        rw [hsplit]
        have := abs_add_le ((LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y))
          (-(LocEst.mIA w x y))
        rw [abs_neg] at this
        linarith [this, h2, hIA4']
      calc y^2 * |(LocEst.mE w x y)^2 * LocEst.mIA w (LocEst.mX w x y) (LocEst.mY w x y)
            - LocEst.mIA w x y| ≤ y^2 * 40 := mul_le_mul_of_nonneg_left hb (sq_nonneg y)
        _ ≤ C * y^2 := by nlinarith [hC40, sq_nonneg y]
    · rw [hMid]; exact mul_pos hEpos hEpos'
    · rw [hMid]
      nlinarith [hEpos, hEpos', hEκ, hEκ', hκlt, hκpos]
  ------------------------------------------------------------------ clause 3 (Lipschitz in x)
  have hlipX : ∀ x₁ x₂ y : ℝ, |x₁| ≤ 3*ρ → |x₂| ≤ 3*ρ → 0 < y → y ≤ h →
      |locA a (x₁, y) - locA a (x₂, y)| ≤ C * y^2 * |x₁ - x₂| ∧
      |locM a (x₁, y) - locM a (x₂, y)| ≤ C * |x₁ - x₂| := by
    intro x₁ x₂ y hx₁ hx₂ hy0 hyh
    obtain ⟨A₁, M₁, hM₁, hM₁', hX4₁, hYp₁, hYl₁, hEp₁, hEκ₁, hEp₁', hEκ₁'⟩ :=
      point_data x₁ y hx₁ hy0 hyh
    obtain ⟨A₂, M₂, hM₂, hM₂', hX4₂, hYp₂, hYl₂, hEp₂, hEκ₂, hEp₂', hEκ₂'⟩ :=
      point_data x₂ y hx₂ hy0 hyh
    set E₁ := LocEst.mE w x₁ y with hE₁df
    set E₂ := LocEst.mE w x₂ y with hE₂df
    set P₁ := LocEst.mE w (LocEst.mX w x₁ y) (LocEst.mY w x₁ y) with hP₁df
    set P₂ := LocEst.mE w (LocEst.mX w x₂ y) (LocEst.mY w x₂ y) with hP₂df
    set Q₁ := LocEst.mIA w (LocEst.mX w x₁ y) (LocEst.mY w x₁ y) with hQ₁df
    set Q₂ := LocEst.mIA w (LocEst.mX w x₂ y) (LocEst.mY w x₂ y) with hQ₂df
    set J₁ := LocEst.mIA w x₁ y with hJ₁df
    set J₂ := LocEst.mIA w x₂ y with hJ₂df
    have hA₁' : locA a (x₁, y) = y^2 * (E₁^2 * Q₁ - J₁) := A₁
    have hA₂' : locA a (x₂, y) = y^2 * (E₂^2 * Q₂ - J₂) := A₂
    have hMid₁ : locM a (x₁, y) = E₁ * P₁ := M₁
    have hMid₂ : locM a (x₂, y) = E₂ * P₂ := M₂
    have hE3 : |E₁| ≤ 3 := by rw [abs_of_pos hEp₁]; exact (LocEst.mE_bounds hM₁).2
    have hE3' : |E₂| ≤ 3 := by rw [abs_of_pos hEp₂]; exact (LocEst.mE_bounds hM₂).2
    have hP3 : |P₁| ≤ 3 := by rw [abs_of_pos hEp₁']; exact (LocEst.mE_bounds hM₁').2
    have hP3' : |P₂| ≤ 3 := by rw [abs_of_pos hEp₂']; exact (LocEst.mE_bounds hM₂').2
    have hQ4 : |Q₁| ≤ 4 := by
      rw [abs_of_pos (LocEst.mIA_bounds hM₁').1]; exact (LocEst.mIA_bounds hM₁').2
    have hJ4 : |J₁| ≤ 4 := by
      rw [abs_of_pos (LocEst.mIA_bounds hM₁).1]; exact (LocEst.mIA_bounds hM₁).2
    have hE : |E₁ - E₂| ≤ 4/w^2 * |x₁ - x₂| := LocEst.mE_lip_u hM₁ hM₂
    have hP : |P₁ - P₂| ≤ 4/w^2 * (2 + 2) * |x₁ - x₂| := by
      have h1 := LocEst.mE_lip hM₁' hM₂'
      have hX : |LocEst.mX w x₁ y - LocEst.mX w x₂ y| ≤ 2 * |x₁ - x₂| := LocEst.mX_lip_u hM₁ hM₂
      have hY : |LocEst.mY w x₁ y - LocEst.mY w x₂ y| ≤ 2 * |x₁ - x₂| := LocEst.mY_lip_u hM₁ hM₂
      have h3 : (4/w^2 : ℝ) * |LocEst.mX w x₁ y - LocEst.mX w x₂ y| ≤ 4/w^2 * (2 * |x₁ - x₂|) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      have h4 : (4/w^2 : ℝ) * |LocEst.mY w x₁ y - LocEst.mY w x₂ y| ≤ 4/w^2 * (2 * |x₁ - x₂|) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
      have h5 : (4/w^2 : ℝ) * (2 * |x₁ - x₂|) + 4/w^2 * (2 * |x₁ - x₂|)
          = 4/w^2 * (2 + 2) * |x₁ - x₂| := by ring
      linarith [h1, h3, h4, h5]
    have hQ : |Q₁ - Q₂| ≤ 64/w^4 * |x₁ - x₂| := by
      have h1 := LocEst.mIA_lip hM₁' hM₂'
      have hX : |LocEst.mX w x₁ y - LocEst.mX w x₂ y| ≤ 2 * |x₁ - x₂| := LocEst.mX_lip_u hM₁ hM₂
      have hY : |LocEst.mY w x₁ y - LocEst.mY w x₂ y| ≤ 2 * |x₁ - x₂| := LocEst.mY_lip_u hM₁ hM₂
      have h3 : (16/w^4 : ℝ) * |LocEst.mX w x₁ y - LocEst.mX w x₂ y| ≤ 16/w^4 * (2 * |x₁ - x₂|) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      have h4 : (16/w^4 : ℝ) * |LocEst.mY w x₁ y - LocEst.mY w x₂ y| ≤ 16/w^4 * (2 * |x₁ - x₂|) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
      have h5 : (16/w^4 : ℝ) * (2 * |x₁ - x₂|) + 16/w^4 * (2 * |x₁ - x₂|)
          = 64/w^4 * |x₁ - x₂| := by ring
      linarith [h1, h3, h4, h5]
    have hIA : |J₁ - J₂| ≤ 16/w^4 * |x₁ - x₂| := LocEst.mIA_lip_u hM₁ hM₂
    have hE2 : |E₁^2 - E₂^2| ≤ 24/w^2 * |x₁ - x₂| := by
      have h := abs_sq_sub_sq_le (M := 3) hE3 hE3' hE
      have h2 : (4/w^2 * |x₁ - x₂|) * (2*3) = 24/w^2 * |x₁ - x₂| := by ring
      linarith [h, h2]
    have hE2' : |E₂^2| ≤ 9 := by
      rw [abs_of_nonneg (sq_nonneg E₂)]
      have h := abs_sq_le_of hE3'
      norm_num at h
      exact h
    have hE2Q : |E₁^2 * Q₁ - E₂^2 * Q₂| ≤ (96/w^2 + 576/w^4) * |x₁ - x₂| := by
      have h := abs_mul_sub_mul_le (f₁ := E₁^2) (f₂ := E₂^2) (g₁ := Q₁) (g₂ := Q₂)
        (M₁ := 4) (M₂ := 9) (A₁ := 24/w^2 * |x₁ - x₂|) (A₂ := 64/w^4 * |x₁ - x₂|)
        hQ4 hE2' hE2 hQ
      have h96 : (24/w^2 * |x₁ - x₂|) * 4 = 96/w^2 * |x₁ - x₂| := by ring
      have h576 : (9:ℝ) * (64/w^4 * |x₁ - x₂|) = 576/w^4 * |x₁ - x₂| := by ring
      linarith [h, h96, h576]
    have hF : |(E₁^2 * Q₁ - J₁) - (E₂^2 * Q₂ - J₂)| ≤ C * |x₁ - x₂| :=
      abs_sub_sub_le hE2Q hIA
        (coef_mul_le (coefX1 hwpos hwlt hC1000) (abs_nonneg _))
    refine ⟨?_, ?_⟩
    · rw [hA₁', hA₂']
      have heq : y^2 * (E₁^2*Q₁ - J₁) - y^2 * (E₂^2*Q₂ - J₂)
          = y^2 * ((E₁^2*Q₁ - J₁) - (E₂^2*Q₂ - J₂)) := by ring
      rw [heq, abs_mul, abs_of_nonneg (sq_nonneg y)]
      calc y^2 * |(E₁^2*Q₁ - J₁) - (E₂^2*Q₂ - J₂)| ≤ y^2 * (C * |x₁ - x₂|) :=
            mul_le_mul_of_nonneg_left hF (sq_nonneg y)
        _ = C * y^2 * |x₁ - x₂| := by ring
    · rw [hMid₁, hMid₂]
      have hres := abs_mul_sub_mul_le (f₁ := E₁) (f₂ := E₂) (g₁ := P₁) (g₂ := P₂)
        (M₁ := 3) (M₂ := 3) (A₁ := 4/w^2 * |x₁ - x₂|) (A₂ := 4/w^2 * (2+2) * |x₁ - x₂|)
        hP3 hE3' hE hP
      calc |E₁ * P₁ - E₂ * P₂| ≤ 4/w^2 * |x₁ - x₂| * 3 + 3 * (4/w^2 * (2 + 2) * |x₁ - x₂|) := hres
        _ = (4/w^2 * 3 + 3 * (4/w^2 * (2 + 2))) * |x₁ - x₂| := by ring
        _ ≤ C * |x₁ - x₂| :=
            mul_le_mul_of_nonneg_right (coefX2 hwpos hwlt hC1000) (abs_nonneg _)
  ------------------------------------------------------------------ clause 4 (Lipschitz in y)
  have hlipY : ∀ x y₁ y₂ : ℝ, |x| ≤ 3*ρ → 0 < y₁ → y₁ ≤ h → 0 < y₂ → y₂ ≤ h →
      |locA a (x, y₁) - locA a (x, y₂)| ≤ C * (y₁ + y₂) * |y₁ - y₂| ∧
      |locM a (x, y₁) - locM a (x, y₂)| ≤ C * |y₁ - y₂| := by
    intro x y₁ y₂ hx hy₁ hyh₁ hy₂ hyh₂
    obtain ⟨A₁, M₁, hM₁, hM₁', hX4₁, hYp₁, hYl₁, hEp₁, hEκ₁, hEp₁', hEκ₁'⟩ :=
      point_data x y₁ hx hy₁ hyh₁
    obtain ⟨A₂, M₂, hM₂, hM₂', hX4₂, hYp₂, hYl₂, hEp₂, hEκ₂, hEp₂', hEκ₂'⟩ :=
      point_data x y₂ hx hy₂ hyh₂
    set E₁ := LocEst.mE w x y₁ with hE₁df
    set E₂ := LocEst.mE w x y₂ with hE₂df
    set P₁ := LocEst.mE w (LocEst.mX w x y₁) (LocEst.mY w x y₁) with hP₁df
    set P₂ := LocEst.mE w (LocEst.mX w x y₂) (LocEst.mY w x y₂) with hP₂df
    set Q₁ := LocEst.mIA w (LocEst.mX w x y₁) (LocEst.mY w x y₁) with hQ₁df
    set Q₂ := LocEst.mIA w (LocEst.mX w x y₂) (LocEst.mY w x y₂) with hQ₂df
    set J₁ := LocEst.mIA w x y₁ with hJ₁df
    set J₂ := LocEst.mIA w x y₂ with hJ₂df
    have hA₁' : locA a (x, y₁) = y₁^2 * (E₁^2 * Q₁ - J₁) := A₁
    have hA₂' : locA a (x, y₂) = y₂^2 * (E₂^2 * Q₂ - J₂) := A₂
    have hMid₁ : locM a (x, y₁) = E₁ * P₁ := M₁
    have hMid₂ : locM a (x, y₂) = E₂ * P₂ := M₂
    have hE3 : |E₁| ≤ 3 := by rw [abs_of_pos hEp₁]; exact (LocEst.mE_bounds hM₁).2
    have hE3' : |E₂| ≤ 3 := by rw [abs_of_pos hEp₂]; exact (LocEst.mE_bounds hM₂).2
    have hP3 : |P₁| ≤ 3 := by rw [abs_of_pos hEp₁']; exact (LocEst.mE_bounds hM₁').2
    have hP3' : |P₂| ≤ 3 := by rw [abs_of_pos hEp₂']; exact (LocEst.mE_bounds hM₂').2
    have hQ4 : |Q₁| ≤ 4 := by
      rw [abs_of_pos (LocEst.mIA_bounds hM₁').1]; exact (LocEst.mIA_bounds hM₁').2
    have hQ4' : |Q₂| ≤ 4 := by
      rw [abs_of_pos (LocEst.mIA_bounds hM₂').1]; exact (LocEst.mIA_bounds hM₂').2
    have hJ4' : |J₂| ≤ 4 := by
      rw [abs_of_pos (LocEst.mIA_bounds hM₂).1]; exact (LocEst.mIA_bounds hM₂).2
    have hE : |E₁ - E₂| ≤ 4/w^2 * |y₁ - y₂| := LocEst.mE_lip_v hM₁ hM₂
    have hX : |LocEst.mX w x y₁ - LocEst.mX w x y₂| ≤ 1 * |y₁ - y₂| := by
      simpa using LocEst.mX_lip_v hM₁ hM₂
    have hY : |LocEst.mY w x y₁ - LocEst.mY w x y₂| ≤ 4 * |y₁ - y₂| := LocEst.mY_lip_v hM₁ hM₂
    have hP : |P₁ - P₂| ≤ 4/w^2 * (1 + 4) * |y₁ - y₂| := by
      have h1 := LocEst.mE_lip hM₁' hM₂'
      have h3 : (4/w^2 : ℝ) * |LocEst.mX w x y₁ - LocEst.mX w x y₂| ≤ 4/w^2 * (1 * |y₁ - y₂|) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      have h4 : (4/w^2 : ℝ) * |LocEst.mY w x y₁ - LocEst.mY w x y₂| ≤ 4/w^2 * (4 * |y₁ - y₂|) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
      have h5 : (4/w^2 : ℝ) * (1 * |y₁ - y₂|) + 4/w^2 * (4 * |y₁ - y₂|)
          = 4/w^2 * (1 + 4) * |y₁ - y₂| := by ring
      linarith [h1, h3, h4, h5]
    have hQ : |Q₁ - Q₂| ≤ 80/w^4 * |y₁ - y₂| := by
      have h1 := LocEst.mIA_lip hM₁' hM₂'
      have h3 : (16/w^4 : ℝ) * |LocEst.mX w x y₁ - LocEst.mX w x y₂| ≤ 16/w^4 * (1 * |y₁ - y₂|) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      have h4 : (16/w^4 : ℝ) * |LocEst.mY w x y₁ - LocEst.mY w x y₂| ≤ 16/w^4 * (4 * |y₁ - y₂|) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
      have h5 : (16/w^4 : ℝ) * (1 * |y₁ - y₂|) + 16/w^4 * (4 * |y₁ - y₂|)
          = 80/w^4 * |y₁ - y₂| := by ring
      linarith [h1, h3, h4, h5]
    have hIA : |J₁ - J₂| ≤ 16/w^4 * |y₁ - y₂| := LocEst.mIA_lip_v hM₁ hM₂
    have hE2 : |E₁^2 - E₂^2| ≤ 24/w^2 * |y₁ - y₂| := by
      have h := abs_sq_sub_sq_le (M := 3) hE3 hE3' hE
      have h2 : (4/w^2 * |y₁ - y₂|) * (2*3) = 24/w^2 * |y₁ - y₂| := by ring
      linarith [h, h2]
    have hE2' : |E₂^2| ≤ 9 := by
      rw [abs_of_nonneg (sq_nonneg E₂)]
      have h := abs_sq_le_of hE3'
      norm_num at h
      exact h
    have hE2Q : |E₁^2 * Q₁ - E₂^2 * Q₂| ≤ (96/w^2 + 720/w^4) * |y₁ - y₂| := by
      have h := abs_mul_sub_mul_le (f₁ := E₁^2) (f₂ := E₂^2) (g₁ := Q₁) (g₂ := Q₂)
        (M₁ := 4) (M₂ := 9) (A₁ := 24/w^2 * |y₁ - y₂|) (A₂ := 80/w^4 * |y₁ - y₂|)
        hQ4 hE2' hE2 hQ
      have h96 : (24/w^2 * |y₁ - y₂|) * 4 = 96/w^2 * |y₁ - y₂| := by ring
      have h720 : (9:ℝ) * (80/w^4 * |y₁ - y₂|) = 720/w^4 * |y₁ - y₂| := by ring
      linarith [h, h96, h720]
    have hF : |(E₁^2 * Q₁ - J₁) - (E₂^2 * Q₂ - J₂)| ≤ C * |y₁ - y₂| :=
      abs_sub_sub_le hE2Q hIA
        (coef_mul_le (coefY1 hwpos hwlt hC1000) (abs_nonneg _))
    have hF2 : |E₂^2 * Q₂ - J₂| ≤ 8 := by
      have hE1'' : |E₂| ≤ 1 := by
        rw [abs_of_pos hEp₂]; nlinarith [hEκ₂, hκlt, hκpos]
      exact abs_prod_sub_le hE1'' hQ4' hJ4'
    have hC8 : h * C + 8 ≤ C := by
      have hCge : (10:ℝ)^4 ≤ C := by
        rw [hCdef]
        have h1 : (0:ℝ) ≤ (10:ℝ)^4/w^4 := by positivity
        linarith
      have hw2le : w^2 ≤ 1 := by nlinarith [hwpos, hwlt]
      have hh100 : h ≤ 1/100 := by nlinarith [hh_w, hw2le]
      nlinarith [hCge, hh100, hh1]
    refine ⟨?_, ?_⟩
    · rw [hA₁', hA₂']
      exact abs_sq_mul_sub hF hF2 hy₁ hy₂ hyh₁ (le_of_lt hCpos) hC8
    · rw [hMid₁, hMid₂]
      have hres := abs_mul_sub_mul_le (f₁ := E₁) (f₂ := E₂) (g₁ := P₁) (g₂ := P₂)
        (M₁ := 3) (M₂ := 3) (A₁ := 4/w^2 * |y₁ - y₂|) (A₂ := 4/w^2 * (1+4) * |y₁ - y₂|)
        hP3 hE3' hE hP
      calc |E₁ * P₁ - E₂ * P₂| ≤ 4/w^2 * |y₁ - y₂| * 3 + 3 * (4/w^2 * (1 + 4) * |y₁ - y₂|) := hres
        _ = (4/w^2 * 3 + 3 * (4/w^2 * (1 + 4))) * |y₁ - y₂| := by ring
        _ ≤ C * |y₁ - y₂| :=
            mul_le_mul_of_nonneg_right (coefY2 hwpos hwlt hC1000) (abs_nonneg _)

  exact ⟨ρ, h, κ, C, hρpos, hhpos, hκpos, hκlt, hCpos, hh_c, hρ2', hbox1, hstep, hlipX, hlipY⟩

end Work.EQ
