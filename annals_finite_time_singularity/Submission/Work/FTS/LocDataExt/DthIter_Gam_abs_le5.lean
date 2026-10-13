import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `|D_θ^i Γ| ≤ 100000 · Γ` on `Iθ`, for `i ≤ 5`

This extends `Work.FTS.LocData.DthIter_Gam_abs_le` (the case `i ≤ 4`) by one order.

The `i ≤ 4` file reduces the statement, through
`Spaces.dthU_iter_Gam_abs_bound`, to the coefficient bound `|Tfun j α θ| ≤ 100000`
for `j ≤ 3`.  Recall `Tfun j α θ = (Qp j α).eval (cos 2θ)`, where the coefficient
polynomials satisfy

`Qp 0 α = X - 1/3`,   `Qp (j+1) α = -2(1-X²)·(Qp j α)' + α·(X-1/3)·(Qp j α)`.

Hence for `i ≤ 5` it remains to bound `Tfun 4 α`, i.e. `Qp 4 α` on `[-1,1]`.  Since

`(Qp 4 α).eval v = -2(1-v²)·(Qp 3 α)'.eval v + α(v-1/3)·(Qp 3 α).eval v`

and `|(Qp 3 α).eval v| ≤ 10300/81` is already known, we need a bound on the derivative
`(Qp 3 α)'.eval v`.  Differentiating the recursion gives

`Qp (j+1)' = 4v·Qp j' - 2(1-v²)·Qp j'' + α·Qp j + α(v-1/3)·Qp j'`,

so `(Qp 3 α)'.eval v` is controlled by `(Qp 2 α)`, `(Qp 2 α)'` (both already bounded) and
the second derivative `(Qp 2 α)''`.  The latter is computed explicitly and bounded by `96`.
Carrying the numbers through gives

`|(Qp 3 α)'.eval v| ≤ 13072/27`  and  `|(Qp 4 α).eval v| ≤ 276496/243 ≤ 100000`,

which is all that is needed.
-/

namespace Work.FTS.LocDataExt

open Work.FTS.LocData

set_option autoImplicit false

/-! ## Derivative recursions for the coefficient polynomials -/

/-- The derivative recursion for the coefficient polynomials, obtained by
differentiating `Q_{j+1} = -2(1-X²)Q_j' + α(X-1/3)Q_j`. -/
theorem Qp_deriv_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.eval v
      = 4 * v * (Qp j α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp j α).derivative.derivative.eval v
        + α * (Qp j α).eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.eval v := by
  simp [Qp]; ring

/-- Explicit second derivative of `Qp 2`, evaluated. -/
theorem Qp2_deriv2_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.eval v
      = 4 * (4 * v + 2 * α * (v - 1 / 3)) + 8 * v * (4 + 2 * α)
        + 2 * α * (4 * v + 2 * α * (v - 1 / 3)) + α * (v - 1 / 3) * (4 + 2 * α) := by
  simp [Qp]; ring

/-- **Bound on `(Qp 2 α)''`.** -/
theorem Qp2_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 2 α).derivative.derivative.eval v| ≤ 96 := by
  rw [Qp2_deriv2_eval]
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hR : |4 * v + 2 * α * (v - 1 / 3)| ≤ 20 / 3 := by
    rw [← Qp1_deriv_eval]; exact Qp1_deriv_bound hα0 hα1 hv
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hA : |4 * (4 * v + 2 * α * (v - 1 / 3))| ≤ 4 * (20 / 3) :=
    abs_mul_le_of (A := 4) (B := 20 / 3) (by norm_num) hR (by norm_num)
  have hB : |8 * v * (4 + 2 * α)| ≤ 8 * 1 * 6 := by
    rw [show 8 * v * (4 + 2 * α) = (8 * v) * (4 + 2 * α) by ring]
    exact abs_mul_le_of (A := 8 * 1) (B := 6)
      (by rw [abs_mul]; norm_num; exact hv) h4 (by norm_num)
  have hC : |2 * α * (4 * v + 2 * α * (v - 1 / 3))| ≤ 2 * 1 * (20 / 3) := by
    rw [show 2 * α * (4 * v + 2 * α * (v - 1 / 3))
        = (2 * α) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 20 / 3)
      (by simpa using abs_two_mul_le_two hα0 hα1) hR (by norm_num)
  have hD : |α * (v - 1 / 3) * (4 + 2 * α)| ≤ 1 * (4 / 3) * 6 := by
    rw [show α * (v - 1 / 3) * (4 + 2 * α) = (α * (v - 1 / 3)) * (4 + 2 * α) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 6)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      h4 (by norm_num)
  have hsp1 := abs_add_le (4 * (4 * v + 2 * α * (v - 1 / 3)) + 8 * v * (4 + 2 * α)
      + 2 * α * (4 * v + 2 * α * (v - 1 / 3))) (α * (v - 1 / 3) * (4 + 2 * α))
  have hsp2 := abs_add_le (4 * (4 * v + 2 * α * (v - 1 / 3)) + 8 * v * (4 + 2 * α))
      (2 * α * (4 * v + 2 * α * (v - 1 / 3)))
  have hsp3 := abs_add_le (4 * (4 * v + 2 * α * (v - 1 / 3))) (8 * v * (4 + 2 * α))
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-- The derivative recursion at `j = 2`, i.e. for `Qp 3`. -/
theorem Qp3_deriv_eval (α v : ℝ) :
    (Qp 3 α).derivative.eval v
      = 4 * v * (Qp 2 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v
        + α * (Qp 2 α).eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.eval v :=
  Qp_deriv_succ_eval 2 α v

/-- **Bound on `(Qp 3 α)'`.** -/
theorem Qp3_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 := by
  rw [Qp3_deriv_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS2 : |(Qp 2 α).derivative.eval v| ≤ 154 / 3 := Qp2_deriv_bound hα0 hα1 hv
  have hU2 : |(Qp 2 α).derivative.derivative.eval v| ≤ 96 := Qp2_deriv2_bound hα0 hα1 hv
  have hQ2 : |(Qp 2 α).eval v| ≤ 496 / 27 := Qp2_eval_bound hα0 hα1 hv
  have hA : |4 * v * (Qp 2 α).derivative.eval v| ≤ 4 * 1 * (154 / 3) := by
    rw [show 4 * v * (Qp 2 α).derivative.eval v
        = (4 * v) * (Qp 2 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 * 1) (B := 154 / 3)
      (by rw [abs_mul]; norm_num; exact hv) hS2 (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v| ≤ 2 * 1 * 96 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 96)
      (by rw [abs_mul]; norm_num; exact h1) hU2 (by norm_num)
  have hC : |α * (Qp 2 α).eval v| ≤ 1 * (496 / 27) :=
    abs_mul_le_of (A := 1) (B := 496 / 27) (by rwa [abs_of_nonneg hα0]) hQ2 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 2 α).derivative.eval v| ≤ 1 * (4 / 3) * (154 / 3) := by
    rw [show α * (v - 1 / 3) * (Qp 2 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 2 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 154 / 3)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hS2 (by norm_num)
  have hsp1 := abs_add_le (4 * v * (Qp 2 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v
      + α * (Qp 2 α).eval v) (α * (v - 1 / 3) * (Qp 2 α).derivative.eval v)
  have hsp2 := abs_add_le (4 * v * (Qp 2 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v)
      (α * (Qp 2 α).eval v)
  have hsp3 := abs_add_le (4 * v * (Qp 2 α).derivative.eval v)
      ((-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.eval v)
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-- The recursion at `j = 3`, i.e. for `Qp 4`. -/
theorem Qp4_eval (α v : ℝ) :
    (Qp 4 α).eval v = (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
      + α * (v - 1 / 3) * (Qp 3 α).eval v := by
  have h := Qp_succ_eval 3 α v
  simpa using h

/-- **Bound on `Qp 4 α` on `[-1,1]`.** -/
theorem Qp4_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).eval v| ≤ 100000 := by
  rw [Qp4_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 := Qp3_deriv_bound hα0 hα1 hv
  have hQ : |(Qp 3 α).eval v| ≤ 10300 / 81 := Qp3_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v| ≤ 2 * 1 * (13072 / 27) := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 13072 / 27)
      (by rw [abs_mul]; norm_num; exact h1) hS (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 3 α).eval v| ≤ 1 * (4 / 3) * (10300 / 81) := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 10300 / 81)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ (by norm_num)
  calc |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 3 α).eval v|
      ≤ |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v|
        + |α * (v - 1 / 3) * (Qp 3 α).eval v| := abs_add_le _ _
    _ ≤ 2 * 1 * (13072 / 27) + 1 * (4 / 3) * (10300 / 81) := add_le_add hA hB
    _ = 276496 / 243 := by norm_num
    _ ≤ 100000 := by norm_num

/-- **The coefficient bound `|Tfun j α θ| ≤ 100000` for `j ≤ 4`**, extending
`Work.FTS.LocData.Tfun_abs_le` by one order. -/
theorem Tfun_abs_le4 (j : ℕ) (hj : j ≤ 4) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 100000 := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact Tfun_abs_le j (by omega) α hα hα1 θ
  · subst heq
    have hq : |(Qp 4 α).eval (Real.cos (2 * θ))| ≤ 100000 :=
      Qp4_eval_bound (le_of_lt hα) hα1
        (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    rw [Tfun_eq_Qp 4 α]
    simpa using hq

/-- The angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` on `Iθ`, extended by one order (to `i ≤ 5`).
The proved `i ≤ 4` version `Work.FTS.LocData.DthIter_Gam_abs_le` reduces the statement to a
bound `|Tfun (i-1) α θ| ≤ 100000`, so it suffices to bound `Qp 4 α` on `|v| ≤ 1`, `α ∈ [0,1]`
through the recursion `Qp (j+1) = -2(1-X²)·Qp j' + α·(X-1/3)·Qp j` and a bound on
`(Qp 3 α).derivative.eval v` obtained from the explicit `Qp3_eval`, and then to re-run the
final assembly of that file (`Work.Spaces.dthU_iter_Gam_abs_bound`). -/
theorem DthIter_Gam_abs_le5 (i : ℕ) (hi : i ≤ 5) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    linarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Tfun_abs_le4 (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 100000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS.LocDataExt
