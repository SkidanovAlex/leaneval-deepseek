/-
# `|D_θ^i Γ| ≤ 100000 · Γ` on `Iθ`, for `i ≤ 4`

With `Γ(θ) = (sin θ · cos²θ)^{α/3}` and `D_θ = sin(2θ) ∂_θ`, we prove the pointwise bound

`|D_θ^i Γ(θ)| ≤ 100000 · Γ(θ)`   for `θ ∈ [0, π/2]`, `0 < α ≤ 1`, `i ≤ 4`,

stated for the two-variable operator `Spaces.DthIter` applied to the `z`-independent
function `(z, θ) ↦ Γ(θ)`.

## Strategy

* `Spaces.dthU` is the one-variable version of `D_θ` (`dthU φ = sin(2·) · φ'`), and
  `Spaces.DthIter i (fun _ θ' => g θ') z θ = dthU^[i] g θ` (`DthIter_rad_eq`).
* The `Spaces` development reduces the angular jets of `Γ` to the coefficient sequence
  `Tfun`: on `(0,π/2)` one has `D_θ^{j+1} Γ = α · Tfun j α · Γ`, and
  `Spaces.dthU_iter_Gam_abs_bound` turns a bound `|Tfun j α| ≤ M` on `Iθ` into
  `|dthU^[j+1] Γ| ≤ α · M · Γ` on all of `Iθ` (both endpoints are handled there by the
  vanishing of `sin(2θ)`).
* So it remains to bound `Tfun j α` for `j ≤ 3` by an explicit constant `≤ 100000`.
  Since `Tfun 0 = qfun` with `qfun θ = cos 2θ - 1/3`, and the recursion
  `Tfun (j+1) = dthU (Tfun j) + α · qfun · Tfun j` differentiates `Tfun j` only through
  `dthU = sin(2θ) ∂_θ`, the sequence `Tfun j α` is, as a function of `v = cos 2θ`, the
  polynomial `Qp j α` defined by

  `Qp 0 α = X - 1/3`,  `Qp (j+1) α = -2(1 - X²)·(Qp j α)' + α·(X - 1/3)·(Qp j α)`

  (use `dthU φ = sin(2θ)φ'(θ)` and `sin²(2θ) = 1 - cos²(2θ)`).  We prove
  `Tfun j α = fun θ => (Qp j α).eval (cos 2θ)` for every `j` (`Tfun_eq_Qp`, by induction,
  the step being the chain rule for `θ ↦ (Qp j α).eval (cos 2θ)`), and then bound the
  first four polynomials by explicit numbers on `[-1,1]` (`Qp_eval_bound`):

  `|Qp 0| ≤ 4/3`,  `|Qp 1| ≤ 34/9`,  `|(Qp 1)'| ≤ 20/3`,  `|Qp 2| ≤ 496/27`,
  `|(Qp 2)'| ≤ 154/3`,  `|Qp 3| ≤ 10300/81`

  for `|v| ≤ 1`, `0 ≤ α ≤ 1`.  Each is obtained recursively from the previous ones by
  bounding the products in the recursion (`abs_add_le` + product bounds), e.g.
  `|Qp j+1| ≤ 2|1-v²|·|(Qp j)'| + α|v-1/3|·|Qp j| ≤ 2|(Qp j)'| + (4/3)|Qp j|`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## `DthIter` on functions of `θ` alone -/

/-- On a function of `θ` alone, the two-variable operator `D_θ` agrees with the
one-variable operator `Spaces.dthU`. -/
theorem DthIter_rad_eq (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => g θ') z θ = Work.Spaces.dthU^[i] g θ := by
  have h : (fun (_ : ℝ) (θ : ℝ) => g θ) = (fun (z : ℝ) (θ : ℝ) => g θ * (1 : ℝ)) := by
    funext z θ; ring
  rw [h, Work.Spaces.DthIter_decomp]
  ring

/-! ## The polynomial majorant of `Tfun` -/

/-- The `j`-th coefficient polynomial of the angular jet of `Γ`, as a polynomial in
`v = cos 2θ`; the recursion is `Q_{j+1}(v) = -2(1 - v²)Q_j'(v) + α(v - 1/3)Q_j(v)`. -/
noncomputable def Qp : ℕ → ℝ → Polynomial ℝ
  | 0, _ => Polynomial.X - Polynomial.C (1 / 3)
  | (j + 1), α => Polynomial.C (-2) * (1 - Polynomial.X ^ 2) * (Qp j α).derivative
      + Polynomial.C α * (Polynomial.X - Polynomial.C (1 / 3)) * (Qp j α)

/-- One step of the recursion, evaluated. -/
theorem Qp_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).eval v
      = -2 * (1 - v ^ 2) * (Qp j α).derivative.eval v + α * (v - 1 / 3) * (Qp j α).eval v := by
  rw [Qp]; simp

/-- The chain rule for `θ ↦ (Qp j α).eval (cos 2θ)`. -/
theorem deriv_Qp_cos (j : ℕ) (α θ : ℝ) :
    deriv (fun t : ℝ => (Qp j α).eval (Real.cos (2 * t))) θ
      = (Qp j α).derivative.eval (Real.cos (2 * θ)) * (-(2 * Real.sin (2 * θ))) := by
  rw [show (fun t : ℝ => (Qp j α).eval (Real.cos (2 * t)))
      = ((fun v : ℝ => (Qp j α).eval v) ∘ (fun t : ℝ => Real.cos (2 * t))) from rfl,
    deriv_comp]
  · rw [Polynomial.deriv]
    congr 1
    rw [show (fun t : ℝ => Real.cos (2 * t)) = (Real.cos ∘ (fun t : ℝ => 2 * t)) from rfl,
      deriv_comp]
    · rw [Real.deriv_cos]; simp; ring
    · exact Real.differentiableAt_cos
    · fun_prop
  · exact (Polynomial.hasDerivAt (Qp j α) _).differentiableAt
  · fun_prop

/-- **`Tfun j α` is the polynomial `Qp j α` evaluated at `v = cos 2θ`.** -/
theorem Tfun_eq_Qp (j : ℕ) (α : ℝ) :
    Work.Spaces.Tfun j α = fun θ => (Qp j α).eval (Real.cos (2 * θ)) := by
  induction j with
  | zero =>
      funext θ
      simp [Qp, Work.Spaces.qfun_apply]
  | succ j ih =>
      have hfun : (fun t : ℝ => Work.Spaces.Tfun j α t)
          = (fun t : ℝ => (Qp j α).eval (Real.cos (2 * t))) := by
        rw [ih]
      funext θ
      rw [Work.Spaces.Tfun_succ, hfun, deriv_Qp_cos, ih, Work.Spaces.qfun_apply, Qp_succ_eval]
      dsimp only []
      have hD : (Qp j α).derivative.eval (Real.cos (2 * θ))
          * (Real.sin (2 * θ) ^ 2 + Real.cos (2 * θ) ^ 2 - 1) = 0 := by
        rw [Real.sin_sq_add_cos_sq]; ring
      nlinarith [hD]

/-! ## Elementary absolute-value facts -/

/-- Product bound from bounds on the two factors. -/
theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hA

theorem abs_one_sub_sq_le_one {v : ℝ} (hv : |v| ≤ 1) : |1 - v ^ 2| ≤ 1 := by
  have hv1 : -1 ≤ v := (abs_le.mp hv).1
  have hv2 : v ≤ 1 := (abs_le.mp hv).2
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg v]

theorem abs_sub_third_le {v : ℝ} (hv : |v| ≤ 1) : |v - 1 / 3| ≤ 4 / 3 := by
  have hv1 : -1 ≤ v := (abs_le.mp hv).1
  have hv2 : v ≤ 1 := (abs_le.mp hv).2
  rw [abs_le]; constructor <;> linarith

theorem abs_two_mul_le_two {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |2 * α| ≤ 2 := by
  rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num, abs_of_nonneg hα0]
  simpa using mul_le_mul_of_nonneg_left hα1 (by norm_num : (0 : ℝ) ≤ 2)

theorem abs_four_add_two_mul_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : |4 + 2 * α| ≤ 6 := by
  rw [abs_le]; constructor <;> linarith

/-! ## The four polynomials, evaluated -/

theorem Qp0_eval (α v : ℝ) : (Qp 0 α).eval v = v - 1 / 3 := by
  simp [Qp]

theorem Qp1_eval (α v : ℝ) :
    (Qp 1 α).eval v = (-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2 := by
  simp [Qp]; ring

theorem Qp1_deriv_eval (α v : ℝ) :
    (Qp 1 α).derivative.eval v = 4 * v + 2 * α * (v - 1 / 3) := by
  simp [Qp]; ring

theorem Qp2_eval (α v : ℝ) :
    (Qp 2 α).eval v = (-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
      + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2) := by
  simp [Qp]; ring

theorem Qp2_deriv_eval (α v : ℝ) :
    (Qp 2 α).derivative.eval v
      = 4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
        + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
        + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)) := by
  simp [Qp]; ring

theorem Qp3_eval (α v : ℝ) :
    (Qp 3 α).eval v
      = (-2 : ℝ) * (1 - v ^ 2)
          * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
              + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
              + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
        + α * (v - 1 / 3)
          * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
              + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)) := by
  simp [Qp]; ring

/-! ## Explicit bounds for `j ≤ 3` -/

theorem Qp0_eval_bound {α v : ℝ} (hv : |v| ≤ 1) : |(Qp 0 α).eval v| ≤ 4 / 3 := by
  rw [Qp0_eval]
  exact (abs_sub_third_le hv).trans (by norm_num)

theorem Qp1_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 1 α).eval v| ≤ 34 / 9 := by
  rw [Qp1_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have h3 : |(v - 1 / 3) ^ 2| ≤ (16 / 9 : ℝ) := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) h2 2).trans_eq (by norm_num)
  have hA : |(-2 : ℝ) * (1 - v ^ 2)| ≤ 2 * 1 := by
    refine abs_mul_le_of (A := 2) (B := 1) ?_ h1 (by norm_num)
    rw [show |(-2 : ℝ)| = 2 from by norm_num]
  have hB : |α * (v - 1 / 3) ^ 2| ≤ 1 * (16 / 9) :=
    abs_mul_le_of (A := 1) (B := 16 / 9) (by rwa [abs_of_nonneg hα0]) h3 (by norm_num)
  calc |(-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2|
      ≤ |(-2 : ℝ) * (1 - v ^ 2)| + |α * (v - 1 / 3) ^ 2| := abs_add_le _ _
    _ ≤ 2 * 1 + 1 * (16 / 9) := add_le_add hA hB
    _ = 34 / 9 := by norm_num

theorem Qp1_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 1 α).derivative.eval v| ≤ 20 / 3 := by
  rw [Qp1_deriv_eval]
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hA : |(4 : ℝ) * v| ≤ 4 * 1 :=
    abs_mul_le_of (A := 4) (B := 1) (by norm_num) hv (by norm_num)
  have hB : |2 * α * (v - 1 / 3)| ≤ 2 * (4 / 3) := by
    rw [show (2 : ℝ) * α * (v - 1 / 3) = (2 * α) * (v - 1 / 3) by ring]
    exact abs_mul_le_of (A := 2) (B := 4 / 3) (abs_two_mul_le_two hα0 hα1) h2 (by norm_num)
  calc |4 * v + 2 * α * (v - 1 / 3)| ≤ |(4 : ℝ) * v| + |2 * α * (v - 1 / 3)| := abs_add_le _ _
    _ ≤ 4 * 1 + 2 * (4 / 3) := add_le_add hA hB
    _ = 20 / 3 := by norm_num

theorem Qp2_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 2 α).eval v| ≤ 496 / 27 := by
  rw [Qp2_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hR : |4 * v + 2 * α * (v - 1 / 3)| ≤ 20 / 3 := by
    rw [← Qp1_deriv_eval]; exact Qp1_deriv_bound hα0 hα1 hv
  have hQ : |(-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2| ≤ 34 / 9 := by
    rw [← Qp1_eval]; exact Qp1_eval_bound hα0 hα1 hv
  have hA : |(-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))| ≤ 2 * 1 * (20 / 3) := by
    rw [show (-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
        = ((-2 : ℝ) * (1 - v ^ 2)) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 20 / 3)
      (by rw [abs_mul]; norm_num; exact h1) hR (by norm_num)
  have hB : |α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
      ≤ 1 * (4 / 3) * (34 / 9) := by
    rw [show α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
        = (α * (v - 1 / 3)) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 34 / 9)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ (by norm_num)
  calc |(-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
        + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (20 / 3) + 1 * (4 / 3) * (34 / 9) := add_le_add hA hB
    _ = 496 / 27 := by norm_num

theorem Qp2_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 2 α).derivative.eval v| ≤ 154 / 3 := by
  rw [Qp2_deriv_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hR : |4 * v + 2 * α * (v - 1 / 3)| ≤ 20 / 3 := by
    rw [← Qp1_deriv_eval]; exact Qp1_deriv_bound hα0 hα1 hv
  have hQ : |(-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2| ≤ 34 / 9 := by
    rw [← Qp1_eval]; exact Qp1_eval_bound hα0 hα1 hv
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hA : |4 * v * (4 * v + 2 * α * (v - 1 / 3))| ≤ 4 * 1 * (20 / 3) := by
    rw [show 4 * v * (4 * v + 2 * α * (v - 1 / 3))
        = (4 * v) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 4 * 1) (B := 20 / 3)
      (by rw [abs_mul]; norm_num; exact hv) hR (by norm_num)
  have hB : |((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)| ≤ 2 * 1 * 6 :=
    abs_mul_le_of (A := 2 * 1) (B := 6) (by rw [abs_mul]; norm_num; exact h1) h4 (by norm_num)
  have hC : |α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)| ≤ 1 * (34 / 9) :=
    abs_mul_le_of (A := 1) (B := 34 / 9) (by rwa [abs_of_nonneg hα0]) hQ (by norm_num)
  have hD : |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| ≤ 1 * (4 / 3) * (20 / 3) := by
    rw [show α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))
        = (α * (v - 1 / 3)) * (4 * v + 2 * α * (v - 1 / 3)) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 20 / 3)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hR (by norm_num)
  have hsplit := abs_add_le (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
      + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
      (α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
  have hsplit2 := abs_add_le (4 * v * (4 * v + 2 * α * (v - 1 / 3))
      + (-2 * (1 - v ^ 2)) * (4 + 2 * α))
      (α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
  have hsplit3 := abs_add_le (4 * v * (4 * v + 2 * α * (v - 1 / 3)))
      ((-2 * (1 - v ^ 2)) * (4 + 2 * α))
  calc |4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
        + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
        + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))|
      = |(4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
          + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
          + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by ring_nf
    _ ≤ |4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)
          + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := hsplit
    _ = |(4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α))
          + α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by ring_nf
    _ ≤ (|4 * v * (4 * v + 2 * α * (v - 1 / 3)) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)|
          + |α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|)
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by
        linarith [hsplit2, abs_nonneg (α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))]
    _ = (|(4 * v * (4 * v + 2 * α * (v - 1 / 3))) + (-2 * (1 - v ^ 2)) * (4 + 2 * α)|
          + |α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|)
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by ring_nf
    _ ≤ (|4 * v * (4 * v + 2 * α * (v - 1 / 3))| + |(-2 * (1 - v ^ 2)) * (4 + 2 * α)|
          + |α * (-2 * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)|)
        + |α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| := by
        linarith [hsplit3]
    _ ≤ (4 * 1 * (20 / 3) + 2 * 1 * 6 + 1 * (34 / 9)) + 1 * (4 / 3) * (20 / 3) := by
        linarith [hA, hB, hC, hD]
    _ = 154 / 3 := by norm_num

set_option maxHeartbeats 1600000 in
theorem Qp3_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).eval v| ≤ 10300 / 81 := by
  rw [Qp3_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hQ2 : |(-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
      + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)| ≤ 496 / 27 := by
    rw [← Qp2_eval]; exact Qp2_eval_bound hα0 hα1 hv
  have hR2 : |4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
      + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
      + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))| ≤ 154 / 3 := by
    rw [← Qp2_deriv_eval]; exact Qp2_deriv_bound hα0 hα1 hv
  have hA : |(-2 : ℝ) * (1 - v ^ 2)
      * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
          + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
          + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))| ≤ 2 * 1 * (154 / 3) := by
    rw [show (-2 : ℝ) * (1 - v ^ 2)
        * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
            + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
            + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
        = ((-2 : ℝ) * (1 - v ^ 2))
          * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
            + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
            + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3))) by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 154 / 3)
      (by rw [abs_mul]; norm_num; exact h1) hR2 (by norm_num)
  have hB : |α * (v - 1 / 3)
      * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
          + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))|
      ≤ 1 * (4 / 3) * (496 / 27) := by
    rw [show α * (v - 1 / 3)
        * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
            + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))
        = (α * (v - 1 / 3))
          * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
            + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)) by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 496 / 27)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ2 (by norm_num)
  calc |(-2 : ℝ) * (1 - v ^ 2)
        * (4 * v * (4 * v + 2 * α * (v - 1 / 3)) + ((-2 : ℝ) * (1 - v ^ 2)) * (4 + 2 * α)
            + α * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2)
            + α * (v - 1 / 3) * (4 * v + 2 * α * (v - 1 / 3)))
        + α * (v - 1 / 3)
          * ((-2 : ℝ) * (1 - v ^ 2) * (4 * v + 2 * α * (v - 1 / 3))
              + α * (v - 1 / 3) * ((-2 : ℝ) * (1 - v ^ 2) + α * (v - 1 / 3) ^ 2))|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (154 / 3) + 1 * (4 / 3) * (496 / 27) := add_le_add hA hB
    _ = 10300 / 81 := by norm_num

/-- **The bound for the coefficient polynomials.** -/
theorem Qp_eval_bound (j : ℕ) (hj : j ≤ 3) (α v : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hv : |v| ≤ 1) : |(Qp j α).eval v| ≤ 100000 := by
  interval_cases j
  · exact (Qp0_eval_bound (α := α) hv).trans (by norm_num)
  · exact (Qp1_eval_bound hα0 hα1 hv).trans (by norm_num)
  · exact (Qp2_eval_bound hα0 hα1 hv).trans (by norm_num)
  · exact (Qp3_eval_bound hα0 hα1 hv).trans (by norm_num)

/-- **The bound `|Tfun j α θ| ≤ 100000` for `j ≤ 3`.** -/
theorem Tfun_abs_le (j : ℕ) (hj : j ≤ 3) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 100000 := by
  rw [Tfun_eq_Qp j α]
  exact Qp_eval_bound j hj α (Real.cos (2 * θ)) (le_of_lt hα) hα1
    (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

/-! ## The main statement -/

theorem DthIter_Gam_abs_le (i : ℕ) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    linarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Tfun_abs_le (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 100000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS.LocData
