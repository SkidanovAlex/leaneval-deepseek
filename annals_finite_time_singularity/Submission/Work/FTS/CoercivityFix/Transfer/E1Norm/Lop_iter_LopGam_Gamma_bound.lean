import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.AngGam
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `α`-gain in the angular iterate bound for `Lop^i (Lop (Gam α))`

`Γ = Gam α = (sinθ cos²θ)^{α/3}` has `Lop (Gam α) = (α/3)(6cos²θ - 4)·Γ`, so for `1 ≤ k`
the iterate `Lop^[k] (Gam α)` equals `Γ θ` times the explicit polynomial coefficient
`(2α/3)·Aang (k-1)(cos²θ, α)` (`E1Parts.Lop_iter_Gam_succ`).  The `Construction` bounds give
`|Aang j x α| ≤ 10^7(α + 4x(1-x)) ≤ 2·10^7` on `[0,1]` for `j ≤ 3`, so the explicit factor `α`
in the coefficient survives:

`|Lop^[i] (Lop (Gam α)) θ| ≤ (4/3)·10^7·α·Γ θ ≤ 10^8·α·Γ θ`   (`i ≤ 3`, `θ ∈ Iθ`).

At the endpoints `θ = 0, π/2` both sides vanish because `sin(2θ) = 0` kills the innermost
`Lop`.  This is the pointwise input of the `E1`-transfer estimate: the angular profile
`D_θΓ` enters `E1 = D_θΓ · radA` with a *full* power of `α`.
-/

open scoped Real

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

/-- `Lop^[i] (Lop f) = Lop^[i+1] f`. -/
lemma Lop_iter_Lop_eq (f : ℝ → ℝ) (i : ℕ) :
    (Work.Spaces.Lop^[i] (Work.Spaces.Lop f)) = (Work.Spaces.Lop^[i + 1] f) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]

/-- `|Aang i x α| ≤ 2·10^7` for `i ≤ 3`, `x ∈ [0,1]`, `0 < α ≤ 1`. -/
lemma Aang_abs_le_const (i : ℕ) (hi : i ≤ 3) (x α : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    |Work.Construction.Aang i x α| ≤ 2 * 10 ^ 7 := by
  have hx4 : 4 * x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg (2 * x - 1)]
  interval_cases i
  · rw [Work.Construction.Aang_zero]
    rw [abs_le]
    constructor <;> nlinarith [hx.1, hx.2]
  · have h := Work.Construction.glop_Aang_bound_one x α hx hα hα1
    nlinarith [h, hx4, hα, hα1]
  · have h := Work.Construction.glop_Aang_bound_two x α hx hα hα1
    nlinarith [h, hx4, hα, hα1]
  · have h := Work.Construction.glop_Aang_bound_three x α hx hα hα1
    nlinarith [h, hx4, hα, hα1]

theorem Lop_iter_LopGam_Gamma_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
        |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ|
          ≤ K * α * Work.Spaces.Gam α θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α hα hα1 i hi θ hθ
  rw [Lop_iter_Lop_eq (Work.Spaces.Gam α) i]
  -- the two endpoints of `Iθ`: `sin (2θ) = 0` makes the innermost `Lop` vanish
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hzero : (Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α)) 0 = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, zero_mul]
    rw [hzero, show Work.Spaces.Gam α 0 = (Real.sin 0 * Real.cos 0 ^ 2) ^ (α / 3) from rfl,
      show Real.sin 0 * Real.cos 0 ^ 2 = (0 : ℝ) by norm_num,
      Real.zero_rpow (by positivity : α / 3 ≠ 0), mul_zero]
    norm_num
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1
    have hzero : (Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α)) (π / 2) = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      rw [show Real.sin (2 * (π / 2)) = 0 by
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi], zero_mul]
    rw [hzero, show Work.Spaces.Gam α (π / 2)
        = (Real.sin (π / 2) * Real.cos (π / 2) ^ 2) ^ (α / 3) from rfl,
      show Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = (0 : ℝ) by norm_num,
      Real.zero_rpow (by positivity : α / 3 ≠ 0), mul_zero]
    norm_num
  · -- interior point: use the explicit polynomial form of the iterate
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h1⟩
    rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Lop_iter_Gam_succ α hα i
      (le_trans hi (by norm_num : (3 : ℕ) ≤ 4)) θ hθ']
    have hGam0 : 0 ≤ Work.Spaces.Gam α θ := by
      rw [show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl]
      exact Real.rpow_nonneg (mul_nonneg
        (le_of_lt (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [h1, Real.pi_pos])))
        (sq_nonneg _)) _
    have hA : |Work.Construction.Aang i (Real.cos θ ^ 2) α| ≤ 2 * 10 ^ 7 :=
      Aang_abs_le_const i hi (Real.cos θ ^ 2) α
        ⟨sq_nonneg _, Real.cos_sq_le_one θ⟩ hα hα1
    have hcoef : |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
        ≤ 10 ^ 8 * α := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α / 3)]
      nlinarith [hA, hα]
    rw [abs_mul, abs_of_nonneg hGam0]
    calc Work.Spaces.Gam α θ * |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
        ≤ Work.Spaces.Gam α θ * (10 ^ 8 * α) :=
          mul_le_mul_of_nonneg_left hcoef hGam0
      _ = 10 ^ 8 * α * Work.Spaces.Gam α θ := by ring

end Work.FTS.CoercivityFix.Transfer.E1Norm
