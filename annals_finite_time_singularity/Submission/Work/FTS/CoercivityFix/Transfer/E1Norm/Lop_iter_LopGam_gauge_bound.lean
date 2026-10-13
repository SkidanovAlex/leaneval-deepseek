import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.AngGam
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `α`-gain in the angular iterate bound for `Lop^i (Lop (Gam α))`, with the gauge factor

`Γ = Gam α = (sinθ cos²θ)^{α/3}` has `Lop (Gam α) = (α/3)(6cos²θ - 4)·Γ`, so for `1 ≤ k` the
iterate `Lop^[k] (Gam α)` equals `Γ θ` times the explicit polynomial coefficient
`(2α/3)·Aang (k-1)(cos²θ, α)` (`E1Parts.Lop_iter_Gam_succ`).  The `Construction` bounds give,
for `1 ≤ j ≤ 3` and `x = cos²θ ∈ [0,1]`,

`|Aang j x α| ≤ 10^7·(α + 4x(1-x)) = 10^7·(α + sin(2θ)²)`,

which is *not* just an absolute constant: it carries the gauge factor `sin(2θ)² + α` that
vanishes at both ends of `Iθ`, exactly where `Γ` degenerates.  Consequently, for `1 ≤ i ≤ 3`
and `θ ∈ Iθ`,

`|Lop^[i] (Lop (Gam α)) θ| ≤ 10^7·α·Γ(θ)·(sin(2θ)² + α)`,

the gauge version of the `E1`-transfer pointwise input.  The hypothesis `1 ≤ i` is essential:
the excluded case `i = 0` involves `Aang 0 = 3x - 2`, which is `≠ 0` at `x = 1` (i.e. at
`θ = 0`), where the gauge factor degenerates to `α`.

At the endpoints `θ = 0, π/2` both sides vanish because the outermost `Lop` carries the factor
`sin(2θ) = 0`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

/-- `Lop^[i] (Lop f) = Lop^[i+1] f`. -/
lemma Lop_iter_Lop_eq_gauge (f : ℝ → ℝ) (i : ℕ) :
    (Work.Spaces.Lop^[i] (Work.Spaces.Lop f)) = (Work.Spaces.Lop^[i + 1] f) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]

/-- `Lop^[n] f` vanishes at `θ = 0` for `n ≥ 1` (the outermost `Lop` carries `sin(2·0) = 0`). -/
lemma Lop_iter_apply_zero (f : ℝ → ℝ) : ∀ n : ℕ, 0 < n → (Work.Spaces.Lop^[n] f) 0 = 0 := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Function.iterate_succ_apply']
  simp only [Work.Spaces.Lop]
  rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, zero_mul]

/-- `Lop^[n] f` vanishes at `θ = π/2` for `n ≥ 1`. -/
lemma Lop_iter_apply_pi_half (f : ℝ → ℝ) : ∀ n : ℕ, 0 < n →
    (Work.Spaces.Lop^[n] f) (π / 2) = 0 := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Function.iterate_succ_apply']
  simp only [Work.Spaces.Lop]
  rw [show Real.sin (2 * (π / 2)) = 0 by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi], zero_mul]

/-- `sin(2θ)² = 4 cos²θ (1 - cos²θ)`. -/
lemma sin_two_sq_eq (θ : ℝ) :
    Real.sin (2 * θ) ^ 2 = 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) := by
  rw [Real.sin_two_mul]
  have h := Real.sin_sq θ
  nlinarith [h]

/-- The interior pointwise bound: for `1 ≤ i ≤ 3` and `θ ∈ (0, π/2)`. -/
lemma Lop_iter_LopGam_gauge_bound_interior (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ)
    (hi1 : 1 ≤ i) (hi3 : i ≤ 3) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ|
      ≤ 10 ^ 7 * α * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  have hGam := Work.Spaces.Gam_bounds α θ hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hx : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨sq_nonneg _, Real.cos_sq_le_one θ⟩
  rw [Lop_iter_Lop_eq_gauge,
    Work.FTS.CoercivityFix.Transfer.E1Parts.Lop_iter_Gam_succ α hα i (by omega) θ hθ,
    abs_mul, abs_of_nonneg hGam.1]
  -- the polynomial coefficient bound, with the gauge factor
  have hA : |Work.Construction.Aang i (Real.cos θ ^ 2) α|
      ≤ 10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)) := by
    interval_cases i
    · exact Work.Construction.glop_Aang_bound_one _ _ hx hα hα1
    · exact Work.Construction.glop_Aang_bound_two _ _ hx hα hα1
    · exact Work.Construction.glop_Aang_bound_three _ _ hx hα hα1
  have hcoef : |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
      ≤ 10 ^ 7 * α * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)) := by
    have h23 : (0 : ℝ) ≤ 2 * α / 3 := by linarith
    have hM : 0 ≤ α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) := by
      nlinarith [hx.1, hx.2, hα]
    have hle : 2 * α / 3 ≤ α := by linarith
    calc |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
        = 2 * α / 3 * |Work.Construction.Aang i (Real.cos θ ^ 2) α| := by
          rw [abs_mul, abs_of_nonneg h23]
      _ ≤ 2 * α / 3 * (10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
          mul_le_mul_of_nonneg_left hA h23
      _ ≤ α * (10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (by norm_num) hM)
      _ = 10 ^ 7 * α * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)) := by ring
  rw [sin_two_sq_eq θ]
  calc Work.Spaces.Gam α θ
        * |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
      ≤ Work.Spaces.Gam α θ
          * (10 ^ 7 * α * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
        mul_le_mul_of_nonneg_left hcoef hGam.1
    _ = 10 ^ 7 * α * Work.Spaces.Gam α θ * (4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) + α) := by
        ring

theorem Lop_iter_LopGam_gauge_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ|
          ≤ K * α * Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α) := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi3 θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · -- `θ = 0`: both sides vanish
    subst h0
    rw [Lop_iter_Lop_eq_gauge, Lop_iter_apply_zero (Work.Spaces.Gam α) (i + 1) (by omega),
      abs_zero]
    have hG := Work.Spaces.Gam_bounds α 0 hα ⟨le_refl 0, by positivity⟩
    have hs : 0 ≤ Real.sin (2 * 0) ^ 2 + α := by
      have := sq_nonneg (Real.sin (2 * 0)); linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hα)) hG.1) hs
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · -- `θ = π/2`: both sides vanish
    subst h1
    rw [Lop_iter_Lop_eq_gauge, Lop_iter_apply_pi_half (Work.Spaces.Gam α) (i + 1) (by omega),
      abs_zero]
    have hG := Work.Spaces.Gam_bounds α (π / 2) hα ⟨by positivity, le_refl _⟩
    have hs : 0 ≤ Real.sin (2 * (π / 2)) ^ 2 + α := by
      have := sq_nonneg (Real.sin (2 * (π / 2))); linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hα)) hG.1) hs
  · exact Lop_iter_LopGam_gauge_bound_interior α hα hα1 i hi1 hi3 θ ⟨h0, h1⟩

end Work.FTS.CoercivityFix.Transfer.E1Norm
