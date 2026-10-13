/-
# `Work.FTS.PhiStar.Psi0Est.fourCosSqBounds`

The elementary "`4 cos²θ`" divisibility bounds for `P = Pfun α` and its `D_θ`-iterates, i.e. the
two facts

* `4 cos²θ |P(θ)| ≤ C sin 2θ` (a *universal* constant `C`, here `200`), and
* `4 cos²θ |D_θ^j P(θ)| ≤ (κ_j/4 + 4 λ_j) sin 2θ` for `1 ≤ j ≤ 5`, whenever
  `|D_θ^j P| ≤ κ_j α sin²θ cos^{2α/3}θ + λ_j sin 2θ` (`ZClass κ λ`).

Both are "one half of a `sin 2θ`": the point is that whatever constant multiplies
`α sin²θ cos^{2α/3}θ` is absorbed, because `α ≤ 1/4`, `sin²θ cos²θ ≤ 1/4`, `cos^{2α/3}θ ≤ 1`.

Proof strategy.  `P` is bounded by `20` on `[0,π/2]` (`Pfun_abs_le`) and by `30θ²` near `0`
(`Pfun_abs_le_sq`); the `θ ≤ 1/2` branch uses the latter together with `sin 2θ ≥ θ` (from
`Real.mul_le_sin` and `π < 4`), the `θ ≥ 1/2` branch uses the former together with
`sin θ ≥ 1/4` (again from `Real.mul_le_sin` and `π < 4`).  For the iterates the only structural
input is `ZClass`, plus `4 cos²θ sin²θ = sin²(2θ)` and `α · sin 2θ · cos^{2α/3}θ ≤ 1/4`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Psi0Classes
import Submission.Work.FTS.PhiStar.Psi0Defs
import Submission.Work.FTS.PhiStar.Psi0Ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open Work.FTS.PhiStar

/-- The universal bound `4 cos²θ |P(θ)| ≤ 200 sin 2θ` for `0 < α ≤ 1/4`, `θ ∈ (0,π/2)`. -/
lemma fourCosSq_mul_Pfun_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ 200 * Real.sin (2 * θ) := by
  have hθ1 := hθ.1
  have hθ2 := hθ.2
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ1, Real.pi_pos], hθ2⟩
  have hcos2_le : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  rcases le_or_gt θ (1 / 2) with hle | hgt
  · -- small `θ`: `|P| ≤ 30θ²` and `sin 2θ ≥ θ`
    have hP := Pfun_abs_le_sq α hα hα1 (le_of_lt hθ1) hle
    have hstep1 : 4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ 120 * θ ^ 2 := by
      nlinarith [hP, hcos2_le, abs_nonneg (Pfun α θ), sq_nonneg θ]
    have hs2 : θ ≤ Real.sin (2 * θ) := by
      have hms := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ1])
        (by linarith [hle, Real.pi_gt_three])
      have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
      have hthis := mul_le_mul_of_nonneg_right h4 (le_of_lt hθ1)
      rw [one_mul] at hthis
      have hEq : (4 / Real.pi) * θ = 2 / Real.pi * (2 * θ) := by ring
      linarith [hms, hthis, hEq]
    have hstep2 : 120 * θ ^ 2 ≤ 60 * θ := by nlinarith [hle, hθ1]
    linarith [hstep1, hstep2, hs2, hθ1]
  · -- large `θ`: `|P| ≤ 20` and `sin θ ≥ 1/4`
    have hP := Pfun_abs_le α hα hα1 ⟨le_of_lt hθ1, le_of_lt hθ2⟩
    have hsin_ge : (1 : ℝ) / 4 ≤ Real.sin θ := by
      have hms := Real.mul_le_sin (x := (1 : ℝ) / 2) (by norm_num)
        (by linarith [Real.pi_gt_three])
      have hpi4 : (1 : ℝ) / 4 ≤ 2 / Real.pi * (1 / 2) := by
        rw [show 2 / Real.pi * (1 / 2) = 1 / Real.pi from by ring]
        exact one_div_le_one_div_of_le Real.pi_pos (le_of_lt Real.pi_lt_four)
      have hsin_mono : Real.sin (1 / 2) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (le_of_lt hθ2)
          (le_of_lt hgt)
      linarith [hms, hpi4, hsin_mono]
    have hL : 4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ 80 * Real.cos θ := by
      nlinarith [hP, hcos_pos, Real.cos_le_one θ, hcos2_le, abs_nonneg (Pfun α θ)]
    have hR : 100 * Real.cos θ ≤ 200 * Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      nlinarith [hsin_ge, hcos_pos]
    linarith [hL, hR]

/-- The `ZClass` divisibility: `4 cos²θ |D_θ^j P(θ)| ≤ (κ_j/4 + 4 λ_j) sin 2θ`. -/
lemma fourCosSq_mul_dthU_le (j : ℕ) (hj1 : 1 ≤ j) (hj5 : j ≤ 5) (κ ℓ : ℕ → ℝ)
    (hZ : ZClass κ ℓ) (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ (κ j / 4 + 4 * ℓ j) * Real.sin (2 * θ) := by
  have hθ1 := hθ.1
  have hθ2 := hθ.2
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ1, Real.pi_pos], hθ2⟩
  have hcos2_le : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hs_pos : 0 < Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hs_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc_le : Real.cos θ ^ (2 * α / 3) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hcos_pos) (Real.cos_le_one θ) (by linarith [hα])
  have hb := hZ.2.2 α hα hα1 j hj1 hj5 θ hθ
  -- the absorption `α · sin 2θ · cos^{2α/3}θ ≤ 1/4`
  have hkey : α * Real.sin (2 * θ) * Real.cos θ ^ (2 * α / 3) ≤ 1 / 4 := by
    have h1 : α * Real.sin (2 * θ) ≤ 1 / 4 := by
      have := mul_le_mul hα1 hs_le (le_of_lt hs_pos) (by norm_num)
      simpa using this
    have h2 := mul_le_mul h1 hc_le (Real.rpow_nonneg (le_of_lt hcos_pos) _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa using h2
  -- `4 cos²θ · (α sin²θ cos^{2α/3}θ) = (α sin 2θ cos^{2α/3}θ) · sin 2θ`
  have hA : 4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)))
      ≤ (1 / 4) * Real.sin (2 * θ) := by
    have heq : 4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)))
        = (α * Real.sin (2 * θ) * Real.cos θ ^ (2 * α / 3)) * Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hkey (le_of_lt hs_pos)
  have hB : 4 * Real.cos θ ^ 2 * Real.sin (2 * θ) ≤ 4 * Real.sin (2 * θ) := by
    have h4 : 4 * Real.cos θ ^ 2 ≤ 4 := by linarith [hcos2_le]
    exact mul_le_mul_of_nonneg_right h4 (le_of_lt hs_pos)
  have hstep : 4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ 4 * Real.cos θ ^ 2 * (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
          + ℓ j * Real.sin (2 * θ)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hsplit : 4 * Real.cos θ ^ 2 * (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
        + ℓ j * Real.sin (2 * θ))
      = κ j * (4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))))
        + ℓ j * (4 * Real.cos θ ^ 2 * Real.sin (2 * θ)) := by ring
  have hA' : κ j * (4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))))
      ≤ κ j * ((1 / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hA (hZ.1 j)
  have hB' : ℓ j * (4 * Real.cos θ ^ 2 * Real.sin (2 * θ))
      ≤ ℓ j * (4 * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hB (hZ.2.1 j)
  calc 4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ 4 * Real.cos θ ^ 2 * (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
          + ℓ j * Real.sin (2 * θ)) := hstep
    _ = κ j * (4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))))
        + ℓ j * (4 * Real.cos θ ^ 2 * Real.sin (2 * θ)) := hsplit
    _ ≤ κ j * ((1 / 4) * Real.sin (2 * θ)) + ℓ j * (4 * Real.sin (2 * θ)) := add_le_add hA' hB'
    _ = (κ j / 4 + 4 * ℓ j) * Real.sin (2 * θ) := by ring

theorem fourCosSqBounds :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        4 * Real.cos θ ^ 2 * |Work.FTS.PhiStar.Pfun α θ| ≤ C * Real.sin (2 * θ)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ κ ℓ : ℕ → ℝ, Work.FTS.PhiStar.ZClass κ ℓ → ∀ α : ℝ,
        0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Work.FTS.PhiStar.Pfun α) θ|
          ≤ (κ j / 4 + 4 * ℓ j) * Real.sin (2 * θ)) :=
  ⟨⟨200, by norm_num, fun α hα hα1 θ hθ => fourCosSq_mul_Pfun_le α θ hα hα1 hθ⟩,
   fun j hj1 hj5 κ ℓ hZ α hα hα1 θ hθ =>
     fourCosSq_mul_dthU_le j hj1 hj5 κ ℓ hZ α θ hα hα1 hθ⟩

end Work.FTS.PhiStar.Psi0Est
