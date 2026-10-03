import Mathlib
import Submission.Work.FatouCoord.Setup

/-!
# The quadratic coefficient of a parabolic germ is intrinsic

Two quantitative `ParabolicBounds` hypotheses for the *same* map `f` (possibly with different
multiplier functions `h`, `h'`, radii `r`, `r'` and constants) determine the same value of the
quadratic coefficient `a`.  Indeed, on the punctured intersection of the two discs the equations
`f z = z + z ^ 2 * h z` and `f z = z + z ^ 2 * h' z` force `h = h'`, while the two closeness
bounds give `h z = 1 + a z + O(z ^ 2)` and `h' z = 1 + a' z + O(z ^ 2)`.  Comparing at real
`z = t → 0` yields `‖a - a'‖ ≤ (A + A₂) * t → 0`.
-/

namespace Work.Parab.coordData

open Set Metric

theorem parabolicBounds_aeq {f h h' : ℂ → ℂ} {a a' : ℂ} {r r' A A₁ A₂ A₃ : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A₁)
    (hb' : Work.FatouCoord.ParabolicBounds f h' a' r' A₂ A₃) : a = a' := by
  have hr : 0 < r := hb.hr
  have hr' : 0 < r' := hb'.hr
  have hA : 0 ≤ A := hb.hA
  have hA₂ : 0 ≤ A₂ := hb'.hA
  -- the two multiplier functions agree on the punctured common disc
  have hhh : ∀ z : ℂ, z ∈ ball (0 : ℂ) r → z ∈ ball (0 : ℂ) r' → z ≠ 0 → h z = h' z := by
    intro z hz hz' hz0
    have e1 : f z = z + z ^ 2 * h z := hb.f_eq z hz
    have e2 : f z = z + z ^ 2 * h' z := hb'.f_eq z hz'
    have hsq : z ^ 2 * h z = z ^ 2 * h' z := by
      rw [e1] at e2
      exact add_left_cancel e2
    exact mul_left_cancel₀ (pow_ne_zero 2 hz0) hsq
  -- the quantitative bound along the positive real axis
  have key : ∀ t : ℝ, 0 < t → t < r → t < r' → ‖a - a'‖ ≤ (A + A₂) * t := by
    intro t ht htr htr'
    have hzt : (t : ℂ) ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact htr
    have hzt' : (t : ℂ) ∈ ball (0 : ℂ) r' := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact htr'
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hh : h (t : ℂ) = h' (t : ℂ) := hhh _ hzt hzt' ht0
    have h1 := hb.h_close (t : ℂ) hzt
    have h2 := hb'.h_close (t : ℂ) hzt'
    have hnorm : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hmain : ‖a - a'‖ * t ≤ (A + A₂) * t ^ 2 := by
      have hsub : (a - a') * (t : ℂ)
          = (h' (t : ℂ) - 1 - a' * (t : ℂ)) - (h (t : ℂ) - 1 - a * (t : ℂ)) := by
        rw [hh]; ring
      calc ‖a - a'‖ * t = ‖(a - a') * (t : ℂ)‖ := by rw [norm_mul, hnorm]
        _ = ‖(h' (t : ℂ) - 1 - a' * (t : ℂ)) - (h (t : ℂ) - 1 - a * (t : ℂ))‖ := by
              rw [hsub]
        _ ≤ ‖h' (t : ℂ) - 1 - a' * (t : ℂ)‖ + ‖h (t : ℂ) - 1 - a * (t : ℂ)‖ :=
              norm_sub_le _ _
        _ ≤ A₂ * ‖(t : ℂ)‖ ^ 2 + A * ‖(t : ℂ)‖ ^ 2 := add_le_add h2 h1
        _ = (A + A₂) * t ^ 2 := by rw [hnorm]; ring
    have hfac : ‖a - a'‖ * t ≤ ((A + A₂) * t) * t := by
      calc ‖a - a'‖ * t ≤ (A + A₂) * t ^ 2 := hmain
        _ = ((A + A₂) * t) * t := by ring
    exact le_of_mul_le_mul_right hfac ht
  -- squeeze the norm of `a - a'` to zero
  have hzero : ‖a - a'‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set t : ℝ := min (min r r' / 2) (ε / (A + A₂ + 1)) with htdef
    have hminpos : 0 < min r r' := lt_min hr hr'
    have hden : 0 < A + A₂ + 1 := by linarith
    have htpos : 0 < t := by
      rw [htdef]
      exact lt_min (by linarith) (div_pos hε hden)
    have htlt : t < min r r' := by
      rw [htdef]
      calc min (min r r' / 2) (ε / (A + A₂ + 1)) ≤ min r r' / 2 := min_le_left _ _
        _ < min r r' := by linarith
    have hbnd := key t htpos (lt_of_lt_of_le htlt (min_le_left _ _))
      (lt_of_lt_of_le htlt (min_le_right _ _))
    have hsmall : (A + A₂) * t ≤ ε := by
      have hle2 : t ≤ ε / (A + A₂ + 1) := by
        rw [htdef]; exact min_le_right _ _
      calc (A + A₂) * t ≤ (A + A₂) * (ε / (A + A₂ + 1)) :=
            mul_le_mul_of_nonneg_left hle2 (by linarith)
        _ = (A + A₂) * ε / (A + A₂ + 1) := by ring
        _ ≤ ε := by
            rw [div_le_iff₀ hden]
            nlinarith [hε]
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))

end Work.Parab.coordData
