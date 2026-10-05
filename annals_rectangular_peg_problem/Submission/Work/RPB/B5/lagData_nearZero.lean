import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B2.chordSurf_period_swap

/-!
# B5: the assembled family near `x = 0` is the chord chart of the middle chord

For `|x| < δ` (with `δ` the two-sided junction radius of `LagData.hrhonearδ`) the assembled
point `ℓ τ (x,t) = lagPt W Γc Ac rho τ x t` is the chord of the curve `CI.c` at time `τ` through
the parameter `r = π/2 + π x/(2√2)`, i.e. the chord `(c τ (t+r), c τ (t-r))` seen in `PS`:

`lagPt τ x t = chordSurf CI.c a τ t (π/2 + π x/(2√2))`.

## Proof

`x ≤ 0`: `lagPt = basePt` and `|x| < δ < 1/4 < √2` puts us in the chart branch
`basePt = W τ t (rho τ x t)`, while `hrhonearδ` gives the explicit quadratic
`rho τ x t = π²/4 (1 + x/√2)² = (π/2 + πx/(2√2))²`; the radius `π/2 + πx/(2√2)` lies in
`(0, π/2]`, so `hWchord` identifies the chart with `chordSurf`.

`x > 0`: `lagPt` is `tau π` of the reflected point, i.e. of the chart at `(t - π, -x)` with
radius `π/2 - πx/(2√2) ∈ (0, π/2]`; `chordSurf_period_swap` (the
`a τ (t+π) (π-r) = a τ t r + π` monodromy) turns `tau π (chordSurf τ (t-π) (π/2 - πx/(2√2)))`
into `chordSurf τ t (π/2 + πx/(2√2))`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The "right half" radius `π/2 + πx/(2√2)` in factored form. -/
private lemma pi_half_add_eq (x : ℝ) :
    Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2) = Real.pi / 2 * (1 + x / Real.sqrt 2) := by
  have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The "left half" (inner) radius `π/2 - πx/(2√2)` in factored form. -/
private lemma pi_half_sub_eq (x : ℝ) :
    Real.pi / 2 - Real.pi * x / (2 * Real.sqrt 2) = Real.pi / 2 * (1 - x / Real.sqrt 2) := by
  have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  field_simp

private lemma one_add_div_sqrt_two_pos {x : ℝ} (hx : -Real.sqrt 2 < x) :
    0 < 1 + x / Real.sqrt 2 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  rw [show 1 + x / Real.sqrt 2 = (Real.sqrt 2 + x) / Real.sqrt 2 by field_simp]
  exact div_pos (by linarith) hs2

private lemma one_sub_div_sqrt_two_pos {x : ℝ} (hx : x < Real.sqrt 2) :
    0 < 1 - x / Real.sqrt 2 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  rw [show 1 - x / Real.sqrt 2 = (Real.sqrt 2 - x) / Real.sqrt 2 by field_simp]
  exact div_pos (by linarith) hs2

theorem lagData_nearZero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ x : ℝ, |x| < δ →
      Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t
        = Work.RPB.chordSurf CI.c a τ t (Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2)) := by
  obtain ⟨δ, hδpos, hδ14, _, _, hnear0⟩ := D.hrhonearδ
  refine ⟨δ, hδpos, by linarith, ?_⟩
  intro τ hτ t x hx
  obtain ⟨hxlo, hxhi⟩ := abs_lt.mp hx
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hs2big : (1 : ℝ) / 4 < Real.sqrt 2 := by
    have h := Real.one_lt_sqrt_two; linarith
  by_cases hxle : x ≤ 0
  · -- ## the left half `x ≤ 0`: the chart `W` at the explicit quadratic `rho`
    have hxsqrt : -Real.sqrt 2 < x := by linarith
    have hrr : D.rho τ x t = (Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2)) ^ 2 := by
      rw [hnear0 τ hτ x ⟨hxlo.le, hxle⟩ t]
      ring
    have hpos : 0 < Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2) := by
      rw [pi_half_add_eq]
      exact mul_pos (by positivity) (one_add_div_sqrt_two_pos hxsqrt)
    have hle : Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2) ≤ Real.pi / 2 := by
      rw [pi_half_add_eq]
      have h1 : x / Real.sqrt 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hxle hs2.le
      nlinarith [Real.pi_pos]
    rw [lagPt, ite_eq_left hxle, basePt, ite_eq_right (not_le.mpr hxsqrt), hrr,
      D.hWchord τ hτ t (Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2)) ⟨hpos, hle⟩]
  · -- ## the right half `x > 0`: `tau π` of the reflected chart point
    have hxpos : 0 < x := not_le.mp hxle
    have hxsqrt : x < Real.sqrt 2 := by linarith
    have hnxsq : -Real.sqrt 2 < -x := by linarith
    have hnxle : -x ≤ 0 := by linarith
    have hrr : D.rho τ (-x) (t - Real.pi)
        = (Real.pi / 2 - Real.pi * x / (2 * Real.sqrt 2)) ^ 2 := by
      rw [hnear0 τ hτ (-x) ⟨by linarith, hnxle⟩ (t - Real.pi)]
      ring
    have hspos : 0 < Real.pi / 2 - Real.pi * x / (2 * Real.sqrt 2) := by
      rw [pi_half_sub_eq]
      exact mul_pos (by positivity) (one_sub_div_sqrt_two_pos hxsqrt)
    have hsle : Real.pi / 2 - Real.pi * x / (2 * Real.sqrt 2) ≤ Real.pi / 2 := by
      rw [pi_half_sub_eq]
      have h1 : 0 ≤ x / Real.sqrt 2 := div_nonneg hxpos.le hs2.le
      nlinarith [Real.pi_pos]
    rw [lagPt, ite_eq_right (not_le.mpr hxpos), basePt, ite_eq_right (not_le.mpr hnxsq), hrr,
      D.hWchord τ hτ (t - Real.pi) (Real.pi / 2 - Real.pi * x / (2 * Real.sqrt 2))
        ⟨hspos, hsle⟩]
    -- the swap monodromy `a τ (t+π) (π-r) = a τ t r + π`, i.e. `τ_π ∘ chordSurf (·, r)`
    have hswap := (Work.RPB.B2.chordSurf_period_swap CI a ha).2 τ hτ (t - Real.pi)
      (Real.pi / 2 - Real.pi * x / (2 * Real.sqrt 2))
      ⟨hspos, by linarith [Real.pi_pos, hsle]⟩
    rw [show t - Real.pi + Real.pi = t by ring,
      show Real.pi - (Real.pi / 2 - Real.pi * x / (2 * Real.sqrt 2))
        = Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2) by ring] at hswap
    exact hswap.symm

end Work.RPB.B5
