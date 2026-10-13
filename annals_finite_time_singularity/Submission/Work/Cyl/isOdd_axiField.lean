import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Work.Cyl

namespace Work.Cyl

/-!
# Parity of the no-swirl field `axiField a b`

`axiField a b x = a (r²) (x₃) • (x₀, x₁, 0) + b (r²) (x₃) • e₃` with `r² = x₀² + x₁²`.

The parity condition `FiniteTimeSingularity.IsOdd` asks, for each component `i`, that the field
be odd in coordinate `i` and even in the other two.  Reflection in coordinate `0` (resp. `1`)
leaves `r²` and `x₃` unchanged and only flips the prefactor `x₀` (resp. `x₁`), so those two
conjuncts hold *unconditionally*.  Reflection in the axial coordinate `2` leaves `r²` unchanged
but sends `x₃ ↦ -x₃` inside the profiles, so the whole content of the definition is

* `a` is even in its second argument `x₃` — this is only forced for `r² > 0`, because on the
  axis (`r² = 0`) the first two components vanish identically and impose nothing on `a`;
* `b` is odd in its second argument `x₃` — forced for `r² ≥ 0`, including the axis, since the
  third component is exactly `b r² x₃`.

This is the "even in `r² > 0` / odd in `r² ≥ 0`" asymmetry of the statement.
-/

/-! ## Coordinates of `axiField` and of the vector notation -/

private lemma axiField_apply_zero (a b : ℝ → ℝ → ℝ) (x : R3) :
    (axiField a b x) 0 = a (radSq x) (axial x) * x 0 := by
  simp [axiField]

private lemma axiField_apply_one (a b : ℝ → ℝ → ℝ) (x : R3) :
    (axiField a b x) 1 = a (radSq x) (axial x) * x 1 := by
  simp [axiField]

private lemma axiField_apply_two (a b : ℝ → ℝ → ℝ) (x : R3) :
    (axiField a b x) 2 = b (radSq x) (axial x) := by
  simp [axiField]

private lemma vec3_radSq (x₀ x₁ x₂ : ℝ) :
    radSq (!₂[x₀, x₁, x₂] : R3) = x₀ ^ 2 + x₁ ^ 2 := by
  simp [radSq]

private lemma vec3_axial (x₀ x₁ x₂ : ℝ) : axial (!₂[x₀, x₁, x₂] : R3) = x₂ := by
  simp [axial]

theorem isOdd_axiField (a b : ℝ → ℝ → ℝ) :
    FiniteTimeSingularity.IsOdd (Work.Cyl.axiField a b) ↔
      (∀ s, 0 < s → ∀ z, a s (-z) = a s z) ∧ (∀ s, 0 ≤ s → ∀ z, b s (-z) = -b s z) := by
  constructor
  · -- **Forward**: read off the parity of the profiles from the third conjunct (reflection `x₃ ↦ -x₃`).
    intro h
    refine ⟨?_, ?_⟩
    · -- `a` even in `x₃` for `r² > 0`: evaluate at `(√s, 0, ±z)`, where the first component is
      -- `a s (∓z) * √s`, and cancel the nonzero factor `√s`.
      intro s hs z
      have h1 := (h.2.2 (Real.sqrt s) 0).1 z
      simp only [axiField_apply_zero, vec3_radSq, vec3_axial] at h1
      have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt (le_of_lt hs)
      have hsp : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
      rw [hs2] at h1
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h1
      exact mul_right_cancel₀ hsp h1
    · -- `b` odd in `x₃` for `r² ≥ 0`: the third component of the field is exactly `b (r²) x₃`.
      intro s hs z
      have h1 := (h.2.2 (Real.sqrt s) 0).2.2 z
      simp only [axiField_apply_two, vec3_radSq, vec3_axial] at h1
      have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
      rw [hs2] at h1
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h1
      exact h1
  · -- **Backward**: assemble `IsOdd` from the two parity hypotheses.
    rintro ⟨ha, hb⟩
    refine ⟨?_, ?_, ?_⟩
    · -- Reflection in coordinate `0`: `r²` and `x₃` are unchanged; only `x₀` flips.
      intro x₁ x₂
      refine ⟨?_, ?_, ?_⟩
      · intro t; simp [axiField, radSq, axial]
      · intro t; simp [axiField, radSq, axial]
      · intro t; simp [axiField, radSq, axial]
    · -- Reflection in coordinate `1`: same, with `x₁` flipping.
      intro x₀ x₂
      refine ⟨?_, ?_, ?_⟩
      · intro t; simp [axiField, radSq, axial]
      · intro t; simp [axiField, radSq, axial]
      · intro t; simp [axiField, radSq, axial]
    · -- Reflection in the axial coordinate `2`: `x₃ ↦ -x₃` inside the profiles.
      intro x₀ x₁
      refine ⟨?_, ?_, ?_⟩
      · -- first component even: needs `ha` unless `x₀ = 0` (where both sides vanish).
        intro t
        by_cases hx₀ : x₀ = 0
        · simp [axiField, radSq, axial, hx₀]
        · have hs : 0 < x₀ ^ 2 + x₁ ^ 2 := by
            nlinarith [sq_pos_of_ne_zero hx₀, sq_nonneg x₁]
          have key : a (x₀ ^ 2 + x₁ ^ 2) (-t) = a (x₀ ^ 2 + x₁ ^ 2) t := ha _ hs t
          have h2 : (axiField a b (!₂[x₀, x₁, -t] : R3)) 0
              = a (x₀ ^ 2 + x₁ ^ 2) (-t) * x₀ := by
            simp [axiField, radSq, axial]
          have h3 : (axiField a b (!₂[x₀, x₁, t] : R3)) 0
              = a (x₀ ^ 2 + x₁ ^ 2) t * x₀ := by
            simp [axiField, radSq, axial]
          show (axiField a b (!₂[x₀, x₁, -t] : R3)) 0
              = (axiField a b (!₂[x₀, x₁, t] : R3)) 0
          rw [h2, h3, key]
      · -- second component even: same, with `x₁`.
        intro t
        by_cases hx₁ : x₁ = 0
        · simp [axiField, radSq, axial, hx₁]
        · have hs : 0 < x₀ ^ 2 + x₁ ^ 2 := by
            nlinarith [sq_pos_of_ne_zero hx₁, sq_nonneg x₀]
          have key : a (x₀ ^ 2 + x₁ ^ 2) (-t) = a (x₀ ^ 2 + x₁ ^ 2) t := ha _ hs t
          have h2 : (axiField a b (!₂[x₀, x₁, -t] : R3)) 1
              = a (x₀ ^ 2 + x₁ ^ 2) (-t) * x₁ := by
            simp [axiField, radSq, axial]
          have h3 : (axiField a b (!₂[x₀, x₁, t] : R3)) 1
              = a (x₀ ^ 2 + x₁ ^ 2) t * x₁ := by
            simp [axiField, radSq, axial]
          show (axiField a b (!₂[x₀, x₁, -t] : R3)) 1
              = (axiField a b (!₂[x₀, x₁, t] : R3)) 1
          rw [h2, h3, key]
      · -- third component odd: `hb` at `r² = x₀² + x₁² ≥ 0`, including the axis.
        intro t
        have h2 : (axiField a b (!₂[x₀, x₁, -t] : R3)) 2 = b (x₀ ^ 2 + x₁ ^ 2) (-t) := by
          simp [axiField, radSq, axial]
        have h3 : (axiField a b (!₂[x₀, x₁, t] : R3)) 2 = b (x₀ ^ 2 + x₁ ^ 2) t := by
          simp [axiField, radSq, axial]
        show (axiField a b (!₂[x₀, x₁, -t] : R3)) 2
            = -(axiField a b (!₂[x₀, x₁, t] : R3)) 2
        rw [h2, h3, hb _ (by positivity) t]

end Work.Cyl
