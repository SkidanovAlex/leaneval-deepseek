import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- **Integrality gives a uniform lower bound.**  If `k * y` is an integer (`k ≠ 0`) and
`y` is not an integer, then `fracDist y ≥ 1/|k|`.

Indeed, writing `y = round y + (y - round y)` and multiplying by `k`, the number
`k * (y - round y)` is an integer combination of integers, hence an integer `j`; it is
nonzero because `fracDist y ≠ 0` and `k ≠ 0`.  So `|j| ≥ 1`, while
`|j| = |k| · fracDist y`. -/
private lemma one_le_abs_mul_fracDist {y : ℝ} {k : ℤ} {z : ℤ}
    (hk : k ≠ 0) (hz : (k : ℝ) * y = (z : ℝ)) (hpos : 0 < fracDist y) :
    (1 : ℝ) ≤ |(k : ℝ)| * fracDist y := by
  have hfr : fracDist y = |y - ((round y : ℤ) : ℝ)| := rfl
  set j : ℤ := z - k * round y with hj
  have hj_eq : (j : ℝ) = (k : ℝ) * (y - ((round y : ℤ) : ℝ)) := by
    rw [hj]; push_cast; rw [mul_sub, hz]
  have hjne : j ≠ 0 := by
    intro h0
    have hzero : (k : ℝ) * (y - ((round y : ℤ) : ℝ)) = 0 := by rw [← hj_eq, h0]; simp
    rcases mul_eq_zero.mp hzero with h | h
    · exact hk ((Int.cast_eq_zero).mp h)
    · have : fracDist y = 0 := by rw [hfr, h]; simp
      linarith [hpos]
  have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    have := Int.one_le_abs hjne
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(j : ℝ)| := h1
    _ = |(k : ℝ) * (y - ((round y : ℤ) : ℝ))| := by rw [hj_eq]
    _ = |(k : ℝ)| * |y - ((round y : ℤ) : ℝ)| := abs_mul _ _
    _ = |(k : ℝ)| * fracDist y := by rw [← hfr]

/-- **`α` is irrational.**  If a strictly increasing sequence `q` and positive numbers `Δ m`
satisfy `Δ m = fracDist (q m · α)` and the "best approximation" sharpening
`Δ m < 1/q_{m+1}`, then `α` is irrational: no nonzero integer multiple of `α` is an integer.

The lower bound `1/|k| ≤ fracDist (q m · α)` for the presumed integer multiple `k α ∈ ℤ`
contradicts `fracDist (q m · α) < 1/q_{m+1}` once `q_{m+1} > |k|`. -/
theorem uni_nonres3_irr {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ))) :
    ∀ k : ℤ, k ≠ 0 → Work.TMC16Core.fracDist ((k : ℝ) * α) ≠ 0 := by
  intro k hk hzero
  -- `k * α` is an integer `z0`.
  set z0 : ℤ := round ((k : ℝ) * α) with hz0def
  have hz0 : (k : ℝ) * α = (z0 : ℝ) := by
    have h := abs_eq_zero.mp hzero
    rw [hz0def]
    linarith
  -- Hence `k * (q m * α) = (q m * z0) ∈ ℤ`, and `fracDist (q m * α) ≥ 1/|k|` for every `m`.
  have hkey : ∀ m, (1 : ℝ) ≤ |(k : ℝ)| * Δ m := by
    intro m
    have hpos : 0 < fracDist ((q m : ℝ) * α) := by rw [← hΔeq m]; exact hΔpos m
    have hz : (k : ℝ) * ((q m : ℝ) * α) = (((q m : ℤ) * z0 : ℤ) : ℝ) := by
      push_cast
      have hh : (k : ℝ) * ((q m : ℝ) * α) = (q m : ℝ) * ((k : ℝ) * α) := by ring
      rw [hh, hz0]
    have h := one_le_abs_mul_fracDist (y := (q m : ℝ) * α) hk hz hpos
    rwa [← hΔeq m] at h
  -- `q` grows at least like the identity.
  have hqge : ∀ n, n ≤ q n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have h : n < q n.succ := lt_of_le_of_lt ih (hmono (Nat.lt_succ_self n))
      exact Nat.succ_le_of_lt h
  -- Choose the scale `m` with `q (m+1) > |k|`.
  set A : ℝ := |(k : ℝ)| with hAdef
  have hApos : 0 < A := by
    rw [hAdef, abs_pos]
    exact_mod_cast hk
  set m : ℕ := Nat.ceil A with hmdef
  have hAm : A ≤ (m : ℝ) := Nat.le_ceil A
  have hmq : A < (q (m + 1) : ℝ) := by
    have h1 : (m : ℝ) + 1 ≤ (q (m + 1) : ℝ) := by
      have := hqge (m + 1)
      exact_mod_cast this
    linarith
  have hb : (1 : ℝ) ≤ A * Δ m := by
    have := hkey m
    rwa [hAdef] at this
  have hArecip : 1 / A ≤ Δ m := by
    rw [div_le_iff₀ hApos]
    linarith [hb]
  have hlt := hΔup m
  have h3 : 1 / (q (m + 1) : ℝ) < 1 / A := one_div_lt_one_div_of_lt hApos hmq
  linarith

end Work.TMC16Core.Core
