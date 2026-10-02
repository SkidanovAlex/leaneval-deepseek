import Mathlib
import Submission.Work.SeedSimple2.Rotation.rotation_monotone_eq_self

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A monotone orbit driven by an integer "carry" cannot stay monotone in one direction

`Rotation/rotation_monotone_eq_self.lean` proves that a strictly *increasing*
`1024`-orbit of fractional parts lying in an arc of length `≤ 1` is impossible,
via the helper `no_strict_increasing_int_orbit`.

Here we add the mirror statement for a strictly *decreasing* orbit (obtained by
negating the sequence, which turns a decreasing orbit equation into an
increasing one) and deduce the disjunction form requested by the caller.
-/

namespace Work.SeedSimple2.Rotation

/-- The mirror of `no_strict_increasing_int_orbit`: no strictly *decreasing*,
bounded below real sequence satisfies `x (n+1) - x n = a * x n + b - m n` with
`m n` integral and `a > 0`.  This follows from the increasing statement applied
to `n ↦ -x n`. -/
theorem no_strict_decreasing_int_orbit {x : ℕ → ℝ} {m : ℕ → ℤ} {a b : ℝ} (ha : 0 < a)
    (hineq : ∀ n, x (n + 1) - x n = a * x n + b - (m n : ℝ))
    (hdec : ∀ n, x (n + 1) < x n)
    (hbdd : ∃ B, ∀ n, B ≤ x n) : False := by
  refine no_strict_increasing_int_orbit (x := fun n => -x n) (m := fun n => -m n)
    (a := a) (b := -b) ha ?_ ?_ ?_
  · intro n
    have h := hineq n
    push_cast
    linarith
  · intro n
    have h := hdec n
    linarith
  · obtain ⟨B, hB⟩ := hbdd
    exact ⟨-B, fun n => by have h := hB n; linarith⟩

/-- The requested lemma: a `1024`-orbit of fractional parts, monotone in *one*
fixed direction and lying in an interval of length `≤ 1`, cannot exist. -/
theorem rotation_monotone_eq_self_mono {c0 d0 α θ : ℝ} (hcd : d0 ≤ c0 + 1)
    (harc : ∀ n : ℕ, Int.fract ((1024 : ℝ) ^ n * θ - α) ∈ Set.Ioo c0 d0)
    (hmono : (∀ n : ℕ, Int.fract ((1024 : ℝ) ^ n * θ - α)
        < Int.fract ((1024 : ℝ) ^ (n + 1) * θ - α)) ∨
      (∀ n : ℕ, Int.fract ((1024 : ℝ) ^ (n + 1) * θ - α)
        < Int.fract ((1024 : ℝ) ^ n * θ - α))) : False := by
  rcases hmono with hinc | hdec
  · exact rotation_monotone_eq_self hcd harc hinc
  · refine no_strict_decreasing_int_orbit
      (x := fun n => Int.fract ((1024 : ℝ) ^ n * θ - α))
      (m := fun n => ⌊(1024 : ℝ) ^ (n + 1) * θ - α⌋
        - (1024 : ℤ) * ⌊(1024 : ℝ) ^ n * θ - α⌋)
      (a := 1023) (b := 1023 * α) (by norm_num) ?_ ?_ ?_
    · intro n
      have h4 : (1024 : ℝ) ^ (n + 1) * θ - α
          = 1024 * ((1024 : ℝ) ^ n * θ - α) + 1023 * α := by
        rw [pow_succ]; ring
      have h1 : Int.fract ((1024 : ℝ) ^ (n + 1) * θ - α)
          = ((1024 : ℝ) ^ (n + 1) * θ - α)
            - (⌊(1024 : ℝ) ^ (n + 1) * θ - α⌋ : ℝ) := rfl
      have h2 : Int.fract ((1024 : ℝ) ^ n * θ - α)
          = ((1024 : ℝ) ^ n * θ - α) - (⌊(1024 : ℝ) ^ n * θ - α⌋ : ℝ) := rfl
      rw [h1, h2]
      push_cast
      linarith [h4]
    · exact hdec
    · exact ⟨c0, fun n => (harc n).1.le⟩

end Work.SeedSimple2.Rotation
