import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.Rotation.rotationZero_of_step
import Submission.Work.SeedSimple2.Rotation.arcBound_of_sidePreserve
import Submission.Work.SeedSimple2.Rotation.exists_arc_of_eventually_const

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.COP

/-- **Arithmetic core of the arc bound**: if the `(×1024)`-orbit of `θ` shifted by `α₁` ever hits
the integer `0` mod `1`, it stays there for ever after.  This uses `1024 α₁ = α₁ + 371`:
`1024^n θ = α₁ + m` (`m : ℤ`) gives `1024^{n+1} θ = 1024 α₁ + 1024 m = α₁ + (371 + 1024 m)`. -/
theorem fract_orbit_zero_of_zero (θ : ℝ) :
    ∀ k : ℕ, Int.fract ((1024 : ℝ) ^ k * θ - Work.EL.alpha1) = 0 →
      Int.fract ((1024 : ℝ) ^ (k + 1) * θ - Work.EL.alpha1) = 0 := by
  intro k hk
  obtain ⟨j, hj⟩ := Int.fract_eq_zero_iff.mp hk
  have hj' : (1024 : ℝ) ^ k * θ = Work.EL.alpha1 + (j : ℝ) := by linarith
  show Int.fract ((1024 : ℝ) ^ (k + 1) * θ - Work.EL.alpha1) = 0
  rw [show (1024 : ℝ) ^ (k + 1) * θ = 1024 * ((1024 : ℝ) ^ k * θ) by ring, hj']
  rw [show (1024 : ℝ) * (Work.EL.alpha1 + (j : ℝ)) - Work.EL.alpha1
      = (Work.EL.alpha1 + (j : ℝ) - Work.EL.alpha1) + (((371 : ℤ) + 1023 * j : ℤ) : ℝ) by
    have h1 := Work.SeedSimple2.Rotation.mul_alpha1
    push_cast
    linarith,
    Int.fract_add_intCast]
  rw [show Work.EL.alpha1 + (j : ℝ) - Work.EL.alpha1 = (j : ℝ) by ring, Int.fract_intCast]

/-- **The arc bound is trivial** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L8`; `COP/NOTES_COP.md` §4): every iterate `Int.fract (1024^n θ - α₁)` of a landing angle stays in a fixed arc of length `≤ 1`.  No `hJ`, no flower.

Proof: all `wₙ := Int.fract (1024^n θ - α₁)` lie in `[0,1)`.  If `w_N = 0` for some `N` then `wₙ = 0` for all `n ≥ N` (because `Int.fract (1024^n θ - α₁) = 0` says `1024^n θ = α₁ + m`, `m : ℤ`, and `1024 * α₁ = α₁ + 371`, `Work.SeedSimple2.Rotation.mul_alpha1`), so the set of values is finite and is contained in some `Ioo c₀ d₀` with `d₀ = c₀ + 1`.  Otherwise take `c₀ = 0`, `d₀ = 1`. -/
theorem arcBound_proved : Work.SeedSimple2.Rotation.arcBound := by
  intro c d θ hθ
  let w : ℕ → ℝ := fun n => Int.fract ((1024 : ℝ) ^ n * θ - Work.EL.alpha1)
  have hw0 : ∀ n : ℕ, 0 ≤ w n := fun n => Int.fract_nonneg _
  have hw1 : ∀ n : ℕ, w n < 1 := fun n => Int.fract_lt_one _
  have hstep : ∀ k : ℕ, w k = 0 → w (k + 1) = 0 := fract_orbit_zero_of_zero θ
  by_cases hzero : ∃ N : ℕ, w N = 0
  · -- some iterate is `0`: the orbit is eventually constant at `0`
    obtain ⟨N, hN⟩ := hzero
    have hconst : ∀ n : ℕ, N < n → w n = w N := by
      have hiter : ∀ m : ℕ, w (N + m) = w N := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          have h2 : w ((N + m) + 1) = 0 := hstep (N + m) (by rw [ih]; exact hN)
          rw [show N + (m + 1) = (N + m) + 1 by ring, h2, hN]
      intro n hn
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt hn)
      exact hiter e
    exact Work.SeedSimple2.Rotation.exists_arc_of_eventually_const (v := w) (p := 0)
      le_rfl (by norm_num) hw0 hw1 (Or.inr ⟨N, hconst⟩)
  · -- no iterate is `0`: then every iterate lies in `(0,1)`
    push Not at hzero
    have hpos : ∀ n : ℕ, (0 : ℝ) < w n := by
      intro n
      exact lt_of_le_of_ne (hw0 n) (Ne.symm (hzero n))
    exact Work.SeedSimple2.Rotation.exists_arc_of_eventually_const (v := w) (p := 0)
      le_rfl (by norm_num) hw0 hw1 (Or.inl hpos)

end Work.SeedSimple2.COP
