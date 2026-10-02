import Mathlib
import Submission.Work.FSeed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FSeed.API

/-- **The exact period divides every period.**  If `z` is fixed by `f^[k]`, if no smaller positive
power of `f` fixes `z`, and if `f^[n] z = z`, then `k ∣ n`: writing `n = q·k + r` with `r < k`, the
periodicity of `f^[k]` gives `f^[r] z = z`, and minimality forces `r = 0`. -/
theorem dvd_of_fixed {f : ℂ → ℂ} {z : ℂ} {k n : ℕ} (hk : 0 < k)
    (hmin : ∀ j : ℕ, 0 < j → j < k → (f^[j]) z ≠ z) (hkz : (f^[k]) z = z)
    (hnz : (f^[n]) z = z) : k ∣ n := by
  -- `f^[k]` fixes every point of the orbit of `z` (the iterates of `f` commute)
  have hkfix : ∀ r : ℕ, (f^[k]) ((f^[r]) z) = (f^[r]) z := by
    intro r
    rw [← Function.iterate_add_apply, show k + r = r + k by omega, Function.iterate_add_apply,
      hkz]
  -- hence the orbit of `z` is `k`-periodic
  have hstep : ∀ m : ℕ, ∀ w : ℂ, (f^[k]) w = w → (f^[m + k]) w = (f^[m]) w := by
    intro m w hw
    rw [Function.iterate_add_apply, hw]
  have hper' : ∀ m r : ℕ, (f^[k * m + r]) z = (f^[r]) z := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ m ih =>
        intro r
        rw [Nat.mul_succ, Function.iterate_add_apply, hstep (k * m) _ (hkfix r),
          ← Function.iterate_add_apply]
        exact ih r
  -- hence the residue class of `n` modulo `k` is a period, and minimality kills it
  have hmod : (f^[n % k]) z = z := by
    have h := hper' (n / k) (n % k)
    rw [Nat.div_add_mod n k] at h
    rw [← h]
    exact hnz
  rcases Nat.eq_zero_or_pos (n % k) with h0 | hpos
  · exact Nat.dvd_of_mod_eq_zero h0
  · exact absurd hmod (hmin _ hpos (Nat.mod_lt _ hk))

/-- There is no dividing by zero: an odd divisor of `10` is `1` or `5`. -/
theorem odd_dvd_ten {k : ℕ} (hk : Odd k) (hdvd : k ∣ 10) : k = 1 ∨ k = 5 := by
  have hle : k ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < k := hk.pos
  interval_cases k <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact absurd hdvd (by decide)
      | exact absurd hk (by decide)

end Work.FSeed.API
