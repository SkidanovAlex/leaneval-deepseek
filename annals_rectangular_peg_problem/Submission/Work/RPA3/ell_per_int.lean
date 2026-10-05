import Mathlib
import Submission.Work.RPA3.InjectiveDefs

namespace Work.RPA3

/-- The nonnegative case of `ell_per_int`: the `n`-fold iterate of `LagFamilyAll.per`, by
induction on `n`.  The inductive step shifts `t` by `2π` and uses `Tk_add`. -/
theorem ell_per_nat (L : Work.RPA3.LagFamilyAll) (τ x t : ℝ) (n : ℕ) :
    L.ℓ τ (x, t + 2 * Real.pi * n) = Work.RPA3.Tk n (L.ℓ τ (x, t)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hper : L.ℓ τ (x, t + 2 * Real.pi * n + 2 * Real.pi)
        = Work.RPA3.Tk 1 (L.ℓ τ (x, t + 2 * Real.pi * n)) :=
      L.per τ x (t + 2 * Real.pi * n)
    rw [ih] at hper
    rw [← Work.RPA3.Tk_add] at hper
    have hcast : (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have harg : t + 2 * Real.pi * n + 2 * Real.pi = t + 2 * Real.pi * (n + 1 : ℕ) := by
      push_cast; ring
    rw [hcast, harg] at hper
    exact hper

/-- The Lagrangian family `ℓ` is periodic in the angle `t` for arbitrary integer multiples of
`2π`: `ℓ τ (x, t + 2πk) = Tk k (ℓ τ (x, t))`.  This is the `k`-fold iterate of `LagFamilyAll.per`
(`ℓ τ (x, t+2π) = Tk 1 (ℓ τ (x,t))`), using `Tk_add`. -/
theorem ell_per_int (L : Work.RPA3.LagFamilyAll) (τ x t : ℝ) (k : ℤ) :
    L.ℓ τ (x, t + 2 * Real.pi * k) = Work.RPA3.Tk k (L.ℓ τ (x, t)) := by
  -- The nonnegative case, with the base point left free so that it can be moved in the negative
  -- case below.
  have natlem : ∀ (t : ℝ) (n : ℕ), L.ℓ τ (x, t + 2 * Real.pi * n)
      = Work.RPA3.Tk n (L.ℓ τ (x, t)) := fun t n => ell_per_nat L τ x t n
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · rw [hn]; exact natlem t n
  · -- For `k = -n`, apply the nonnegative case at the base point `t - 2πn` and use that `Tk n` is
    -- inverted by `Tk (-n)`.
    rw [hn]
    have hn' := natlem (t + 2 * Real.pi * (-(n : ℝ))) n
    have harg : (t + 2 * Real.pi * (-(n : ℝ))) + 2 * Real.pi * n = t := by ring
    rw [harg] at hn'
    have h2 := congrArg (Work.RPA3.Tk (-(n : ℤ))) hn'
    rw [Work.RPA3.Tk_neg_apply] at h2
    have harg2 : t + 2 * Real.pi * ↑(-(n : ℤ)) = t + 2 * Real.pi * (-(n : ℝ)) := by
      push_cast; ring
    rw [harg2, ← h2]

end Work.RPA3
