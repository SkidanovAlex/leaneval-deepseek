import Mathlib
import Submission.Work.Peluse.Ulower.gap_defs

namespace Work.Peluse.Ulower

open Work.Peluse

/-! ## Finite support is preserved by the peel

The peel step `Δ'_{a,b} F = fun x => F (x + a) * conj (F (x + b))` is a pointwise product of two
values of `F` at points shifted by `a` resp. `b`; hence if `F` vanishes off `[-N,N]`, then
`Δ'_{a,b} F` vanishes off `[-(N+|a|+|b|), N+|a|+|b|]`.  Iterating gives the statement. -/

/-- One step of the peel preserves finite support. -/
private lemma finSuppZ_iterDeltaStep' {s : ℤ × ℤ} {F : ℤ → ℂ}
    (h : Work.Peluse.FinSuppZ F) : Work.Peluse.FinSuppZ (iterDeltaStep s F) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + s.1.natAbs + s.2.natAbs, fun x hx => ?_⟩
  have hxa : F (x + s.1) = 0 := by
    refine hN _ ?_
    have htri : x.natAbs ≤ (x + s.1).natAbs + s.1.natAbs := by
      have h := Int.natAbs_add_le (x + s.1) (-s.1)
      rw [Int.natAbs_neg] at h
      simpa using h
    omega
  simp [iterDeltaStep, hxa]

/-- Iterating the peel preserves finite support. -/
private lemma finSuppZ_iterDelta' : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ),
    Work.Peluse.FinSuppZ F → Work.Peluse.FinSuppZ (iterDelta k sh F) := by
  intro k
  induction k with
  | zero =>
      intro sh F h
      rwa [iterDelta_zero]
  | succ k ih =>
      intro sh F h
      rw [iterDelta_succ]
      exact finSuppZ_iterDeltaStep' (ih (fun i => sh i.succ) F h)

theorem iterDelta_finsupp_bound {k : ℕ} (sh : Fin k → ℤ × ℤ) {F : ℤ → ℂ}
    (h : Work.Peluse.FinSuppZ F) : Work.Peluse.FinSuppZ (Work.Peluse.Ulower.iterDelta k sh F) :=
  finSuppZ_iterDelta' k sh F h

end Work.Peluse.Ulower
