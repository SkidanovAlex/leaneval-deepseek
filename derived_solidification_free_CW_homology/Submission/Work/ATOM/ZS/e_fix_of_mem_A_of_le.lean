import Mathlib
import Submission.Work.ATOM.ZS.Data

namespace Work.ATOM.ZS

open CategoryTheory LightProfinite

/-- A point of `A_m = range (e_m)` is fixed by every idempotent `e_n` with `m ≤ n`
(`A_m ⊆ A_n` by monotonicity, and `e_n` fixes its own image).  This is the "coherence" of the
tower of idempotents of `NOTES_LEAD_solid_gaps1.md` §3.1 used to check the identities
`h₁`, `h₃`, `h₄` of REFS/03 §1. -/
theorem e_fix_of_mem_A_of_le (S : LightProfinite.{0}) [Infinite S] {m n : ℕ} (hmn : m ≤ n)
    {y : ↥S} (hy : y ∈ Work.ATOM.A S m) : Work.ATOM.e S n y = y := by
  -- `e_m ∘ e_n = e_{min m n} = e_m` because `m ≤ n`, so `e_n` fixes the image of `e_m`.
  have h : Work.ATOM.e S n (Work.ATOM.e S m y) = Work.ATOM.e S m y := by
    have h2 := ConcreteCategory.congr_hom (Work.ATOM.e_comp S m n) y
    rw [ConcreteCategory.comp_apply, Nat.min_eq_left hmn] at h2
    exact h2
  rw [← Work.ATOM.e_fixes_of_mem_A S hy, h]

end Work.ATOM.ZS
