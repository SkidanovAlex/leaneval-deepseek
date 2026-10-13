/-
  WilG4c / `CritFixDefs` — the *corrected* punctured-limit criterion.

  The frozen criterion `Work.WilkG4c.Crit` (`AlSliceBase`) restricts, at order `m`, the counts
  vector `c` to `Fin (m + 1)`, i.e. to counts `≤ m - 1`.  The counts of a word
  `v : Fin m → Fin (n+1)` satisfy `wordCounts v ≤ m`, so the constant word
  `(d, …, d)` with `d ≠ n` — the `m`-th derivative in a single direction — is *never* covered
  by the frozen criterion: with `m = 1` only `∂_n` is constrained.  Consequently
  `Crit ∩ AlGood ⊆ AlDgListSlice` is false (counterexample: `p = 0`, `n = 1`, `L = [1]`,
  `f = |y 0|`).

  This module defines the corrected index set, in which the counts at order `m` are bounded by
  `m` (the bound `Fin (m + 2)`), which does cover the constant words and therefore all words once
  one adds permutation invariance of `iteratedFDeriv`.  The definitions mirror `AlSliceBase`
  verbatim apart from that bound.
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The corrected index set of the limit conditions: at order `m`, the counts vector has entries
`≤ m` (instead of `≤ m - 1` in the frozen `critIdx`). -/
def critIdxFix (n k : ℕ) : Finset (Σ m : Fin k, Fin (n + 1) → Fin (m.val + 2)) :=
  Finset.sigma Finset.univ (fun _ => Finset.univ)

/-- The corrected value-free criterion at a single point. -/
def UVFix (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  contSet p n f ∩ ⋂ i ∈ critIdxFix n k, LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val)

/-- The corrected localised punctured-limit criterion. -/
def LocCritFix (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | ∃ ρ : ℝ, 0 < ρ ∧ ∀ w' : Fin (p + (n + 1)) → ℝ,
    parPt w' = parPt (Fin.init z) →
      dist (cubePt w') (cubePt (Fin.init z)) < ρ → w' ∈ UVFix p n f L.length}

/-- The corrected punctured-limit criterion. -/
def CritFix (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    Set (Fin (p + (n + 1) + 1) → ℝ) :=
  LocCritFix p n f L ∩ {z | z ∈ Work.WilG4c.LimeqP p n
    (dgSet p n f L.length (fun j => L.get j))}

/-- Membership in `CritFix`, unfolded. -/
theorem mem_CritFix {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (n + 1))} {z : Fin (p + (n + 1) + 1) → ℝ} :
    z ∈ CritFix p n f L ↔
      z ∈ LocCritFix p n f L ∧
        z ∈ Work.WilG4c.LimeqP p n (dgSet p n f L.length (fun j => L.get j)) :=
  Iff.rfl

end Work.WilkG4c
