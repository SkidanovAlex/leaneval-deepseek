import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gowers_cube_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Nonnegativity of the Gowers `d`-cube sum for `d ≥ 1` (Gowers's identity: it is a sum
of squares). -/
theorem cubeSum_nonneg {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (hd : 1 ≤ d) (g : G → ℝ) :
    0 ≤ ∑ h : Fin d → G, ∑ x : G,
        ∏ ω : Fin d → Bool, g (x + ∑ i, (if ω i then h i else 0)) := by
  -- `gowers_cube_nonneg` is the statement for `d = (d-1)+1`; rewrite `d` accordingly.
  have h := Commons.Combinatorics.Additive.Gowers.gowers_cube_nonneg g (d - 1)
  rw [Nat.sub_add_cancel hd] at h
  exact h

end Commons.Combinatorics.Transference
