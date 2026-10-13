/-
  WilG1 / Calc / closure_mem.

  `closure_mem` : the topological closure of an `Ω`-set is an `Ω`-set, with explicit format and
  degree bounds (`a + 3n + 40` and `12·b.eval D + 60`).

  The construction is in `Work.WilG1.Calc.ClosureDefs` (the sets `cylSet`, `hypSet`, `bigJ`,
  `finalC`) and `Work.WilG1.Calc.ClosureStep` (the set-theoretic identity
  `projLast (finalC X) = (closure X)ᶜ` and the `Ω`-membership of `finalC X`).  Here we only
  supply the two reading facts: the closure criterion (`closure_char`) and the coordinate
  reading of `bigJ` in the layout `(x, r, y, s)` (`closure_append_mem`).
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.ClosureStep
import Submission.Work.WilG1.Calc.closure_char
import Submission.Work.WilG1.Calc.closure_append_mem

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Calc

theorem closure_mem {S : WilkiesDesign.SOMin} {n : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {X : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a (b.eval D) n) :
    closure X ∈ S.Ω (a + 3 * n + 40) ((Polynomial.C 12 * b + Polynomial.C 60).eval D) n := by
  refine closure_mem_of (S := S) ?_ ?_ hX
  · intro x
    exact Set.ext_iff.mp (closure_char X) x
  · exact fun x r u => closure_append_mem (x := x) (r := r) (u := u)

end Work.WilG1.Calc
