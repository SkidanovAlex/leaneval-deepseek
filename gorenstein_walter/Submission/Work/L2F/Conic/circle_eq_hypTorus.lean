import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_circle
import Submission.Work.L2F.Conic.mem_hypTorus

namespace Work.L2F.Conic

/-- The centralizer of `z` is the norm-one torus for `d = -1`: both are
`{!![a,b;-b,a] | a² + b² = 1}`, the second because `hypTorus F (-1)` consists of the matrices
`!![a, -b; b, a]` with `a² + b² = 1` and `-b` runs over `F`.  Uses `mem_circle` and `mem_hypTorus`. -/
theorem circle_eq_hypTorus (F : Type*) [Field F] : Work.L2F.circle F = Work.L2F.hypTorus F (-1) := by
  ext x
  rw [mem_circle, mem_hypTorus]
  constructor
  · -- `x = !![a, b; -b, a]` with `a² + b² = 1`: rewrite as the `hypTorus` element with index `-b`.
    rintro ⟨a, b, hab, hx⟩
    refine ⟨a, -b, ?_, ?_⟩
    · have h : a ^ 2 - (-1 : F) * (-b) ^ 2 = a ^ 2 + b ^ 2 := by ring
      rw [h]; exact hab
    · rw [hx]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · -- `x = !![a, -b; b, a]` with `a² + b² = 1`: rewrite as the `circle` element with index `-b`.
    rintro ⟨a, b, hab, hx⟩
    refine ⟨a, -b, ?_, ?_⟩
    · have h : a ^ 2 + (-b) ^ 2 = a ^ 2 - (-1 : F) * b ^ 2 := by ring
      rw [h]; exact hab
    · rw [hx]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp

end Work.L2F.Conic
