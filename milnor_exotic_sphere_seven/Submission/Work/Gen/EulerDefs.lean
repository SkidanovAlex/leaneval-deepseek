import Mathlib
import Submission.Work.Gen.Euler
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The (complexified) Euler-sequence target bundle over `ℂP⁴`

`Work.Gen.eulerTarget` is the **five-fold sum of `ℂ ⊗ O(1)`** over `ℂP⁴`, i.e.
`(O(1) ⊕ O(-1))⁵`, a complex bundle of rank `10`.  It is the right-hand side of the complexified
Euler sequence `ℂ ⊗ TℂP⁴ ⊕ ε² ≅ (ℂ ⊗ O(1))⁵`, and it is `Work.Gen.stdTangentC 4 ⊕ ε²` up to a
`Work.Thom.BundleIso`; its Chern classes are `(1 - u²)⁵` with `u = c₁(O(1))`.
-/

open Work.Projective
open CategoryTheory

namespace Work.Gen

noncomputable section

/-- **`ℂ ⊗ O(1) = O(1) ⊕ O(-1)`** over `ℂPⁿ`, in the standard fibre `ℂ²`. -/
def lineC (n : ℕ) :
    VectorBundleCore ℂ (CP n) (EuclideanSpace ℂ (Fin 2)) (Fin (n + 1) × Fin (n + 1)) :=
  Work.Whitney.whitneySum (tautDual n) (tautLine n)

@[simp] theorem lineC_baseSet (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) :
    (lineC n).baseSet p = chartSet p.1 ∩ chartSet p.2 := rfl

/-- The index type of `5` copies of `lineC 4`. -/
abbrev lineIdx : Type := Fin 5 × Fin 5

/-- **The five-fold sum of `ℂ ⊗ O(1)`** over `ℂP⁴`: the right-hand side of the complexified Euler
sequence, a complex bundle of rank `10`. -/
def eulerTarget :
    VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 10))
      (lineIdx × lineIdx × lineIdx × lineIdx × lineIdx) :=
  Work.Whitney.whitneySum (lineC 4)
    (Work.Whitney.whitneySum (lineC 4)
      (Work.Whitney.whitneySum (lineC 4)
        (Work.Whitney.whitneySum (lineC 4) (lineC 4))))

end

end Work.Gen
