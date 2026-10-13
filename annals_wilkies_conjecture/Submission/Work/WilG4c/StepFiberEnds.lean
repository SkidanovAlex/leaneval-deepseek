import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.FiberEndsLo
import Submission.Work.WilG4c.FiberEndsA.A_lo_mem
import Submission.Work.WilG4c.FiberEndsHi

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **BNZ §2.3 (fibre ends).**  For an `Ω`-set `Z ⊆ ℝ^{m+1}` whose points all lie in the
open unit interval in the last coordinate, the pointwise infimum and supremum of the fibre
`Z_l = {x | (l,x) ∈ Z}` are `Ω`-definable functions of `l`, with a format independent of the
degree `D` and a degree polynomial in `D`.  Both ends are exact (lower/upper bound and
sharp). -/
theorem StepFiberEnds (S : SOMin) (m F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D r : ℕ) (Z : Set (Fin (m + 1) → ℝ)), Z ∈ S.Ω F0 D (m + 1) →
      (∀ z ∈ Z, z (Fin.last m) ∈ Set.Ioo (0 : ℝ) 1) →
      ∃ (lo hi : (Fin m → ℝ) → ℝ),
        graphOf lo ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (m + 1) ∧
        graphOf hi ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (m + 1) ∧
        ∀ l : Fin m → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ Z) →
          (∀ x : ℝ, Fin.snoc l x ∈ Z → lo l ≤ x ∧ x ≤ hi l) ∧
          (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < u) ∧
          (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ u < x) :=
  stepFiberEnds_aux S m F0 (FiberEndsA.A_lo_mem S m F0) (A_hi_mem_alt S m F0)
    (fun Z hI => hiOf_graph_props_alt m Z hI)

end Work.WilG4c
