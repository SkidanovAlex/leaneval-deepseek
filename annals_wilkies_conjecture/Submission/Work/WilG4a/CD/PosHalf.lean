/-
  WilG4a/CD — a *clean* copy of the positivity half-space and its `Ω`-membership.

  The legacy module `Submission.Work.WilG4a.lip_loci_defs` (and, through it,
  `Submission.Work.WilG4a.LipChartsDefs`) defines `posHalf_y`/`posHalf_mem_y` in the
  `Work.WilG4a` namespace **and** re-defines `Work.WilG4a.strip`, which clashes with the
  definition in `Submission.Work.WilG4a.f1affine1_defs`.  Since the cell-decomposition
  assembly must import both the `CD` development and `f1affine1_defs`, the `CD` tree needs
  its own copy of the two helpers; they are placed in the `CD` namespace so that they can
  coexist with the legacy ones.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a.CD

open WilkiesDesign

/-- The positivity half-space `{v | 0 < v k}`. -/
def posHalf_y (n : ℕ) (k : Fin n) : Set (Fin n → ℝ) := {v | 0 < v k}

/-- The positivity half-space is `Ω`-definable: it is the positivity set of the linear
polynomial `X k`, of total degree `1`, hence lies in format `n + 2` and degree `3`. -/
theorem posHalf_mem_y (S : SOMin) (n : ℕ) (k : Fin n) (D : ℕ) :
    posHalf_y n k ∈ S.Ω (n + 2) ((Polynomial.C 3).eval D) n := by
  have h := Work.WilG1.Calc.pos_mem (S := S) D (MvPolynomial.X k : MvPolynomial (Fin n) ℝ)
  have hset : {x : Fin n → ℝ | 0 < MvPolynomial.eval x (MvPolynomial.X k : MvPolynomial (Fin n) ℝ)}
      = posHalf_y n k := by
    ext v
    simp [posHalf_y]
  rw [hset] at h
  have htd : (MvPolynomial.X k : MvPolynomial (Fin n) ℝ).totalDegree + 2 = 3 := by
    rw [MvPolynomial.totalDegree_X]
  simpa [htd] using h

end Work.WilG4a.CD
