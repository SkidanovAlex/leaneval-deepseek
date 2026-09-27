import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic

/-!
# Shift vocabulary for `avg_shift_integral`

The target lemma `Work.EKLComp.ErgMax.avg_shift_integral` compares the integrals of a bounded
continuous `f : X₃ →ᵇ ℝ` against the `A⁺`-average `avg ν N` and against its pushforward under
`act (aPlus r s)`.  Both integrals expand into normalised double sums of the single function

  `psi ν f u v = ∫ y, f (aPlus u v • y) ∂ν`,

evaluated at the grid parameters `(i/N, j/N)` resp. `(i/N + r, j/N + s)`.  The proof of the target
therefore splits into (a) the two integral expansions and (b) a purely real-analytic comparison of
the two double sums, both of which are stated in terms of the vocabulary below.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

/-! ## The real-parameter grid -/

/-- `shiftR u v = u • g1 + v • g2`, the real-parameter version of `shift`. -/
def shiftR (u v : ℝ) : Fin 3 → ℝ := u • g1 + v • g2

/-- The integral grid is the `shiftR`-grid: `shift N i j = shiftR (i/N) (j/N)`. -/
theorem shift_eq_shiftR (N i j : ℕ) : shift N i j = shiftR ((i : ℝ) / N) ((j : ℝ) / N) := rfl

/-- `aDiag` of a `shiftR`-vector is `aPlus`. -/
theorem aDiag_shiftR (u v : ℝ) : aDiag (shiftR u v) = aPlus u v := by
  rw [aPlus, shiftR]
  congr 1
  funext k
  fin_cases k <;> simp [g1, g2] <;> ring

/-- The two generators commute with their own translates: `aPlus (u+r) (v+s) = aPlus r s * aPlus u v`. -/
theorem aPlus_add_swap (r s u v : ℝ) : aPlus (u + r) (v + s) = aPlus r s * aPlus u v := by
  rw [← aPlus_add u v r s, aPlus_add_comm]

/-- `aPlus r s * aDiag (shift N i j) = aDiag (shiftR (i/N + r) (j/N + s))`: pushing `aPlus r s`
after a grid point is the same as re-indexing the grid by `(i/N + r, j/N + s)`. -/
theorem aPlus_mul_aDiag_shift (r s : ℝ) (N i j : ℕ) :
    aPlus r s * aDiag (shift N i j) = aDiag (shiftR ((i : ℝ) / N + r) ((j : ℝ) / N + s)) := by
  rw [aDiag_shift, aPlus_add, add_comm r ((i : ℝ) / N), add_comm s ((j : ℝ) / N),
    aDiag_shiftR]

/-! ## The averaged integrand -/

/-- `psi ν f u v = ∫ y, f (aPlus u v • y) ∂ν`: the value of `f`-integral against the
`aPlus u v`-translate of `ν`. -/
def psi (ν : Measure X3) (f : BoundedContinuousFunction X3 ℝ) (u v : ℝ) : ℝ := ∫ y, f (aPlus u v • y) ∂ν

@[simp] theorem psi_apply (ν : Measure X3) (f : BoundedContinuousFunction X3 ℝ) (u v : ℝ) :
    psi ν f u v = ∫ y, f (aPlus u v • y) ∂ν := rfl

end

end Work.EKLComp.ErgMax
