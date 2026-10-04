/-
# Flat ("torus") tame-estimate vocabulary for the B3 transport assembly

This module fixes two small definitions used by the *tame* (Gagliardo–Nirenberg based) estimates
for the coefficient matrix of the B3 transport identity `tmA φ lam' (tmGfi D h j)`:

* `HasGNBound m U K f` — the (sharp-exponent) Gagliardo–Nirenberg bound for a smooth `1`-periodic
  `f : (ι → ℝ) → ℂ` with sup bound `U`, at order `m`, with constant `K`.  It is *exactly* the
  conclusion of `Work.Diff.STE.GN_torus`.

* `ENormSqMat m M` — the `H^m` energy of a matrix-valued periodic function, the sum over the
  entries of `Work.Diff.STE.ENormSq m`.

These are the hypotheses/conclusions in which the Moser-type estimate for the inverse of a bounded
matrix field (`Work.Diff.STE.B3.ENormSq_mat_inv_le`) is stated.
-/
import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

/-- **The Gagliardo–Nirenberg bound** for a `1`-periodic `f : (ι → ℝ) → ℂ` with sup bound `U`, at
order `m`: every `j`-th order partial derivative (`1 ≤ j ≤ m`) satisfies
`∫_{cube} ‖∂^β f‖^{2m/j} ≤ K · U^{2m/j - 2} · ENormSq m f`.

(This is the sharp-exponent Gagliardo–Nirenberg inequality on the unit torus; it is the conclusion
of `Work.Diff.STE.GN_torus`.) -/
def HasGNBound {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (U K : ℝ)
    (f : (ι → ℝ) → ℂ) : Prop :=
  ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (β : Fin j → ι),
    ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pdVec j β f x‖ ^ ((2 * (m : ℝ)) / (j : ℝ))
      ≤ K * U ^ ((2 * (m : ℝ)) / (j : ℝ) - 2) * Work.Diff.STE.ENormSq m f

/-- The `H^m` energy of a matrix-valued `1`-periodic function: the sum of the `Work.Diff.STE.ENormSq`
of its entries. -/
def ENormSqMat {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (m : ℕ)
    (M : (ι → ℝ) → Fin n → Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, Work.Diff.STE.ENormSq m (fun x => M x i j)

end Work.Diff.STE.B3
