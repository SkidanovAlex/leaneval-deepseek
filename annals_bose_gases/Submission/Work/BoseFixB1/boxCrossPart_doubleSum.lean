import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PairBlockCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxCrossPart_doubleSum` — the cross part as an iterated double sum

`boxCrossPart V ℓ A w₁ Φ` is defined (`Submission/Work/BoseFixB1/PairBlockCore.lean`) as the
sum over the *ordered distinct-pair set* `pairSet N = {(i,j) : i ≠ j}` of the per-pair integrals
of `pairCross`:

    boxCrossPart = ∑_{p ∈ pairSet N} ∫_{abox N ℓ} pairCross p .

This file rewrites that `pairSet`-sum into the *iterated double sum* over `Fin N × Fin N` with the
diagonal terms replaced by `0`:

    boxCrossPart = ∑ i, ∑ j, if i ≠ j then ∫_{abox N ℓ} pairCross (i,j) else 0 .

Since, with `P_i = boxPInd V A i` and `Q_i = boxQInd V A i`,

    pairCross (i,j) = (P_i Q_j Φ + P_j Q_i Φ) · (P_i P_j Φ) · w₁(x_i, x_j) ,

the right-hand side is precisely the two-orientation cross term displayed index by index: the
`i`- and `j`-slots of the two opposite orientations `(P_i Q_j Φ)(P_i P_j Φ)w₁` and
`(P_j Q_i Φ)(P_i P_j Φ)w₁` are visible, which is what the later manipulations of the cross part
(for instance the pairing of the two orientations against the swapped summand) need.

The content is purely combinatorial; the only non-definitional input is the `Finset` splitting
`∑_{p ∈ s.filter P} f p = ∑_{p ∈ s} if P p then f p else 0`.

No hypotheses on `w₁`, `Φ` or the box are needed: the identity is a rearrangement of the
summation index, valid for the Bochner/Lebesgue integral with its default (`∫ = 0` for
non-integrable functions) convention.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixB1

set_option autoImplicit false

/-- **The ordered distinct-pair sum as an iterated double sum.**
For any `g : Fin N × Fin N → ℝ`, the sum over `pairSet N` (the ordered pairs of *distinct*
indices) is the full double sum over `Fin N × Fin N` with the diagonal terms replaced by `0`. -/
theorem sum_pairSet_eq_doubleSum {N : ℕ} (g : Fin N × Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, g p)
      = ∑ i : Fin N, ∑ j : Fin N, if i ≠ j then g (i, j) else 0 := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]

/-- **The box cross part as a double sum.**  Unfolding `boxCrossPart` (a sum over `pairSet N`,
i.e. over the ordered pairs `(i,j)` with `i ≠ j`) and applying `sum_pairSet_eq_doubleSum`
leaves the iterated sum over `Fin N × Fin N` whose summand is the per-pair cross integrand read
at `(i,j)`. -/
theorem boxCrossPart_doubleSum {N : ℕ} (V ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB1.boxCrossPart V ℓ A W Φ
      = ∑ i : Fin N, ∑ j : Fin N,
          if i ≠ j then ∫ x in Submission.BoseGases.abox N ℓ,
              ((Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
                + (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x))
              * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
              * W (x i) (x j)
            else 0 := by
  unfold boxCrossPart
  rw [show (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ, pairCross V A W Φ p x)
      = ∑ i : Fin N, ∑ j : Fin N, if i ≠ j then
          ∫ x in Submission.BoseGases.abox N ℓ, pairCross V A W Φ (i, j) x else 0 from
      sum_pairSet_eq_doubleSum
        (fun p => ∫ x in Submission.BoseGases.abox N ℓ, pairCross V A W Φ p x)]
  simp only [pairCross]

end Work.BoseFixB1
