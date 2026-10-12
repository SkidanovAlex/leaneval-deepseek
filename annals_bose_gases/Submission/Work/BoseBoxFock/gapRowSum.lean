import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.bf3a_cnplus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.gapRowSum` — the gap row of FS `prop:Hamilton2ndQuant`

The gap column of the box word `H_Λ(μ)` is `bℓ⁻²·n₊`, and the `i`-th summand of the row
`Σᵢ gapWordᵢ` is the one-body gap word `gapWord ℓ b 0 ψ = bℓ⁻²·gapBare ℓ 0 ψ` evaluated on
the slot-`i` fibre:

    `Σᵢ ∫_{abox n ℓ} 1_{Λ(0)}(xᵢ)·gapWord ℓ b 0 (fibre n i Φ x) dx
        = bℓ⁻² · (ℓ³ · cnPlus ℓ Φ)`,

where `cnPlus ℓ Φ = Σᵢ ∫_{abox n ℓ} (aQ ℓ i Φ)²` is the excited-particle count.

## Proof

The coefficient `bℓ⁻²` is a constant, so it factors out of every slot integral and out of
the finite sum; what remains is exactly the `b = ℓ²` peel identity already proved as
`Work.BoseBoxFock.bf3a_cnplus`:
`Σᵢ ∫_{abox n ℓ} 1_{Λ(0)}(xᵢ)·gapBare ℓ 0 (fibre n i Φ x) dx = ℓ³·cnPlus ℓ Φ`.
(The `n = 0` case is degenerate: both the empty sum and `cnPlus ℓ Φ` vanish, and
`bf3a_cnplus` covers it.)
-/

namespace Work.BoseBoxFock

theorem gapRowSum {ℓ b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n i Φ x))
      = b * ℓ ^ (-2 : ℤ) * (ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ) := by
  -- the gap word is `bℓ⁻²` times the bare mean-free box mass, pointwise
  have hpt : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n i Φ x)
        = (b * ℓ ^ (-2 : ℤ)) * (Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n i Φ x)) := by
    intro i x
    simp only [Work.BoseKinLoc.gapWord]
    ring
  -- hence the constant factors out of each slot integral
  have hint : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n i Φ x))
        = (b * ℓ ^ (-2 : ℤ)) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n i Φ x)) := by
    intro i
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => hpt i x)
  -- and out of the sum over the slots
  have hsum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n i Φ x))
      = (b * ℓ ^ (-2 : ℤ)) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n i Φ x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hint i
  -- what remains is the `b = ℓ²` peel identity
  calc (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n i Φ x))
      = (b * ℓ ^ (-2 : ℤ)) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n i Φ x)) := hsum
    _ = (b * ℓ ^ (-2 : ℤ)) * (ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ) := by
        rw [bf3a_cnplus hℓ hΦ]
    _ = b * ℓ ^ (-2 : ℤ) * (ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ) := by ring

end Work.BoseBoxFock
