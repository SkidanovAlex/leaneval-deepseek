import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.q1CrossW1csLocalised
import Submission.Work.BoseFixB1S.boxFibLine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-!
# `Work.BoseFixB1.boxQIndFibreCountB1` — the `Q²`-fibre count with the *explicit* constant `Kfib`

This is the sibling `Work.BoseFixB1S.boxFibLine` (`Submission/Work/BoseFixB1S/boxFibLine.lean`)
at its own constant instead of an existential: the localised one-body fibre

  `fib(z) = w1Fibre ℓ (wSmall1Pair h M ℓ d u) z = ∫_{acube ℓ} w_{1,B(u)}(z,y) dy`

is pointwise **nonnegative** and **bounded by `Kfib M`** at the sharp regime
`R₀ ≤ ℓd/16`, `R₀ ≤ ℓ·chiR0`:

* `Work.BoseFixB1S.boxFibLine_fibre_nonneg` — `0 ≤ fib z`;
* `Work.BoseFixB1.q1cw1_w1Fibre_abs_le` — `|fib z| ≤ Kfib M` (from
  `Work.BoseFixB1.wSmall1Pair_fibre_abs_le`).

Hence, for a *continuous* state `Φ` and the FS-faithful mean-free box projection
`Q_{B(u),i} = boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i`, the weighted excited count

  `Σᵢ ∫_{abox N ℓ} (Q_{B(u),i}Φ x)² · fib(xᵢ)`

is at most `Kfib M` times the unweighted excited count
`n₊(B(u)) = Σᵢ ∫ (Q_{B(u),i}Φ)² = Work.BoseFixB1S.boxQCount ...`.

The passage from the pointwise bound to the sum is the monotonicity of the integral on
nonnegative integrands (`MeasureTheory.integral_mono_of_nonneg`), which needs integrability of the
dominating function `(Q_{B(u),i}Φ)²·Kfib M` on the compact box `abox N ℓ` — supplied, for **every**
box mass `volA` (the sliding box may degenerate), by
`Work.BoseFixB1S.integrableOn_boxQInd_sq_mul_const`.
-/

theorem boxQIndFibreCountB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * (Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
      ≤ Work.BoseFixB1.Kfib (v := v) M
        * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  -- the two pointwise facts about the localised fibre
  have hle : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
        ≤ Kfib (v := v) M :=
    fun z => le_trans (le_abs_self _)
      (q1cw1_w1Fibre_abs_le hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u z)
  have hfi_nn : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => Work.BoseFixB1S.boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  -- the constant is nonnegative, so the dominating function is nonnegative
  have hKf_nn : 0 ≤ Kfib (v := v) M := le_trans (hfi_nn 0) (hle 0)
  -- the box measure data of the sliding box
  have hvolnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := le_of_lt hvol
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  rw [Work.BoseFixB1S.boxQCount, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- the dominating function is integrable on the box
  have hint : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 * Kfib (v := v) M)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    Work.BoseFixB1S.integrableOn_boxQInd_sq_mul_const hℓ hvolnn hA hvolA hAc i hΦc
  calc ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 * Kfib (v := v) M :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hfi_nn (x i))))
          hint
          (Filter.Eventually.of_forall
            (fun x => mul_le_mul_of_nonneg_left (hle (x i)) (sq_nonneg _)))
    _ = Kfib (v := v) M * ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 := by
        rw [MeasureTheory.integral_mul_const, mul_comm]

end Work.BoseFixB1
