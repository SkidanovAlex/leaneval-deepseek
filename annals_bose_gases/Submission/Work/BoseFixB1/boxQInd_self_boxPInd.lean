import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

/-- **`Q_{B,i}` kills the range of `P_{B,i}`.**  With FS's box projections
`boxPInd V A i Φ x = (1/V)(∫_{z∈A} Φ(x with z in slot i))·1_A(x_i)` and
`boxQInd = 1_A(·_i)·Φ − P_{B,i}Φ` (FS `eq:HBU`), the composite
`Q_{B,i} ∘ P_{B,i}` vanishes identically.

The two structural facts are (i) `P_{B,i}Φ` is constant along the `i`-th
coordinate, so that averaging it over `A` in the `i`-th slot returns the same
constant, and (ii) the box indicator `1_A(x_i)` takes only the values `0,1`, so
`P_{B,i}Φ x = a·1_A(x_i)` is a fixed point of multiplication by the indicator. -/
theorem boxQInd_self_boxPInd {N : ℕ} {V : ℝ} (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxPInd V A i Φ) x = 0 := by
  -- the box indicator `c = 1_A(x_i)` and the averaged amplitude `a`
  set c : ℝ := A.indicator (fun _ => 1) (x i) with hc
  set a : ℝ := (1 / V) * (∫ z in A, Φ (Function.update x i z)) with ha
  have hne : V ≠ 0 := ne_of_gt hV
  have hc01 : c = 0 ∨ c = 1 := by
    rw [hc]
    by_cases h : x i ∈ A
    · right; exact Set.indicator_of_mem h _
    · left; exact Set.indicator_of_notMem h _
  -- the algebraic core: the indicator is idempotent as a multiplier
  have hkey : ∀ y : ℝ, c * (y * c) - y * c = 0 := by
    intro y; rcases hc01 with h | h <;> rw [h] <;> ring
  -- the value of the box projection at `x`
  have hPx : Work.UBBInputs8.boxPInd V A i Φ x = a * c := by
    rw [Work.UBBInputs8.boxPInd, ha, hc]
  -- `P_{B,i}Φ` is constant along the `i`-th coordinate, hence its average over
  -- the box in that slot is that same constant
  have hPz : ∀ z ∈ A, Work.UBBInputs8.boxPInd V A i Φ (Function.update x i z) = a := by
    intro z hz
    rw [Work.UBBInputs8.boxPInd, ha]
    simp only [Function.update_self i z x, Function.update_idem, Set.indicator_of_mem hz]
    ring
  have hInt : ∫ z in A, Work.UBBInputs8.boxPInd V A i Φ (Function.update x i z) = a * V := by
    rw [setIntegral_congr_fun hA (fun z hz => hPz z hz)]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, hVeq.symm, mul_comm]
  -- hence `P_{B,i}` is a fixed point of itself
  have hQQ : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A i Φ) x = a * c := by
    rw [Work.UBBInputs8.boxPInd, hInt, ← hc]
    have h1 : (1 / V) * (a * V) = a := by field_simp
    rw [h1]
  rw [Work.UBBInputs8.boxQInd, hQQ, hPx, ← hc]
  exact hkey a

end Work.BoseFixB1
