import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxQInd_self_boxPInd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

/-- **`P_{B,i}` is idempotent.**  With FS's box projection (`eq:HBU`)
`boxPInd V A i Φ x = (1/V)(∫_{z∈A} Φ(x with z in slot i))·1_A(x_i)`, applying it twice returns
the same function.

Pointwise, write `c = 1_A(x_i)` and `a = (1/V)∫_{z∈A} Φ(x with z in slot i)`, so that
`P_{B,i}Φ x = a·c`.  For `z ∈ A` the value of `P_{B,i}Φ` at `x` with `z` in slot `i` is again `a`
(the projection is constant along the `i`-th coordinate while the indicator evaluates to `1`), so
the defining average of `P_{B,i}(P_{B,i}Φ)` at `x` equals `(1/V)·(a·V) = a`; multiplying by the
indicator `c` gives `a·c = P_{B,i}Φ x`. -/
theorem boxPInd_self_idem {N : ℕ} {V : ℝ} (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A i Φ)
      = Work.UBBInputs8.boxPInd V A i Φ := by
  funext x
  -- the box indicator `c = 1_A(x_i)` and the averaged amplitude `a`
  set c : ℝ := A.indicator (fun _ => 1) (x i) with hc
  set a : ℝ := (1 / V) * (∫ z in A, Φ (Function.update x i z)) with ha
  -- the value of the box projection at `x`
  have hPx : Work.UBBInputs8.boxPInd V A i Φ x = a * c := by
    rw [Work.UBBInputs8.boxPInd, ha, hc]
  -- `P_{B,i}Φ` is constant along the `i`-th coordinate, with value `a` on the box
  have hPz : ∀ z ∈ A, Work.UBBInputs8.boxPInd V A i Φ (Function.update x i z) = a := by
    intro z hz
    rw [Work.UBBInputs8.boxPInd, ha]
    simp only [Function.update_self i z x, Function.update_idem, Set.indicator_of_mem hz]
    ring
  have hInt : ∫ z in A, Work.UBBInputs8.boxPInd V A i Φ (Function.update x i z) = a * V := by
    rw [setIntegral_congr_fun hA (fun z hz => hPz z hz)]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, hVeq.symm, mul_comm]
  -- hence `P_{B,i}Φ` is a fixed point of `P_{B,i}`
  have hQQ : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A i Φ) x = a * c := by
    rw [Work.UBBInputs8.boxPInd, hInt, ← hc]
    have h1 : (1 / V) * (a * V) = a := by field_simp
    rw [h1]
  rw [hQQ, hPx]

end Work.BoseFixB1
