import Mathlib

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open MeasureTheory ENNReal

/-- Shannon-type lower bound for the integral of a function restricted to a countable
partition of a finite-measure set.  If `D : ι → Set α` is a measurable, pairwise disjoint
family covering `W` and `Φ` dominates, on each piece `D i`, the constant
`-log (ν (D i) / ν W)`, then the normalized integral `(∫_W Φ) / ν W` dominates the
entropy `Σ_i negMulLog (ν (D i) / ν W)`. -/
theorem ofReal_sum_negMulLog_le_lintegral_div {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    {ι : Type*} [Fintype ι] {W : Set α} (hW : MeasurableSet W) (hW0 : ν W ≠ 0) (hWtop : ν W ≠ ⊤)
    {D : ι → Set α} (hD : ∀ i, MeasurableSet (D i)) (hd : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hcov : ⋃ i, D i = W) {Φ : α → ENNReal}
    (h : ∀ i, ∀ᵐ u ∂(MeasureTheory.Measure.restrict ν (D i)),
        ENNReal.ofReal (- Real.log (((ν (D i)).toReal) / ((ν W).toReal))) ≤ Φ u) :
    ENNReal.ofReal (Finset.sum Finset.univ (fun i => Real.negMulLog (((ν (D i)).toReal) / ((ν W).toReal))))
      ≤ (MeasureTheory.lintegral (MeasureTheory.Measure.restrict ν W) Φ) / (ν W) := by
  set b : ℝ := (ν W).toReal with hbdef
  have hbpos : 0 < b := by rw [hbdef]; exact ENNReal.toReal_pos hW0 hWtop
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hbnn : 0 ≤ b := le_of_lt hbpos
  have hofb : ENNReal.ofReal b = ν W := by rw [hbdef]; exact ENNReal.ofReal_toReal hWtop
  have hDsub : ∀ i, D i ⊆ W := fun i => by rw [← hcov]; exact Set.subset_iUnion D i
  have hle_i : ∀ i, ν (D i) ≤ ν W := fun i => MeasureTheory.measure_mono (hDsub i)
  have hfin_i : ∀ i, ν (D i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hWtop (hle_i i)
  have hxnn : ∀ i, 0 ≤ (ν (D i)).toReal := fun i => ENNReal.toReal_nonneg
  have hxi_le : ∀ i, (ν (D i)).toReal ≤ b := fun i => by
    rw [hbdef]; exact ENNReal.toReal_mono hWtop (hle_i i)
  have hofx : ∀ i, ENNReal.ofReal ((ν (D i)).toReal) = ν (D i) :=
    fun i => ENNReal.ofReal_toReal (hfin_i i)
  have hpi0 : ∀ i, 0 ≤ (ν (D i)).toReal / b := fun i => div_nonneg (hxnn i) hbnn
  have hpi1 : ∀ i, (ν (D i)).toReal / b ≤ 1 := fun i => (div_le_one hbpos).mpr (hxi_le i)
  -- Termwise: `ofReal (-log (x/b)) * ν (D i) = ofReal b * ofReal (negMulLog (x/b))`.
  have hterm : ∀ i, ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) * ν (D i)
      = ENNReal.ofReal b * ENNReal.ofReal (Real.negMulLog ((ν (D i)).toReal / b)) := by
    intro i
    have hkey : (ν (D i)).toReal * (- Real.log ((ν (D i)).toReal / b))
        = Real.negMulLog ((ν (D i)).toReal / b) * b := by
      have hp : ((ν (D i)).toReal / b) * b = (ν (D i)).toReal := div_mul_cancel₀ _ hbne
      calc (ν (D i)).toReal * (- Real.log ((ν (D i)).toReal / b))
          = (((ν (D i)).toReal / b) * b) * (- Real.log ((ν (D i)).toReal / b)) := by rw [hp]
        _ = - ((ν (D i)).toReal / b) * Real.log ((ν (D i)).toReal / b) * b := by ring
        _ = Real.negMulLog ((ν (D i)).toReal / b) * b := by rw [Real.negMulLog]
    calc ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) * ν (D i)
        = ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) * ENNReal.ofReal ((ν (D i)).toReal) := by
            rw [hofx i]
      _ = ENNReal.ofReal ((ν (D i)).toReal) * ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) := by
            rw [mul_comm]
      _ = ENNReal.ofReal ((ν (D i)).toReal * (- Real.log ((ν (D i)).toReal / b))) := by
            rw [ENNReal.ofReal_mul (hxnn i)]
      _ = ENNReal.ofReal (Real.negMulLog ((ν (D i)).toReal / b) * b) := by rw [hkey]
      _ = ENNReal.ofReal (b * Real.negMulLog ((ν (D i)).toReal / b)) := by rw [mul_comm]
      _ = ENNReal.ofReal b * ENNReal.ofReal (Real.negMulLog ((ν (D i)).toReal / b)) := by
            rw [ENNReal.ofReal_mul hbnn]
  -- Pointwise (a.e.) lower bound on each piece.
  have hstep1 : ∀ i, ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) * ν (D i)
      ≤ ∫⁻ u in D i, Φ u ∂ν := by
    intro i
    have hm := MeasureTheory.lintegral_mono_ae (h i)
    rwa [MeasureTheory.setLIntegral_const] at hm
  -- The integral over `W` splits as the sum over the pieces.
  have hsplit : (∑ i, ∫⁻ u in D i, Φ u ∂ν) = ∫⁻ u in W, Φ u ∂ν := by
    rw [← hcov]
    rw [MeasureTheory.lintegral_iUnion hD hd Φ, tsum_fintype]
  -- Summing the termwise identities.
  have hsumid : (∑ i, ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) * ν (D i))
      = ENNReal.ofReal b * ENNReal.ofReal (∑ i, Real.negMulLog ((ν (D i)).toReal / b)) := by
    calc ∑ i, ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) * ν (D i)
        = ∑ i, ENNReal.ofReal b * ENNReal.ofReal (Real.negMulLog ((ν (D i)).toReal / b)) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
      _ = ENNReal.ofReal b * ∑ i, ENNReal.ofReal (Real.negMulLog ((ν (D i)).toReal / b)) := by
            rw [Finset.mul_sum]
      _ = ENNReal.ofReal b * ENNReal.ofReal (∑ i, Real.negMulLog ((ν (D i)).toReal / b)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.negMulLog_nonneg (hpi0 i) (hpi1 i))]
  -- Final assembly.
  have hbound : ENNReal.ofReal b * ENNReal.ofReal (∑ i, Real.negMulLog ((ν (D i)).toReal / b))
      ≤ ∫⁻ u in W, Φ u ∂ν := by
    rw [← hsumid]
    calc ∑ i, ENNReal.ofReal (- Real.log ((ν (D i)).toReal / b)) * ν (D i)
        ≤ ∑ i, ∫⁻ u in D i, Φ u ∂ν := Finset.sum_le_sum (fun i _ => hstep1 i)
      _ = ∫⁻ u in W, Φ u ∂ν := hsplit
  rw [ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWtop), ← hofb, mul_comm]
  exact hbound

end Work.EKLC6Core
