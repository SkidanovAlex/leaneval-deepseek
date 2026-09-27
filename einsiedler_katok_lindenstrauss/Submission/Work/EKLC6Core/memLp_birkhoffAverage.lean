import Mathlib

/-!
# Birkhoff averages of `L²` functions are `L²`

Let `T : X → X` be measure preserving for a measure `μ`, and let `f ∈ L²(μ)` be real valued.
The `n`-th Birkhoff average of `f` along `T`,
`birkhoffAverage ℝ T f n = (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, f ∘ T^[k]`,
is again in `L²(μ)`: each of the finitely many summands `f ∘ T^[k]` is `MemLp` because
`T^[k]` is measure preserving (`MeasureTheory.MemLp.comp_measurePreserving`), a finite sum of
`MemLp` functions is `MemLp` (`MeasureTheory.memLp_finsetSum`), and `MemLp` is closed under
scalar multiplication (`MeasureTheory.MemLp.const_smul`).
-/

namespace Work.EKLC6Core

open MeasureTheory

/-- The `n`-th Birkhoff sum of an `Lᵖ` function along a measure preserving map is `Lᵖ`. -/
lemma memLp_birkhoffSum {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (f : X → ℝ) {p : ENNReal} (hf : MeasureTheory.MemLp f p μ) (n : ℕ) :
    MeasureTheory.MemLp (birkhoffSum T f n) p μ := by
  change MeasureTheory.MemLp (fun x => ∑ k ∈ Finset.range n, f (T^[k] x)) p μ
  exact MeasureTheory.memLp_finsetSum (Finset.range n)
    (fun k _ => hf.comp_measurePreserving (hmp.iterate k))

theorem memLp_birkhoffAverage {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ] (T : X → X)
    (hmp : MeasureTheory.MeasurePreserving T μ μ) (f : X → ℝ) (hf : MeasureTheory.MemLp f 2 μ)
    (n : ℕ) : MeasureTheory.MemLp (birkhoffAverage ℝ T f n) 2 μ := by
  have hsmul := (memLp_birkhoffSum μ T hmp f hf n).const_smul ((n : ℝ)⁻¹)
  refine MeasureTheory.MemLp.ae_eq ?_ hsmul
  filter_upwards with x
  simp [birkhoffAverage, Pi.smul_apply]

end Work.EKLC6Core
