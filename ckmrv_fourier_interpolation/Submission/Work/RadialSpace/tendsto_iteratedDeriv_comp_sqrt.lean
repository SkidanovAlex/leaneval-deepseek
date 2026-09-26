import Mathlib
import Submission.Work.RadialSpace.EvenHalfDeriv
import Submission.Work.RadialSpace.iteratedDeriv_comp_sqrt

/-!
# The one-sided limit at `0` of the iterated derivatives of `s ↦ g (√s)`

For an even smooth function `g : ℝ → ℂ` the iterated derivative
`iteratedDeriv m (fun s => g (√s))` has, as `s → 0⁺`, the limit
`(evenHalfDeriv^[m] g) 0`: on `s > 0` the function equals
`(evenHalfDeriv^[m] g) (√s)` (`iteratedDeriv_comp_sqrt`), and the latter tends
to `(evenHalfDeriv^[m] g) 0` because `evenHalfDeriv^[m] g` is smooth, hence
continuous, and `√s → 0` as `s → 0⁺`.

## Main results

* `Work.RadialSpace.tendsto_iteratedDeriv_comp_sqrt`
-/

open Filter Topology
open scoped ContDiff

namespace Work.RadialSpace

/-- As `s → 0⁺`, the `m`-th derivative of `s ↦ g (√s)` tends to the value at
`0` of the `m`-fold half-derivative of `g`. -/
theorem tendsto_iteratedDeriv_comp_sqrt {g : ℝ → ℂ} (hg : ContDiff ℝ Work.RadialSpace.Smooth g)
    (he : Function.Even g) (m : ℕ) : Filter.Tendsto (iteratedDeriv m fun s => g (Real.sqrt s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((Work.RadialSpace.evenHalfDeriv^[m]) g 0)) := by
  -- `√s → 0` as `s → 0⁺`.
  have hsqrt : Filter.Tendsto (fun s : ℝ => Real.sqrt s)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun x : ℝ => Real.sqrt x) (nhds 0) (nhds 0) := by
      simpa [Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt (x := 0)).tendsto
    exact h0.mono_left nhdsWithin_le_nhds
  -- `evenHalfDeriv^[m] g` is smooth, hence continuous.
  have hcont : Continuous ((evenHalfDeriv^[m]) g) :=
    (contDiff_iterate_evenHalfDeriv hg m).continuous
  have hlim : Filter.Tendsto (fun s : ℝ => (evenHalfDeriv^[m]) g (Real.sqrt s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((evenHalfDeriv^[m]) g 0)) := by
    simpa only [Function.comp_def] using hcont.continuousAt.tendsto.comp hsqrt
  -- On `s > 0` the two functions agree.
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (iteratedDeriv_comp_sqrt hg he hs m).symm

end Work.RadialSpace
