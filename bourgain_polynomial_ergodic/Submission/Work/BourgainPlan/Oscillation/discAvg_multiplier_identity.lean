import Mathlib
import Submission.Work.BourgainPlan.Oscillation.defs

/-!
# The density kernel as a multiplier on the sampled sequence

The polynomial density kernel `k_N(j) = (1/N) · #{i < N : P(i) = j}` (as a real number,
viewed in `ℂ`) turns the *sampled* sequence `i ↦ z(P(i))` into the averaged sequence

  `∑_j k_N(j) · z(j) = (1/N) · ∑_{i<N} z(P(i))`.

This is the discrete form of the identity `∑_j k_N(j) e^{i j θ} = (1/N) ∑_{i<N} e^{i P(i) θ}`
used to read the polynomial average as a Fourier multiplier in Bourgain's argument.
-/

open Finset
open scoped BigOperators

namespace Work.BourgainPlan.Oscillation

/-- The complex version of `Submission.sum_card_filter_mul`: summing a function against the
cardinalities of the fibres of `i ↦ (P.eval i).toNat` over `i < N` reproduces the sum of the
composed function.  Identical combinatorial content; we need it in `ℂ` for the multiplier
identity below. -/
theorem sum_card_filter_mul_complex (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℂ) :
    (∑ j ∈ Finset.range (Submission.polySupport P N),
        (((Finset.range N).filter (fun i : ℕ => (P.eval (i : ℤ)).toNat = j)).card : ℂ) * g j)
      = ∑ i ∈ Finset.range N, g ((P.eval (i : ℤ)).toNat) := by
  have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.range N)
      (t := Finset.range (Submission.polySupport P N))
      (g := fun i : ℕ => (P.eval (i : ℤ)).toNat)
      (fun i hi => Finset.mem_range.mpr (Submission.polySupport_spec P N i hi))
      (fun i => g ((P.eval (i : ℤ)).toNat))
  rw [← hfib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  rw [Finset.sum_const, nsmul_eq_mul]

theorem discAvg_multiplier_identity (P : Polynomial ℤ) (N : ℕ) (z : ℕ → ℂ) :
    (∑ j ∈ Finset.range (Submission.polySupport P N),
        Submission.polyKernel P N j * z j)
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, z ((P.eval (i : ℤ)).toNat) := by
  rw [show (∑ j ∈ Finset.range (Submission.polySupport P N),
        Submission.polyKernel P N j * z j)
      = ∑ j ∈ Finset.range (Submission.polySupport P N),
          (N : ℂ)⁻¹ * (((((Finset.range N).filter
            (fun i : ℕ => (P.eval (i : ℤ)).toNat = j)).card : ℕ) : ℂ) * z j) from
      Finset.sum_congr rfl (fun j _ => by unfold Submission.polyKernel; push_cast; ring)]
  rw [← Finset.mul_sum]
  rw [sum_card_filter_mul_complex]

end Work.BourgainPlan.Oscillation
