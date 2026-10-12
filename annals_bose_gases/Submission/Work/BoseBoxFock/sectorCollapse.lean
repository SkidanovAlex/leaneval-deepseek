import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sectorSlotLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sectorCollapse` — the slot-sum collapse for arbitrary "spectator-free" states

`Work.BoseBoxFock.boxSlotSum_sector_eq_sum_mem` proves that on the `S`-sector
`slotExact e S Φ` the one-body slot sum `boxSlotSum e T` collapses to the sum over the *occupied*
slots `j ∈ S` (every `j ∉ S` term vanishes because the `j`-slot of a sector state carries no
`V`-component, `slotProj1 e j (slotExact e S Φ) = 0`).

That statement is stated for the sector state itself, but its proof only uses the *vanishing of
the slot projections* outside `S` and the regularity of the state.  This file records the
general form, which is what an **iterated** slot sum needs: for the composite
`boxSlotSum e T₁ (boxSlotSum e T₂ (slotExact e S Φ))` the inner result is *not* again a sector
state, but it still has no `V`-component in the slots outside `S` (the `j ∈ S` slot operators do
not touch the other slots), so the outer collapse applies to it.  Consequently the pointwise
decoupling (`Work.BoseBoxFock.boxSlotSum_pairCoord`) iterates, i.e. the composite of two one-body
rows (the shape of the `n₀ n₊` and `L₀ ∘ a_k†a_k ∘ a₀` rows of `H2ndF`) decouples over the
complement configuration in the same way as a single one.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- **The slot sum collapses to `S` whenever the state has no `V`-component outside `S`.**
This is `Work.BoseBoxFock.boxSlotSum_sector_eq_sum_mem` with the hypothesis
`Θ = slotExact e S Φ` replaced by `∀ j ∉ S, slotProj1 e j Θ = 0` — exactly what its proof uses
(`Work.BoseBoxFock.boxSlotOf_eq_zero_of_slotProj1_eq_zero` needs no more). -/
theorem boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero {m n : ℕ}
    (e : Fin m → Ω → ℂ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (S : Finset (Fin n)) (Θ : (Fin n → Ω) → ℂ)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (hint : ∀ k k', MeasureTheory.Integrable (fun z : Ω => star (e k z) * e k' z))
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (hΘ0 : ∀ j : Fin n, j ∉ S → slotProj1 e j Θ = 0) :
    Work.BoseDict.boxSlotSum e T Θ
      = ∑ j ∈ S, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  classical
  have hzero : ∀ j : Fin n, j ∉ S →
      (∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) = 0 := by
    intro j hj
    refine Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun l' _ => ?_))
    rw [boxSlotOf_eq_zero_of_slotProj1_eq_zero e l l' j he hec horth hint Θ hΘm hΘb (hΘ0 j hj)]
    exact smul_zero _
  rw [Work.BoseDict.boxSlotSum]
  exact (Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hzero j hj)).symm

end Work.BoseBoxFock
