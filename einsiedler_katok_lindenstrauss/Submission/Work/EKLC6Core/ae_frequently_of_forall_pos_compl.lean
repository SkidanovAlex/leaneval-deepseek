import Mathlib
import Submission.Work.EKLC6Core.ae_frequently_of_conull_iUnion

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped Classical

/-- **Lemma.** If `T` preserves the probability measure `μ` and `(A k)` is a sequence of
measurable sets whose complements have arbitrarily small measure, then for `μ`-a.e. `x` there is
some single `k` for which the `T`-orbit of `x` visits `A k` infinitely often.

The proof is the same "bad set" argument as in `ae_frequently_of_conull_iUnion`, but the
hypothesis `h0` replaces monotonicity plus conullity of the union: the bad set
`bad = ⋂ k, {x | T^[n] x ∈ (A k)ᶜ eventually}` satisfies `μ bad ≤ μ ((A k)ᶜ)` for every `k` by
`measure_eventually_mem_le`; choosing `k` with `μ ((A k)ᶜ) < μ bad` (possible by `h0` whenever
`μ bad > 0`) is a contradiction. -/
theorem ae_frequently_of_forall_pos_compl {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasureTheory.MeasurePreserving T μ μ) {A : ℕ → Set X}
    (hA : ∀ k, MeasurableSet (A k))
    (h0 : ∀ ε : ENNReal, 0 < ε → ∃ k, μ ((A k)ᶜ) < ε) :
    ∀ᵐ x ∂μ, ∃ k : ℕ, ∃ᶠ n in Filter.atTop, T^[n] x ∈ A k := by
  rw [MeasureTheory.ae_iff]
  set bad : Set X := ⋂ k, {x | ∀ᶠ n in atTop, T^[n] x ∈ (A k)ᶜ} with hbaddef
  have hgoal_eq : {x | ¬ ∃ k, ∃ᶠ n in Filter.atTop, T^[n] x ∈ A k} = bad := by
    rw [hbaddef]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, not_exists,
      Filter.not_frequently]
  rw [hgoal_eq]
  have hbound : ∀ k, μ bad ≤ μ ((A k)ᶜ) := by
    intro k
    rw [hbaddef]
    exact le_trans (measure_mono (Set.iInter_subset _ k))
      (measure_eventually_mem_le hT (hA k).compl)
  refine le_antisymm ?_ zero_le
  by_contra h
  rw [not_le] at h
  obtain ⟨k, hk⟩ := h0 (μ bad) h
  exact absurd (lt_of_le_of_lt (hbound k) hk) (lt_irrefl (μ bad))

end Work.EKLC6Core
