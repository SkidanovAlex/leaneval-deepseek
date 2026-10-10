import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.ValuationSubring.exists_separator_lt_one_of_pairwise_incomparable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

theorem exists_unit_at_index_nonunit_else {L : Type*} [Field L] {ι : Type*} [Fintype ι]
    (C : ι → ValuationSubring L) (hnt : ∀ i, C i ≠ ⊤)
    (hincomp : ∀ i j, i ≠ j → ¬ (C i ≤ C j)) (i : ι) :
    ∃ u ∈ (⨅ k, (C k).toSubring), u ∉ (C i).nonunits ∧ ∀ k, k ≠ i → u ∈ (C k).nonunits := by
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨τ, hτ1, hτ2⟩ :=
    exists_separator_lt_one_of_pairwise_incomparable C hnt hincomp i
  have hτne : τ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hτ1
    exact absurd hτ1 (not_lt_of_ge (zero_le_one : (0 : (C i).ValueGroup) ≤ 1))
  have hvi : (C i).valuation (1 + τ) = (C i).valuation τ :=
    Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_one]; exact hτ1)
  refine ⟨τ / (1 + τ), ?_, ?_, ?_⟩
  · rw [Subring.mem_iInf]
    intro k
    rw [ValuationSubring.mem_toSubring, ← ValuationSubring.valuation_le_one_iff, Valuation.map_div]
    by_cases hk : k = i
    · subst hk; rw [hvi, div_self (ne_of_gt (zero_lt_one.trans hτ1))]
    · rw [Valuation.map_one_add_of_lt _ (hτ2 k hk), div_one]
      exact le_of_lt (hτ2 k hk)
  · rw [ValuationSubring.mem_nonunits_iff, Valuation.map_div, hvi,
      div_self (ne_of_gt (zero_lt_one.trans hτ1))]
    exact lt_irrefl 1
  · intro k hk
    rw [ValuationSubring.mem_nonunits_iff, Valuation.map_div,
      Valuation.map_one_add_of_lt _ (hτ2 k hk), div_one]
    exact hτ2 k hk

end Commons.RingTheory.Valuation.ValuationSubring
