import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RamificationAudit

/-- **Clearing denominators in a valuation ring.**  Given finitely many nonzero elements `c i` of a
field `M` and a valuation subring `B` of `M`, there is `s ≠ 0` in `M` such that every `s * c i` lies
in `B` and at least one of them is a unit of `B` (equivalently, does not lie in the maximal ideal of
`B`; in terms of the valuation of `B`, `B.valuation (s * c i) = 1`).

Take `m` to be the maximum of the values `B.valuation (c i)` (attained at some `i₀`), i.e.
`m = Finset.univ.sup' _ fun i => B.valuation (c i)`, and `s` with `B.valuation s = m⁻¹`
(possible by `ValuationSubring.valuation_surjective`).  Then for each `i`,
`B.valuation (s * c i) = m⁻¹ * B.valuation (c i) ≤ 1`, i.e. `s * c i ∈ B` by
`ValuationSubring.valuation_le_one_iff`, and for `i₀` the value is `1`. -/
theorem exists_mul_mem_and_valuation_eq_one {M : Type*} [Field M] (B : ValuationSubring M)
    {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → M) (hc : ∀ i, c i ≠ 0) :
    ∃ s : M, s ≠ 0 ∧ (∀ i, s * c i ∈ B) ∧ ∃ i, B.valuation (s * c i) = 1 := by
  classical
  -- the valuations of the given elements, viewed in the value group of `B`
  let f : ι → B.ValueGroup := fun i => B.valuation (c i)
  -- nonzero elements have nonzero valuation
  have hf0 : ∀ i, f i ≠ 0 := fun i => (Valuation.ne_zero_iff B.valuation).2 (hc i)
  -- the maximum of the values
  let m : B.ValueGroup := Finset.univ.sup' Finset.univ_nonempty f
  have hm : m ≠ 0 := by
    obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    have h : m = f i0 := hi0
    rw [h]
    exact hf0 i0
  -- an element whose value is the inverse of the maximum
  obtain ⟨s, hs⟩ := B.valuation_surjective m⁻¹
  refine ⟨s, ?_, ?_, ?_⟩
  · -- `s ≠ 0`
    rintro rfl
    rw [Valuation.map_zero] at hs
    exact inv_ne_zero hm hs.symm
  · -- every `s * c i` lies in `B`
    intro i
    rw [← B.valuation_le_one_iff]
    rw [Valuation.map_mul, hs]
    calc m⁻¹ * f i ≤ m⁻¹ * m := mul_le_mul_right (Finset.le_sup' f (Finset.mem_univ i)) m⁻¹
      _ = 1 := inv_mul_cancel₀ hm
  · -- an index at which the value is exactly `1`
    obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    have h : m = f i0 := hi0
    refine ⟨i0, ?_⟩
    rw [Valuation.map_mul, hs]
    change m⁻¹ * f i0 = 1
    rw [← h]
    exact inv_mul_cancel₀ hm

end NK.RamificationAudit
