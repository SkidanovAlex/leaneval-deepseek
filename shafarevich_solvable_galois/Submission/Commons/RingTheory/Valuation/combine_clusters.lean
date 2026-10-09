import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_valuation_sub_lt_of_pairwise_independent
import Submission.Commons.RingTheory.Valuation.ValuationSubring.le_iff_forall_valuation_lt_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

/-- **Combining local solutions on independent clusters.**

Let `C : ι → ValuationSubring F` be a finite family of valuation subrings, grouped into clusters by
a map `f : ι → σ`, in such a way that each `C i` is contained in the valuation subring `E (f i)`,
where the `E s` are pairwise independent (`E s ⊔ E t = ⊤` for `s ≠ t`) and proper (`E s ≠ ⊤`).
Given for every cluster `s` an element `x s` that already satisfies the "`z i`-closeness"
conditions for all indices `i` of that cluster, there is a single element `x0` satisfying all the
conditions simultaneously.

The point is that depth at the coarse valuation `E (f i)` transfers to depth at the fine valuation
`C i`, and the `E s` are independent, so the local solutions can be glued. -/
theorem combine_clusters {F : Type*} [Field F] {ι σ : Type*} [Fintype ι] [Fintype σ] [Nonempty σ]
    (C : ι → ValuationSubring F) (f : ι → σ) (E : σ → ValuationSubring F)
    (a z : ι → F) (hz : ∀ i, z i ≠ 0)
    (hle : ∀ i, C i ≤ E (f i))
    (hind : ∀ s t, s ≠ t → E s ⊔ E t = ⊤)
    (hne : ∀ s, E s ≠ ⊤)
    (x : σ → F) (hx : ∀ s, ∀ i, f i = s → (C i).valuation (x s - a i) < (C i).valuation (z i)) :
    ∃ x0 : F, ∀ i, (C i).valuation (x0 - a i) < (C i).valuation (z i) := by
  classical
  -- A per-index comparison element: `x (f i) - a i`, or `z i` when the former vanishes.
  let c : ι → F := fun i => if x (f i) = a i then z i else x (f i) - a i
  have hcne : ∀ i, c i ≠ 0 := by
    intro i
    simp only [c]
    split_ifs with h
    · exact hz i
    · exact sub_ne_zero.mpr h
  -- The cluster of an index `s`.
  let cl : σ → Finset ι := fun s => Finset.univ.filter (fun i => f i = s)
  -- Deep thresholds at the coarse valuations `E s`.
  let γ : (s : σ) → (E s).ValueGroup := fun s =>
    if h : (cl s).Nonempty then
      ((cl s).image (fun i => (E s).valuation (c i))).min'
        (h.image (fun i => (E s).valuation (c i)))
    else 1
  have hγpos : ∀ s, 0 < γ s := by
    intro s
    by_cases h : (cl s).Nonempty
    · have hdef : γ s = ((cl s).image (fun i => (E s).valuation (c i))).min'
          (h.image (fun i => (E s).valuation (c i))) := by
        simp only [γ]; exact dif_pos h
      rw [hdef]
      obtain ⟨i, _, hiv⟩ :=
        Finset.mem_image.mp (Finset.min'_mem ((cl s).image (fun i => (E s).valuation (c i))) _)
      rw [← hiv]
      exact (Valuation.pos_iff _).mpr (hcne i)
    · have hdef : γ s = 1 := by simp only [γ]; exact dif_neg h
      rw [hdef]; exact zero_lt_one
  have hγle : ∀ s i, f i = s → γ s ≤ (E s).valuation (c i) := by
    intro s i hfi
    have hi : i ∈ cl s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hfi⟩
    have hnecl : (cl s).Nonempty := ⟨i, hi⟩
    have hdef : γ s = ((cl s).image (fun i => (E s).valuation (c i))).min'
        (hnecl.image (fun i => (E s).valuation (c i))) := by
      simp only [γ]; exact dif_pos hnecl
    rw [hdef]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  -- Glue the local solutions at the level of the independent `E s`.
  obtain ⟨x0, hx0⟩ :=
    Commons.RingTheory.Valuation.exists_valuation_sub_lt_of_pairwise_independent E hne hind x γ hγpos
  refine ⟨x0, fun i => ?_⟩
  have hbound : (E (f i)).valuation (x0 - x (f i)) < (E (f i)).valuation (c i) :=
    lt_of_lt_of_le (hx0 (f i)) (hγle (f i) i rfl)
  -- Transfer the depth from `E (f i)` down to the finer `C i`.
  have hC : (C i).valuation (x0 - x (f i)) < (C i).valuation (c i) := by
    have hdiv : (E (f i)).valuation ((x0 - x (f i)) / c i) < 1 := by
      rw [Valuation.map_div]
      exact (div_lt_one₀ ((Valuation.pos_iff _).mpr (hcne i))).mpr hbound
    have hlt1 : (C i).valuation ((x0 - x (f i)) / c i) < 1 :=
      (ValuationSubring.le_iff_forall_valuation_lt_one (C i) (E (f i))).mp (hle i) _ hdiv
    rw [Valuation.map_div] at hlt1
    exact (div_lt_one₀ ((Valuation.pos_iff _).mpr (hcne i))).mp hlt1
  by_cases h : x (f i) = a i
  · have hc : c i = z i := by simp only [c]; rw [if_pos h]
    rw [hc] at hC
    rw [← h]
    exact hC
  · have hc : c i = x (f i) - a i := by simp only [c]; rw [if_neg h]
    rw [hc] at hC
    have heq : (C i).valuation (x0 - a i) = (C i).valuation (x (f i) - a i) := by
      have hxy : x0 - a i = (x0 - x (f i)) + (x (f i) - a i) := by ring
      rw [hxy]
      exact Valuation.map_add_eq_of_lt_right _ hC
    rw [heq]
    exact hx (f i) i rfl

end Commons.RingTheory.Valuation
