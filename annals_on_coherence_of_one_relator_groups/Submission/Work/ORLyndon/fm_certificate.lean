import Mathlib

namespace Work.ORLyndon

theorem fm_certificate {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι]
    (a : ι → κ → ℚ) (k : κ)
    (w : {i : ι // a i k = 0} ⊕ {p : ι × ι // 0 < a p.1 k ∧ a p.2 k < 0} → ℚ)
    (hw : ∀ e, 0 ≤ w e) (hne : w ≠ 0)
    (hsum : ∀ j : {j : κ // j ≠ k},
      (∑ e, w e * (match e with
        | Sum.inl i => a i.1 j.1
        | Sum.inr p => a p.1.1 k * a p.1.2 j.1 - a p.1.2 k * a p.1.1 j.1)) = 0) :
    ∃ ν : ι → ℚ, (∀ i, 0 ≤ ν i) ∧ ν ≠ 0 ∧ (∀ j : κ, ∑ i, ν i * a i j = 0) := by
  classical
  -- The candidate nonnegative kernel vector: the row-coefficient of index `m` in
  --   ν = ∑_{i ∈ Z} w_i e_i + ∑_{(p,q)} w_{pq} (a_{pk} e_q - a_{qk} e_p)
  -- where `Z = {i | a i k = 0}` and the pairs `(p,q)` have `a pk > 0`, `a qk < 0`.
  let g : ({i : ι // a i k = 0} ⊕ {p : ι × ι // 0 < a p.1 k ∧ a p.2 k < 0}) → ι → ℚ :=
    fun e m => match e with
      | Sum.inl i => if i.1 = m then 1 else 0
      | Sum.inr p => (if p.1.2 = m then a p.1.1 k else 0) - (if p.1.1 = m then a p.1.2 k else 0)
  have hg_inl : ∀ (i : {i : ι // a i k = 0}) (m : ι),
      g (Sum.inl i) m = if i.1 = m then (1 : ℚ) else 0 := fun i m => rfl
  have hg_inr : ∀ (p : {p : ι × ι // 0 < a p.1 k ∧ a p.2 k < 0}) (m : ι),
      g (Sum.inr p) m = (if p.1.2 = m then a p.1.1 k else 0)
        - (if p.1.1 = m then a p.1.2 k else 0) := fun p m => rfl
  -- Every coefficient is nonnegative: `g e m ≥ 0`.
  have hg_nonneg : ∀ e m, 0 ≤ g e m := by
    rintro (i | p) m
    · change 0 ≤ (if i.1 = m then (1 : ℚ) else 0)
      split_ifs <;> norm_num
    · change 0 ≤ (if p.1.2 = m then a p.1.1 k else 0) - (if p.1.1 = m then a p.1.2 k else 0)
      split_ifs <;> linarith [p.2.1, p.2.2]
  -- Summing `g e m * a m j` over `m` recovers exactly the coefficient of `w e`
  -- that appears in the hypothesis `hsum`.
  have hg_sum : ∀ (e : ({i : ι // a i k = 0} ⊕ {p : ι × ι // 0 < a p.1 k ∧ a p.2 k < 0}))
      (j : κ),
      ∑ m, g e m * a m j = (match e with
        | Sum.inl i => a i.1 j
        | Sum.inr p => a p.1.1 k * a p.1.2 j - a p.1.2 k * a p.1.1 j) := by
    rintro (i | p) j
    · change ∑ m, (if i.1 = m then (1 : ℚ) else 0) * a m j = a i.1 j
      rw [Finset.sum_eq_single i.1]
      · simp
      · intro b _ hb
        rw [if_neg (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · change ∑ m, ((if p.1.2 = m then a p.1.1 k else 0)
          - (if p.1.1 = m then a p.1.2 k else 0)) * a m j
        = a p.1.1 k * a p.1.2 j - a p.1.2 k * a p.1.1 j
      have hstep : ∀ m : ι, ((if p.1.2 = m then a p.1.1 k else 0)
            - (if p.1.1 = m then a p.1.2 k else 0)) * a m j
          = (if p.1.2 = m then a p.1.1 k * a m j else 0)
            - (if p.1.1 = m then a p.1.2 k * a m j else 0) := by
        intro m
        by_cases hA : p.1.2 = m <;> by_cases hB : p.1.1 = m <;> simp [hA, hB]
      simp only [hstep, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  let ν : ι → ℚ := fun m => ∑ e, w e * g e m
  -- Column sums of `ν` are the `hsum` combination.
  have key : ∀ j : κ, ∑ i, ν i * a i j = ∑ e, w e * (match e with
        | Sum.inl i => a i.1 j
        | Sum.inr p => a p.1.1 k * a p.1.2 j - a p.1.2 k * a p.1.1 j) := by
    intro j
    calc ∑ i, ν i * a i j
        = ∑ i, ∑ e, (w e * g e i) * a i j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [show ν i = ∑ e, w e * g e i from rfl, Finset.sum_mul]
        _ = ∑ e, ∑ i, (w e * g e i) * a i j := by rw [Finset.sum_comm]
        _ = ∑ e, ∑ i, w e * (g e i * a i j) := by
            apply Finset.sum_congr rfl; intro e _
            apply Finset.sum_congr rfl; intro i _
            ring
        _ = ∑ e, w e * ∑ i, g e i * a i j := by
            apply Finset.sum_congr rfl; intro e _
            rw [Finset.mul_sum]
        _ = ∑ e, w e * (match e with
              | Sum.inl i => a i.1 j
              | Sum.inr p => a p.1.1 k * a p.1.2 j - a p.1.2 k * a p.1.1 j) := by
            apply Finset.sum_congr rfl; intro e _
            rw [hg_sum e j]
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro m
    show 0 ≤ ∑ e, w e * g e m
    apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (hw e) (hg_nonneg e m)
  · intro hν0
    -- `w ≠ 0` with `w ≥ 0` gives some `e0` with `0 < w e0`.
    obtain ⟨e0, he0⟩ : ∃ e, w e ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hne (funext h)
    have hpos : 0 < w e0 := lt_of_le_of_ne (hw e0) (Ne.symm he0)
    have h0m : ∀ m, ν m = 0 := fun m => by
      have := congrFun hν0 m; simpa using this
    rcases e0 with i | p
    · have hνi : 0 < ν i.1 := by
        show 0 < ∑ e, w e * g e i.1
        apply Finset.sum_pos'
        · intro e _; exact mul_nonneg (hw e) (hg_nonneg e i.1)
        · refine ⟨Sum.inl i, Finset.mem_univ _, ?_⟩
          show 0 < w (Sum.inl i) * g (Sum.inl i) i.1
          rw [hg_inl i i.1, if_pos rfl, mul_one]
          exact hpos
      rw [h0m i.1] at hνi
      exact lt_irrefl 0 hνi
    · have hνp : 0 < ν p.1.1 := by
        show 0 < ∑ e, w e * g e p.1.1
        apply Finset.sum_pos'
        · intro e _; exact mul_nonneg (hw e) (hg_nonneg e p.1.1)
        · refine ⟨Sum.inr p, Finset.mem_univ _, ?_⟩
          show 0 < w (Sum.inr p) * g (Sum.inr p) p.1.1
          have hne₂ : p.1.2 ≠ p.1.1 := by
            intro h
            have hp2 := p.2.2
            rw [h] at hp2
            linarith [p.2.1, hp2]
          rw [hg_inr p p.1.1, if_neg hne₂, if_pos rfl, zero_sub]
          exact mul_pos hpos (by linarith [p.2.2])
      rw [h0m p.1.1] at hνp
      exact lt_irrefl 0 hνp
  · intro j
    rw [key j]
    by_cases hjk : j = k
    · rw [hjk]
      -- For the column `k` every coefficient vanishes: `a_{ik} = 0` for `i ∈ Z`,
      -- and the pair terms cancel.
      apply Finset.sum_eq_zero
      intro e _
      rcases e with i | p
      · show w (Sum.inl i) * a i.1 k = 0
        rw [i.2, mul_zero]
      · show w (Sum.inr p) * (a p.1.1 k * a p.1.2 k - a p.1.2 k * a p.1.1 k) = 0
        ring
    · exact hsum ⟨j, hjk⟩

end Work.ORLyndon
