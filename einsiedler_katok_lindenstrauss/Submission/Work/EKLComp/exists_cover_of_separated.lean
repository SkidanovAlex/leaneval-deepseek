import Mathlib

namespace Work.EKLComp

theorem exists_cover_of_separated {X : Type*} [PseudoMetricSpace X] (S : Set X) {δ : ℝ} (hδ : 0 < δ)
    {A : ℝ} (hA : 0 < A)
    (hsep : ∀ F : Finset X, (F : Set X) ⊆ S →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ dist x y) → (F.card : ℝ) < A) :
    ∃ F : Finset X, (F : Set X) ⊆ S ∧ (F.card : ℝ) < A ∧ S ⊆ ⋃ a ∈ F, Metric.ball a δ := by
  classical
  have hApos : (0 : ℝ) < A := hA
  -- The family of δ-separated subsets of `S`.
  have hchain : ∀ c ⊆ {T : Set X | T ⊆ S ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y},
      IsChain (· ⊆ ·) c →
      ∃ ub ∈ {T : Set X | T ⊆ S ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y},
        ∀ s ∈ c, s ⊆ ub := by
    intro c hcsub hchain
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Set.mem_sUnion.1 hx with ⟨s, hsc, hxs⟩
      exact (hcsub hsc).1 hxs
    · intro x hx y hy hxy
      rcases Set.mem_sUnion.1 hx with ⟨s, hsc, hxs⟩
      rcases Set.mem_sUnion.1 hy with ⟨t, htc, hyt⟩
      rcases eq_or_ne s t with rfl | hst
      · exact (hcsub hsc).2 x hxs y hyt hxy
      · rcases hchain hsc htc hst with hsub | hsub
        · exact (hcsub htc).2 x (hsub hxs) y hyt hxy
        · exact (hcsub hsc).2 x hxs y (hsub hyt) hxy
  -- Zorn: a maximal δ-separated subset of `S`.
  obtain ⟨M, hMmax⟩ := zorn_subset {T : Set X | T ⊆ S ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y} hchain
  have hMgood : M ⊆ S ∧ ∀ x ∈ M, ∀ y ∈ M, x ≠ y → δ ≤ dist x y := hMmax.1
  -- A maximal separated set covers `S` by δ-balls.
  have hcover : ∀ x ∈ S, ∃ a ∈ M, dist x a < δ := by
    intro x hxS
    by_contra hcon
    have hle : ∀ a ∈ M, δ ≤ dist x a := by
      intro a ha
      by_contra hlt
      exact hcon ⟨a, ha, lt_of_not_ge hlt⟩
    have hInsertGood : insert x M ⊆ S ∧ ∀ u ∈ insert x M, ∀ v ∈ insert x M, u ≠ v → δ ≤ dist u v := by
      refine ⟨?_, ?_⟩
      · intro u hu
        rcases Set.mem_insert_iff.1 hu with h | hu
        · rw [h]; exact hxS
        · exact hMgood.1 hu
      · intro u hu v hv huv
        rcases Set.mem_insert_iff.1 hu with h | hu
        · rw [h]
          rcases Set.mem_insert_iff.1 hv with h' | hv
          · exact absurd (h.trans h'.symm) huv
          · exact hle v hv
        · rcases Set.mem_insert_iff.1 hv with h' | hv
          · rw [h', dist_comm]; exact hle u hu
          · exact hMgood.2 u hu v hv huv
    have hsub' : insert x M ⊆ M :=
      hMmax.2 (y := insert x M) ⟨hInsertGood.1, hInsertGood.2⟩ (Set.subset_insert x M)
    have hxM : x ∈ M := hsub' (Set.mem_insert x M)
    have : δ ≤ dist x x := hle x hxM
    rw [dist_self] at this
    linarith
  -- The packing bound forces `M` to be finite.
  have hMfin : M.Finite := by
    by_contra hfin
    have hMinf : M.Infinite := Set.not_finite.mp hfin
    obtain ⟨n, hn⟩ := exists_nat_ge A
    obtain ⟨T, hTsub, hTcard⟩ := hMinf.exists_subset_card_eq n
    have hTsubS : (T : Set X) ⊆ S := fun x hx => hMgood.1 (hTsub hx)
    have hTsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y :=
      fun x hx y hy hxy => hMgood.2 x (hTsub hx) y (hTsub hy) hxy
    have hlt : (T.card : ℝ) < A := hsep T hTsubS hTsep
    rw [hTcard] at hlt
    linarith
  refine ⟨hMfin.toFinset, ?_, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset hMfin]; exact hMgood.1
  · have hFsep : ∀ x ∈ hMfin.toFinset, ∀ y ∈ hMfin.toFinset, x ≠ y → δ ≤ dist x y := by
      intro x hx y hy hxy
      exact hMgood.2 x ((Set.Finite.mem_toFinset hMfin).1 hx) y ((Set.Finite.mem_toFinset hMfin).1 hy) hxy
    exact hsep hMfin.toFinset (by rw [Set.Finite.coe_toFinset hMfin]; exact hMgood.1) hFsep
  · intro x hx
    obtain ⟨a, haM, hd⟩ := hcover x hx
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact (Set.Finite.mem_toFinset hMfin).2 haM
    · exact Metric.mem_ball.2 hd

end Work.EKLComp
