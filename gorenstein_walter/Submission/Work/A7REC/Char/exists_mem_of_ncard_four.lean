import Mathlib

namespace Work.A7REC.Char

/-- In a subgroup of cardinality `3`, any nonidentity element `y` together with `1` and `y ^ 2`
already exhausts the subgroup. -/
private lemma subgroup_eq_of_card_three {G : Type*} [Group G] {W : Subgroup G}
    (hW : Nat.card W = 3) {y : G} (hy : y ∈ W) (hy1 : y ≠ 1) :
    (W : Set G) = ({1, y, y ^ 2} : Set G) := by
  have hy3 : y ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := W) (x := (⟨y, hy⟩ : W))
    rw [hW] at h
    simpa using congrArg Subtype.val h
  have hyy2 : y ≠ y ^ 2 := by
    intro h
    have h1 : (1 : G) = y := by
      have := congrArg (fun z => y⁻¹ * z) h
      simpa [pow_two, mul_assoc] using this
    exact hy1 h1.symm
  have hy2ne1 : y ^ 2 ≠ 1 := by
    intro h2
    have hy3y : y ^ 3 = y := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul]
    exact hy1 (hy3y.symm.trans hy3)
  have hWfty : Finite W := (Nat.card_ne_zero.mp (by rw [hW]; norm_num)).2
  have hWfin : (W : Set G).Finite := Set.finite_coe_iff.mpr hWfty
  have hWn : (W : Set G).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hW
  have hsub : ({1, y, y ^ 2} : Set G) ⊆ (W : Set G) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact W.one_mem
    · exact hy
    · exact W.pow_mem hy 2
  have hcard : ({1, y, y ^ 2} : Set G).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, y, y ^ 2, Ne.symm hy1, hy2ne1.symm, hyy2, rfl⟩
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hWn, hcard]) hWfin).symm

/-- Two distinct subgroups of cardinality `3` have no nonidentity element in common. -/
private lemma disjoint_sdiff_of_card_three {G : Type*} [Group G] {W₁ W₂ : Subgroup G}
    (h₁ : Nat.card W₁ = 3) (h₂ : Nat.card W₂ = 3) (hne : W₁ ≠ W₂) :
    Disjoint ((W₁ : Set G) \ {1}) ((W₂ : Set G) \ {1}) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  obtain ⟨hyW1, hyne⟩ := hy1
  obtain ⟨hyW2, _⟩ := hy2
  have e1 : (W₁ : Set G) = ({1, y, y ^ 2} : Set G) := subgroup_eq_of_card_three h₁ hyW1 hyne
  have e2 : (W₂ : Set G) = ({1, y, y ^ 2} : Set G) := subgroup_eq_of_card_three h₂ hyW2 hyne
  exact hne (SetLike.coe_injective (e1.trans e2.symm))

theorem exists_mem_of_ncard_four {G : Type*} [Group G] {R : Subgroup G} {Ω : Set (Subgroup G)}
    (hR : Nat.card R = 9) (hsub : ∀ W ∈ Ω, W ≤ R ∧ Nat.card W = 3) (hΩ : Ω.ncard = 4) :
    ∀ x ∈ R, x ≠ 1 → ∃ W ∈ Ω, x ∈ W := by
  intro x hxR hxne
  -- `Ω` consists of exactly four subgroups of order three.
  obtain ⟨W1, W2, W3, W4, hW12, hW13, hW14, hW23, hW24, hW34, hΩeq⟩ :=
    Set.ncard_eq_four.mp hΩ
  have hm1 : W1 ∈ Ω := by rw [hΩeq]; simp
  have hm2 : W2 ∈ Ω := by rw [hΩeq]; simp
  have hm3 : W3 ∈ Ω := by rw [hΩeq]; simp
  have hm4 : W4 ∈ Ω := by rw [hΩeq]; simp
  have hc1 : Nat.card W1 = 3 := (hsub W1 hm1).2
  have hc2 : Nat.card W2 = 3 := (hsub W2 hm2).2
  have hc3 : Nat.card W3 = 3 := (hsub W3 hm3).2
  have hc4 : Nat.card W4 = 3 := (hsub W4 hm4).2
  -- Finiteness and cardinality bookkeeping.
  have hRfty : Finite R := (Nat.card_ne_zero.mp (by rw [hR]; norm_num)).2
  have hRfin : (R : Set G).Finite := Set.finite_coe_iff.mpr hRfty
  have hRn : (R : Set G).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hR
  have hf1 : (W1 : Set G).Finite := by
    have : Finite W1 := (Nat.card_ne_zero.mp (by rw [hc1]; norm_num)).2
    exact Set.finite_coe_iff.mpr this
  have hf2 : (W2 : Set G).Finite := by
    have : Finite W2 := (Nat.card_ne_zero.mp (by rw [hc2]; norm_num)).2
    exact Set.finite_coe_iff.mpr this
  have hf3 : (W3 : Set G).Finite := by
    have : Finite W3 := (Nat.card_ne_zero.mp (by rw [hc3]; norm_num)).2
    exact Set.finite_coe_iff.mpr this
  have hf4 : (W4 : Set G).Finite := by
    have : Finite W4 := (Nat.card_ne_zero.mp (by rw [hc4]; norm_num)).2
    exact Set.finite_coe_iff.mpr this
  have hn1 : (W1 : Set G).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hc1
  have hn2 : (W2 : Set G).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hc2
  have hn3 : (W3 : Set G).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hc3
  have hn4 : (W4 : Set G).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hc4
  -- The nonidentity parts of the four subgroups.
  set A1 : Set G := (W1 : Set G) \ {1} with hA1
  set A2 : Set G := (W2 : Set G) \ {1} with hA2
  set A3 : Set G := (W3 : Set G) \ {1} with hA3
  set A4 : Set G := (W4 : Set G) \ {1} with hA4
  have hA1n : A1.ncard = 2 := by rw [hA1, Set.ncard_sdiff_singleton_of_mem W1.one_mem, hn1]
  have hA2n : A2.ncard = 2 := by rw [hA2, Set.ncard_sdiff_singleton_of_mem W2.one_mem, hn2]
  have hA3n : A3.ncard = 2 := by rw [hA3, Set.ncard_sdiff_singleton_of_mem W3.one_mem, hn3]
  have hA4n : A4.ncard = 2 := by rw [hA4, Set.ncard_sdiff_singleton_of_mem W4.one_mem, hn4]
  have hA1f : A1.Finite := by rw [hA1]; exact hf1.subset (Set.sdiff_subset ..)
  have hA2f : A2.Finite := by rw [hA2]; exact hf2.subset (Set.sdiff_subset ..)
  have hA3f : A3.Finite := by rw [hA3]; exact hf3.subset (Set.sdiff_subset ..)
  have hA4f : A4.Finite := by rw [hA4]; exact hf4.subset (Set.sdiff_subset ..)
  -- They are pairwise disjoint.
  have hD12 : Disjoint A1 A2 := by rw [hA1, hA2]; exact disjoint_sdiff_of_card_three hc1 hc2 hW12
  have hD13 : Disjoint A1 A3 := by rw [hA1, hA3]; exact disjoint_sdiff_of_card_three hc1 hc3 hW13
  have hD14 : Disjoint A1 A4 := by rw [hA1, hA4]; exact disjoint_sdiff_of_card_three hc1 hc4 hW14
  have hD23 : Disjoint A2 A3 := by rw [hA2, hA3]; exact disjoint_sdiff_of_card_three hc2 hc3 hW23
  have hD24 : Disjoint A2 A4 := by rw [hA2, hA4]; exact disjoint_sdiff_of_card_three hc2 hc4 hW24
  have hD34 : Disjoint A3 A4 := by rw [hA3, hA4]; exact disjoint_sdiff_of_card_three hc3 hc4 hW34
  -- Hence their union has `8` elements.
  have hU12 : (A1 ∪ A2).ncard = 4 := by rw [Set.ncard_union_eq hD12 hA1f hA2f, hA1n, hA2n]
  have hD123 : Disjoint (A1 ∪ A2) A3 := by
    rw [Set.disjoint_left]
    intro z hz hz3
    rw [Set.mem_union] at hz
    rcases hz with hz1 | hz2
    · exact (Set.disjoint_left.mp hD13) hz1 hz3
    · exact (Set.disjoint_left.mp hD23) hz2 hz3
  have hU123 : ((A1 ∪ A2) ∪ A3).ncard = 6 := by
    rw [Set.ncard_union_eq hD123 (hA1f.union hA2f) hA3f, hU12, hA3n]
  have hD1234 : Disjoint ((A1 ∪ A2) ∪ A3) A4 := by
    rw [Set.disjoint_left]
    intro z hz hz4
    rw [Set.mem_union] at hz
    rcases hz with hz12 | hz3
    · rw [Set.mem_union] at hz12
      rcases hz12 with hz1 | hz2
      · exact (Set.disjoint_left.mp hD14) hz1 hz4
      · exact (Set.disjoint_left.mp hD24) hz2 hz4
    · exact (Set.disjoint_left.mp hD34) hz3 hz4
  have hU1234 : (((A1 ∪ A2) ∪ A3) ∪ A4).ncard = 8 := by
    rw [Set.ncard_union_eq hD1234 ((hA1f.union hA2f).union hA3f) hA4f, hU123, hA4n]
  -- The union sits inside the eight nonidentity elements of `R`.
  have hSsub : (((A1 ∪ A2) ∪ A3) ∪ A4) ⊆ (R : Set G) \ {1} := by
    intro z hz
    rw [Set.mem_sdiff]
    rw [Set.mem_union] at hz
    rcases hz with hz | hz4
    · rw [Set.mem_union] at hz
      rcases hz with hz | hz3
      · rw [Set.mem_union] at hz
        rcases hz with hz1 | hz2
        · rw [hA1, Set.mem_sdiff] at hz1
          exact ⟨(hsub W1 hm1).1 hz1.1, hz1.2⟩
        · rw [hA2, Set.mem_sdiff] at hz2
          exact ⟨(hsub W2 hm2).1 hz2.1, hz2.2⟩
      · rw [hA3, Set.mem_sdiff] at hz3
        exact ⟨(hsub W3 hm3).1 hz3.1, hz3.2⟩
    · rw [hA4, Set.mem_sdiff] at hz4
      exact ⟨(hsub W4 hm4).1 hz4.1, hz4.2⟩
  have hRsdiffn : ((R : Set G) \ {1}).ncard = 8 := by
    rw [Set.ncard_sdiff_singleton_of_mem R.one_mem, hRn]
  -- Cardinality forces the two sets to be equal.
  have hSeq : (((A1 ∪ A2) ∪ A3) ∪ A4) = (R : Set G) \ {1} :=
    Set.eq_of_subset_of_ncard_le hSsub (by rw [hRsdiffn, hU1234])
      (hRfin.subset (Set.sdiff_subset ..))
  have hxS : x ∈ (((A1 ∪ A2) ∪ A3) ∪ A4) := by
    rw [hSeq, Set.mem_sdiff]
    exact ⟨hxR, by simpa using hxne⟩
  -- Extract the subgroup containing `x`.
  rw [Set.mem_union] at hxS
  rcases hxS with hxS | hx4
  · rw [Set.mem_union] at hxS
    rcases hxS with hxS | hx3
    · rw [Set.mem_union] at hxS
      rcases hxS with hx1 | hx2
      · rw [hA1, Set.mem_sdiff] at hx1
        exact ⟨W1, hm1, hx1.1⟩
      · rw [hA2, Set.mem_sdiff] at hx2
        exact ⟨W2, hm2, hx2.1⟩
    · rw [hA3, Set.mem_sdiff] at hx3
      exact ⟨W3, hm3, hx3.1⟩
  · rw [hA4, Set.mem_sdiff] at hx4
    exact ⟨W4, hm4, hx4.1⟩

end Work.A7REC.Char
