import Mathlib

namespace Work.CORE3

/-- An explicit set of three elements has at most three elements. -/
private lemma ncard_three_le {Q : Type} (a b c : Q) : ({a, b, c} : Set Q).ncard ≤ 3 := by
  have h1 : ({b, c} : Set Q).ncard ≤ 2 := by
    have := Set.ncard_insert_le b ({c} : Set Q)
    rw [Set.ncard_singleton] at this
    simpa using this
  have h0 : ({a, b, c} : Set Q).ncard ≤ ({b, c} : Set Q).ncard + 1 := Set.ncard_insert_le a _
  omega

/-- If a set equals a `4`-element explicit set but is contained in a `3`-element one, contradiction. -/
private lemma absurd_of_sub {Q : Type} [Finite Q] {s t : Set Q} (h : s.ncard = 4)
    (h3 : t.ncard ≤ 3) (hsub : s ⊆ t) : False := by
  have := Set.ncard_le_ncard hsub
  omega

/-- A four-element explicit set has pairwise distinct entries. -/
private lemma distinct_of_ncard_four {Q : Type} [Finite Q] {a b c d : Q}
    (h : ({a, b, c, d} : Set Q).ncard = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hab
    exact absurd_of_sub h (ncard_three_le b c d) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl hab
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl))
  · intro hac
    exact absurd_of_sub h (ncard_three_le a b d) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hac.symm
      · exact Or.inr (Or.inr rfl))
  · intro had
    exact absurd_of_sub h (ncard_three_le a b c) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl had.symm)
  · intro hbc
    exact absurd_of_sub h (ncard_three_le a b d) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inl hbc.symm)
      · exact Or.inr (Or.inr rfl))
  · intro hbd
    exact absurd_of_sub h (ncard_three_le a b c) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl hbd.symm))
  · intro hcd
    exact absurd_of_sub h (ncard_three_le a b c) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inr hcd.symm))

theorem CosetPairCaseA {Q : Type} [Group Q] [Finite Q] (I : Set Q) (ι κ : Q)
    (hI : I = ({1, ι, ι⁻¹, κ} : Set Q)) (hcard : I.ncard = 4)
    (hι3 : ι * ι * ι = 1) (hκ2 : κ * κ = 1) (hκι : κ * ι * κ = ι⁻¹) :
    {p : Q × Q | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧
      (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}.ncard = 6 := by
  classical
  -- ## Distinctness of the four listed elements
  have hcard' : ({1, ι, ι⁻¹, κ} : Set Q).ncard = 4 := by rw [← hI]; exact hcard
  obtain ⟨hn1ι, _hn1ιi, _hn1κ, _hniιi, _hniκ, _hniik⟩ := distinct_of_ncard_four hcard'
  have hι_ne_one : ι ≠ 1 := hn1ι.symm
  -- ## Elementary group identities
  have hi_inv : ι⁻¹ = ι * ι := inv_eq_of_mul_eq_one_left hι3
  have hκ_inv : κ⁻¹ = κ := inv_eq_of_mul_eq_one_left hκ2
  have hii : ι⁻¹ * ι⁻¹ = ι := by rw [hi_inv, ← mul_assoc, hι3, one_mul]
  have h4 : (ι * ι) * (ι * ι) = ι := by rw [← mul_assoc, hι3, one_mul]
  have hι2ne1 : ι * ι ≠ 1 := by
    intro h
    exact hι_ne_one (calc ι = ι * (ι * ι) := by rw [h, mul_one]
                          _ = ι * ι * ι := by rw [mul_assoc]
                          _ = 1 := hι3)
  have hiine1 : ι⁻¹ * ι⁻¹ ≠ 1 := by
    intro h; exact hι_ne_one (hii.symm.trans h)
  have hκii : κ * ι⁻¹ * κ = ι := by
    have h := congrArg Inv.inv hκι
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hκ_inv] at h
    rw [← mul_assoc] at h
    exact h
  -- ## Membership in `I`
  have hκI : κ ∈ I := by rw [hI]; simp
  have hmem : ∀ x : Q, x ∈ I ↔ x = 1 ∨ x = ι ∨ x = ι⁻¹ ∨ x = κ := by
    intro x; rw [hI]; simp
  have hthree : ∀ x : Q, x ∈ I → x ≠ κ → (x = 1 ∨ x = ι ∨ x = ι⁻¹) := by
    intro x hx hxk
    rcases (hmem x).mp hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h hxk
  -- ## The characterisation of the counted pairs
  have key : ∀ x y : Q, x ∈ I → y ∈ I → x ≠ y →
      ((x⁻¹ * y) * (x⁻¹ * y) = 1 ↔ x = κ ∨ y = κ) := by
    intro x y hx hy hne
    constructor
    · intro hsq
      by_contra hc
      obtain ⟨hxk, hyk⟩ := not_or.mp hc
      have hx3 := hthree x hx hxk
      have hy3 := hthree y hy hyk
      rcases hx3 with rfl | rfl | rfl <;> rcases hy3 with rfl | rfl | rfl
      · exact hne rfl
      · simp only [inv_one, one_mul] at hsq; exact hι2ne1 hsq
      · simp only [inv_one, one_mul] at hsq; exact hiine1 hsq
      · simp only [mul_one] at hsq; exact hiine1 hsq
      · exact hne rfl
      · rw [hii] at hsq; exact hι2ne1 hsq
      · simp only [inv_inv, mul_one] at hsq; exact hι2ne1 hsq
      · simp only [inv_inv] at hsq; rw [h4] at hsq; exact hι_ne_one hsq
      · exact hne rfl
    · intro hcond
      rcases hcond with hxκ | hyκ
      · rw [hxκ]
        have hy3 := hthree y hy (fun h => hne (hxκ.trans h.symm))
        rcases hy3 with h | h | h
        · rw [h, hκ_inv]; simp [hκ2]
        · rw [h, hκ_inv]
          have hh : (κ * ι) * (κ * ι) = (κ * ι * κ) * ι := by group
          rw [hh, hκι, inv_mul_cancel]
        · rw [h, hκ_inv]
          have hh : (κ * ι⁻¹) * (κ * ι⁻¹) = (κ * ι⁻¹ * κ) * ι⁻¹ := by group
          rw [hh, hκii, mul_inv_cancel]
      · rw [hyκ]
        have hx3 := hthree x hx (fun h => hne (h.trans hyκ.symm))
        rcases hx3 with h | h | h
        · rw [h]; simp [hκ2]
        · rw [h]
          have hh : (ι⁻¹ * κ) * (ι⁻¹ * κ) = ι⁻¹ * (κ * ι⁻¹ * κ) := by group
          rw [hh, hκii, inv_mul_cancel]
        · rw [h]; simp only [inv_inv]
          have hh : (ι * κ) * (ι * κ) = ι * (κ * ι * κ) := by group
          rw [hh, hκι, mul_inv_cancel]
  -- ## Decomposition of the counted set as a disjoint union
  let A : Set (Q × Q) := ({κ} : Set Q) ×ˢ (I \ {κ})
  let B : Set (Q × Q) := (I \ {κ}) ×ˢ ({κ} : Set Q)
  have hS : ({p : Q × Q | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧
      (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1} : Set (Q × Q)) = A ∪ B := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_prod, Set.mem_sdiff,
      Set.mem_singleton_iff, A, B]
    constructor
    · rintro ⟨h1, h2, hne, hsq⟩
      rcases (key p.1 p.2 h1 h2 hne).mp hsq with hk | hk
      · exact Or.inl ⟨hk, h2, fun h => hne (hk.trans h.symm)⟩
      · exact Or.inr ⟨⟨h1, fun h => hne (h.trans hk.symm)⟩, hk⟩
    · rintro (⟨hk, h2, h2k⟩ | ⟨⟨h1, h1k⟩, hk⟩)
      · rw [hk]
        exact ⟨hκI, h2, Ne.symm h2k,
          (key κ p.2 hκI h2 (Ne.symm h2k)).mpr (Or.inl rfl)⟩
      · rw [hk]
        exact ⟨h1, hκI, h1k, (key p.1 κ h1 hκI h1k).mpr (Or.inr rfl)⟩
  -- ## Cardinalities
  have hdiff : (I \ {κ}).ncard = 3 := by
    have hsub : ({κ} : Set Q) ⊆ I := Set.singleton_subset_iff.mpr hκI
    rw [Set.ncard_sdiff hsub (Set.finite_singleton κ), Set.ncard_singleton, hcard]
  have hA : A.ncard = 3 := by
    show (({κ} : Set Q) ×ˢ (I \ {κ})).ncard = 3
    rw [Set.ncard_prod, Set.ncard_singleton, hdiff]
  have hB : B.ncard = 3 := by
    show ((I \ {κ}) ×ˢ ({κ} : Set Q)).ncard = 3
    rw [Set.ncard_prod, Set.ncard_singleton, hdiff]
  have hinter : A ∩ B = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨p, hp⟩
    rw [Set.mem_inter_iff] at hp
    obtain ⟨hpA, hpB⟩ := hp
    simp only [A, B, Set.mem_prod, Set.mem_singleton_iff, Set.mem_sdiff] at hpA hpB
    exact hpB.1.2 hpA.1
  have hmain : (A ∪ B).ncard = 6 := by
    have h1 := Set.ncard_union_add_ncard_inter A B
    rw [hinter, Set.ncard_empty, Nat.add_zero, hA, hB] at h1
    omega
  rw [hS]
  exact hmain

end Work.CORE3
