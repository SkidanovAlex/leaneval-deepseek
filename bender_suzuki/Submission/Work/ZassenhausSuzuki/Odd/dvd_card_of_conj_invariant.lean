import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- If `S` is a union of conjugacy classes of a finite group `G`, and every conjugacy class
meeting `S` has cardinality divisible by `N`, then `|S|` is divisible by `N`. -/
theorem dvd_card_of_conj_invariant {G : Type} [Group G] [Finite G] (N : ℕ) (S : Set G)
    (hS : ∀ g : G, ∀ x : G, x ∈ S → g * x * g⁻¹ ∈ S)
    (hN : ∀ x : G, x ∈ S → N ∣ Nat.card ↥(ConjClasses.carrier (ConjClasses.mk x))) :
    N ∣ Nat.card S := by
  classical
  -- Strong induction on `|S|`: strip off one conjugacy class at a time.
  have key : ∀ m : ℕ, ∀ S : Set G, S.ncard = m →
      (∀ g x : G, x ∈ S → g * x * g⁻¹ ∈ S) →
      (∀ x : G, x ∈ S → N ∣ Nat.card ↥(ConjClasses.carrier (ConjClasses.mk x))) →
      N ∣ S.ncard := fun m =>
    Nat.strong_induction_on m (fun n ih S hSm hS' hN' => by
      by_cases hne : S.Nonempty
      · obtain ⟨x, hx⟩ := hne
        -- the conjugacy class of `x`, which is contained in `S`
        let A : Set G := ConjClasses.carrier (ConjClasses.mk x)
        have hxA : x ∈ A := ConjClasses.mem_carrier_mk
        have hAS : A ⊆ S := by
          intro y hy
          have h1 : ConjClasses.mk y = ConjClasses.mk x :=
            ConjClasses.mem_carrier_iff_mk_eq.mp hy
          have h2 : IsConj y x := ConjClasses.mk_eq_mk_iff_isConj.mp h1
          obtain ⟨c, hc⟩ := isConj_iff.mp h2.symm
          rw [← hc]
          exact hS' c x hx
        -- `A` is itself invariant under conjugation
        have hAinv : ∀ g y : G, y ∈ A → g * y * g⁻¹ ∈ A := by
          intro g y hy
          have hy' : ConjClasses.mk y = ConjClasses.mk x :=
            ConjClasses.mem_carrier_iff_mk_eq.mp hy
          have hconj : ConjClasses.mk y = ConjClasses.mk (g * y * g⁻¹) :=
            ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)
          exact ConjClasses.mem_carrier_iff_mk_eq.mpr (by rw [← hconj, hy'])
        -- `S \ A` is again a union of conjugacy classes
        have hS'inv : ∀ g y : G, y ∈ S \ A → g * y * g⁻¹ ∈ S \ A := by
          intro g y hy
          rw [Set.mem_sdiff] at hy ⊢
          refine ⟨hS' g y hy.1, ?_⟩
          intro hmem
          exact hy.2 (by
            have hgoal : g⁻¹ * (g * y * g⁻¹) * g = y := by group
            rw [← hgoal]
            simpa using hAinv g⁻¹ (g * y * g⁻¹) hmem)
        have hN'S' : ∀ y : G, y ∈ S \ A →
            N ∣ Nat.card ↥(ConjClasses.carrier (ConjClasses.mk y)) :=
          fun y hy => hN' y ((Set.mem_sdiff y).mp hy).1
        have hssub : S \ A ⊂ S := by
          rw [Set.ssubset_def]
          exact ⟨Set.sdiff_subset, fun hcon => ((Set.mem_sdiff x).mp (hcon hx)).2 hxA⟩
        have hlt : (S \ A).ncard < n := by
          have h := Set.ncard_lt_ncard hssub
          rw [hSm] at h
          exact h
        have hdvd' : N ∣ (S \ A).ncard := ih (S \ A).ncard hlt (S \ A) rfl hS'inv hN'S'
        have hdvdA : N ∣ A.ncard := hN' x hx
        have hsum : (S \ A).ncard + A.ncard = S.ncard :=
          Set.ncard_sdiff_add_ncard_of_subset hAS
        rw [← hsum]
        exact dvd_add hdvd' hdvdA
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
        exact dvd_zero N)
  exact key S.ncard S rfl hS hN

end Work.ZassenhausSuzuki.Odd
