import Mathlib

namespace Work.EKLC6Core

/-- **Elementary Vitali-type 3-covering lemma (finite version).**

Given a finite family of open balls `Metric.ball (c a) (ρ a)` (`a ∈ T`) with positive radius on `T`,
there is a subfamily `u ⊆ T` of pairwise disjoint balls such that every ball of the family is
contained in the ball with the same centre and radius `3 * ρ b`, for some `b ∈ u`.

The proof is the classical greedy selection by decreasing radius: pick a ball of maximal radius,
keep it, discard every ball meeting it, and iterate. A discarded ball `a` meets a kept ball `b` of
radius at least `ρ a`, and an `ε`-argument on the (open) intersection then gives
`Metric.ball (c a) (ρ a) ⊆ Metric.ball (c b) (3 * ρ b)`; the strict inequality is exactly why the
constant `3` is affordable for open balls. -/
theorem exists_disjoint_ball_subfamily {ι : Type*} (T : Finset ι) (c ρ : ι → ℝ)
    (hρ : ∀ a ∈ T, 0 < ρ a) :
    ∃ u : Finset ι, u ⊆ T ∧
      (∀ a ∈ u, ∀ b ∈ u, a ≠ b →
        Disjoint (Metric.ball (c a) (ρ a)) (Metric.ball (c b) (ρ b))) ∧
      ∀ a ∈ T, ∃ b ∈ u, Metric.ball (c a) (ρ a) ⊆ Metric.ball (c b) (3 * ρ b) := by
  classical
  -- Geometric core: if `a` and `b` are open balls with `ρ b ≤ ρ a` that meet, then the smaller
  -- one is contained in the ball of radius `3 * ρ a` around the same centre as the larger one.
  have geo : ∀ {a b : ι}, ρ b ≤ ρ a →
      ¬ Disjoint (Metric.ball (c a) (ρ a)) (Metric.ball (c b) (ρ b)) →
      Metric.ball (c b) (ρ b) ⊆ Metric.ball (c a) (3 * ρ a) := by
    intro a b _ hnd x hx
    rw [Metric.mem_ball] at hx ⊢
    obtain ⟨y, hy⟩ := Set.not_disjoint_iff_nonempty_inter.mp hnd
    rw [Set.mem_inter_iff, Metric.mem_ball, Metric.mem_ball] at hy
    obtain ⟨hya, hyb⟩ := hy
    rw [dist_comm] at hyb
    have h1 : dist x (c a) ≤ dist x (c b) + dist (c b) y + dist y (c a) :=
      dist_triangle4 x (c b) y (c a)
    have h2 : dist x (c b) + dist (c b) y + dist y (c a) < 3 * ρ a := by
      have hA : dist x (c b) + dist (c b) y < ρ b + ρ b := add_lt_add hx hyb
      have hB : dist x (c b) + dist (c b) y + dist y (c a) < (ρ b + ρ b) + ρ a :=
        add_lt_add hA hya
      linarith
    linarith
  -- Greedy selection, by strong induction on the cardinality of the remaining family.
  suffices main : ∀ n : ℕ, ∀ T : Finset ι, T.card = n → (∀ a ∈ T, 0 < ρ a) →
      ∃ u : Finset ι, u ⊆ T ∧
        (∀ a ∈ u, ∀ b ∈ u, a ≠ b →
          Disjoint (Metric.ball (c a) (ρ a)) (Metric.ball (c b) (ρ b))) ∧
        ∀ a ∈ T, ∃ b ∈ u, Metric.ball (c a) (ρ a) ⊆ Metric.ball (c b) (3 * ρ b) from
    main T.card T rfl hρ
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro T hcard hρT
  rcases T.eq_empty_or_nonempty with hT | hne
  · subst hT
    exact ⟨∅, by simp, by simp, by simp⟩
  · -- Pick an element of maximal radius, keep its ball, and recurse on the balls disjoint from it.
    obtain ⟨a, haT, hamax⟩ := Finset.exists_max_image T ρ hne
    set S : Finset ι :=
      T.filter (fun b => Disjoint (Metric.ball (c a) (ρ a)) (Metric.ball (c b) (ρ b))) with hSdef
    have hmemS : ∀ b : ι, b ∈ S ↔ b ∈ T ∧
        Disjoint (Metric.ball (c a) (ρ a)) (Metric.ball (c b) (ρ b)) := by
      intro b; simp only [hSdef, Finset.mem_filter]
    have hST : S ⊆ T := fun b hb => (hmemS b).mp hb |>.1
    have haS : a ∉ S := by
      intro hmem
      have hd := (hmemS a).mp hmem |>.2
      have hx : c a ∈ Metric.ball (c a) (ρ a) := Metric.mem_ball_self (hρT a haT)
      exact (Set.disjoint_left.mp hd hx) hx
    have hcardS : S.card < T.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨hST, fun heq => haS (heq ▸ haT)⟩
    have hlt : S.card < n := hcard ▸ hcardS
    obtain ⟨u, huS, hdisj, hcov⟩ := ih S.card hlt S rfl (fun b hb => hρT b (hST hb))
    refine ⟨insert a u, ?_, ?_, ?_⟩
    · -- the resulting family is still a subfamily of `T`
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact haT
      · exact hST (huS hx)
    · -- pairwise disjointness
      intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact (hmemS y).mp (huS hy) |>.2
      · rcases hy with rfl | hy
        · exact disjoint_comm.mp ((hmemS x).mp (huS hx) |>.2)
        · exact hdisj x hx y hy hxy
    · -- covering
      intro b hbT
      by_cases hbS : b ∈ S
      · obtain ⟨b', hb'u, hsub⟩ := hcov b hbS
        exact ⟨b', Finset.mem_insert_of_mem hb'u, hsub⟩
      · refine ⟨a, Finset.mem_insert_self a u, ?_⟩
        have hnd : ¬ Disjoint (Metric.ball (c a) (ρ a)) (Metric.ball (c b) (ρ b)) := by
          intro hd
          exact hbS ((hmemS b).mpr ⟨hbT, hd⟩)
        exact geo (hamax b hbT) hnd

end Work.EKLC6Core
