import Mathlib

namespace Work.WilG1.Thin

/-- If a preconnected subset of `ℝ` contains points strictly below and strictly above a point `y`,
then `y` is an interior point of the set. -/
lemma mem_interior_of_preconnected_lt_lt {I : Set ℝ} (hI : IsPreconnected I) {p y q : ℝ}
    (hp : p ∈ I) (hq : q ∈ I) (hpy : p < y) (hyq : y < q) : y ∈ interior I :=
  interior_maximal (Set.Ioo_subset_Icc_self.trans (IsPreconnected.Icc_subset hI hp hq)) isOpen_Ioo
    ⟨hpy, hyq⟩

/-- A preconnected subset of `ℝ` has no three points `a < b < c` in its frontier. -/
lemma not_three_lt_frontier {I : Set ℝ} (hI : IsPreconnected I) :
    ¬ ∃ a ∈ frontier I, ∃ b ∈ frontier I, ∃ c ∈ frontier I, a < b ∧ b < c := by
  rintro ⟨a, ha, b, hb, c, hc, hab, hbc⟩
  have ha_cl : a ∈ closure I := frontier_subset_closure ha
  have hb_int : b ∉ interior I := (hb : b ∈ closure I \ interior I).2
  have hc_cl : c ∈ closure I := frontier_subset_closure hc
  have hex : ∃ p ∈ I, p < b := by
    obtain ⟨p, hp, hd⟩ := Metric.mem_closure_iff.mp ha_cl ((b - a) / 2) (by linarith)
    refine ⟨p, hp, ?_⟩
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).1
    linarith
  have hexq : ∃ q ∈ I, b < q := by
    obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.mp hc_cl ((c - b) / 2) (by linarith)
    refine ⟨q, hq, ?_⟩
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).2
    linarith
  obtain ⟨p, hp, hpb⟩ := hex
  obtain ⟨q, hq, hbq⟩ := hexq
  exact hb_int (mem_interior_of_preconnected_lt_lt hI hp hq hpb hbq)

theorem frontier_isPreconnected_finite {I : Set ℝ} (hI : IsPreconnected I) :
    (frontier I).Finite := by
  -- the frontier contains no three distinct points
  have no_three : ∀ a ∈ frontier I, ∀ b ∈ frontier I, ∀ c ∈ frontier I,
      a = b ∨ a = c ∨ b = c := by
    intro a ha b hb c hc
    by_contra h
    push_neg at h
    obtain ⟨hab, hac, hbc⟩ := h
    rcases lt_or_gt_of_ne hab with hab' | hab'
    · rcases lt_or_gt_of_ne hac with hac' | hac'
      · rcases lt_or_gt_of_ne hbc with hbc' | hbc'
        · exact not_three_lt_frontier hI ⟨a, ha, b, hb, c, hc, hab', hbc'⟩
        · exact not_three_lt_frontier hI ⟨a, ha, c, hc, b, hb, hac', hbc'⟩
      · exact not_three_lt_frontier hI ⟨c, hc, a, ha, b, hb, hac', hab'⟩
    · rcases lt_or_gt_of_ne hac with hac' | hac'
      · exact not_three_lt_frontier hI ⟨b, hb, a, ha, c, hc, hab', hac'⟩
      · rcases lt_or_gt_of_ne hbc with hbc' | hbc'
        · exact not_three_lt_frontier hI ⟨b, hb, c, hc, a, ha, hbc', hac'⟩
        · exact not_three_lt_frontier hI ⟨c, hc, b, hb, a, ha, hbc', hab'⟩
  by_cases hne : (frontier I).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    -- removing one point leaves a subsingleton
    have hss : (frontier I \ {x0}).Subsingleton := by
      rintro y ⟨hyF, hy0⟩ z ⟨hzF, hz0⟩
      simp only [Set.mem_singleton_iff] at hy0 hz0
      rcases no_three x0 hx0 y hyF z hzF with h | h | h
      · exact absurd h.symm hy0
      · exact absurd h.symm hz0
      · exact h
    refine Set.Finite.subset (hss.finite.insert x0) ?_
    intro z hz
    rw [Set.mem_insert_iff]
    by_cases hz0 : z = x0
    · exact Or.inl hz0
    · exact Or.inr ⟨hz, by simpa using hz0⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

end Work.WilG1.Thin
