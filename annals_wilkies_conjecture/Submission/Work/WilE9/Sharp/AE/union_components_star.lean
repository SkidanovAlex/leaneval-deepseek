import Mathlib
import Submission.Work.WilE8.StarOfSemipfLe.star_of_semipf_le

namespace Work.WilE9.Sharp.AE

/-- **`star_of_semipf_le` for a union of connected components.**  If `Y ⊆ X.set` is a union of
connected components of `X.set` (i.e. `connectedComponentIn X.set z ⊆ Y` for every `z ∈ Y`),
then `Y` is presented by the sub-family of the pieces of `star_of_semipf_le` that lie in `Y`,
so `projFirst n m '' Y` is a `Star`-set with the same format and degree bounds. -/
theorem union_components_star
    (hE2 : ∀ F'' : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F'' →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n m F'' : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)) (hX : X.fmt ≤ F'')
    (Y : Set (Fin (n + m) → ℝ)) (hYsub : Y ⊆ X.set)
    (hY : ∀ z ∈ Y, connectedComponentIn X.set z ⊆ Y) :
    WilkiesDesign.E.Star F'' ((hE2 F'').choose.eval X.deg * X.deg) n
      (WilkiesDesign.E.projFirst n m '' Y) := by
  classical
  obtain ⟨s, hcard, hsub, hcov⟩ := (hE2 F'').choose_spec (n + m) X hX
  refine ⟨(s.filter (fun y => y ∈ Y)).toList.map
      (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n)), ?_, ?_, ?_⟩
  · -- `projFirst '' Y` is the union of the projected components through the representatives in `Y`
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨z, hz, rfl⟩
      have hzX : z ∈ X.set := hYsub hz
      obtain ⟨y, hy, heq⟩ := hcov z hzX
      have hyY : y ∈ Y := hY z hz (heq ▸ mem_connectedComponentIn (hsub hy))
      rw [Work.WilE8.mem_list_iUnion]
      refine ⟨⟨m, X, y⟩, ?_, ?_⟩
      · rw [List.mem_map]
        exact ⟨y, Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨hy, hyY⟩), rfl⟩
      · refine ⟨z, ?_, rfl⟩
        show z ∈ connectedComponentIn X.set y
        rw [← heq]
        exact mem_connectedComponentIn hzX
    · intro x hx
      rw [Work.WilE8.mem_list_iUnion] at hx
      obtain ⟨P, hP, hx⟩ := hx
      rw [List.mem_map] at hP
      obtain ⟨y, hy, rfl⟩ := hP
      rw [Finset.mem_toList, Finset.mem_filter] at hy
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, hY y hy.2 hz, rfl⟩
  · -- every piece carries the format `F''` inherited from `X`
    intro P hP
    rw [List.mem_map] at hP
    obtain ⟨y, -, rfl⟩ := hP
    exact hX
  · -- the degrees add up to at most `(s.filter _).card * X.deg ≤ p.eval X.deg * X.deg`
    have hdeg : ∀ x ∈ ((s.filter (fun y => y ∈ Y)).toList.map
        (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n))).map (fun P => P.X.deg),
        x ≤ X.deg := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      rw [List.mem_map] at hP
      obtain ⟨y, -, rfl⟩ := hP
      exact le_rfl
    calc (((s.filter (fun y => y ∈ Y)).toList.map
            (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n))).map
            (fun P => P.X.deg)).sum
        ≤ _ • X.deg := List.sum_le_length_nsmul _ _ hdeg
      _ = (s.filter (fun y => y ∈ Y)).card * X.deg := by simp
      _ ≤ (hE2 F'').choose.eval X.deg * X.deg :=
          Nat.mul_le_mul_right X.deg (le_trans (Finset.card_filter_le _ _) hcard)

end Work.WilE9.Sharp.AE
