/-
  WilE8 / E2 — packaging the components bound (E2b) into a `Star`-presentation.

  `E2_components` supplies, for every semi-Pfaffian set `X ⊆ ℝ^{n+m}` of format `≤ F`, a finite
  set `s` of representatives of the connected components of `X.set`, of cardinality at most
  `p_F(X.deg)`.  Projecting to the first `n` coordinates, `projFirst n m '' X.set` is covered by
  the projections of the components through the points of `s`; each such projection is exactly
  the set of the `*`-piece `⟨m, X, y⟩`.  Taking the list of these pieces therefore expresses
  `projFirst n m '' X.set` as a `Star`-set of degree `≤ p_F(X.deg) · X.deg` and format `X.fmt`.
-/
import Mathlib
import Submission.Work.WilE8.Basic

namespace Work.WilE8.E2

open Classical

theorem star_of_semipf
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)) :
    WilkiesDesign.E.Star X.fmt ((hE2 X.fmt).choose.eval X.deg * X.deg) n
      (WilkiesDesign.E.projFirst n m '' X.set) := by
  classical
  obtain ⟨s, hcard, hsub, hcov⟩ := (hE2 X.fmt).choose_spec (n + m) X le_rfl
  refine ⟨s.toList.map (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n)), ?_, ?_, ?_⟩
  · -- the covering set is the union of the projected components through the representatives
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨z, hz, rfl⟩
      obtain ⟨y, hy, heq⟩ := hcov z hz
      rw [Work.WilE8.mem_list_iUnion]
      refine ⟨⟨m, X, y⟩, ?_, ?_⟩
      · rw [List.mem_map]
        exact ⟨y, Finset.mem_toList.mpr hy, rfl⟩
      · refine ⟨z, ?_, rfl⟩
        rw [← heq]
        exact mem_connectedComponentIn hz
    · intro x hx
      rw [Work.WilE8.mem_list_iUnion] at hx
      obtain ⟨P, hP, hx⟩ := hx
      rw [List.mem_map] at hP
      obtain ⟨y, -, rfl⟩ := hP
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, connectedComponentIn_subset X.set y hz, rfl⟩
  · -- every piece has format `X.fmt`
    intro P hP
    rw [List.mem_map] at hP
    obtain ⟨y, -, rfl⟩ := hP
    exact le_rfl
  · -- the degrees add up to at most `s.card * X.deg`
    have hdeg : ∀ x ∈ (s.toList.map (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n))).map
        (fun P => P.X.deg), x ≤ X.deg := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      rw [List.mem_map] at hP
      obtain ⟨y, -, rfl⟩ := hP
      exact le_rfl
    calc ((s.toList.map (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n))).map
            (fun P => P.X.deg)).sum
        ≤ ((s.toList.map (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n))).map
            (fun P => P.X.deg)).length • X.deg := List.sum_le_length_nsmul _ _ hdeg
      _ = s.card * X.deg := by simp
      _ ≤ (hE2 X.fmt).choose.eval X.deg * X.deg := Nat.mul_le_mul_right X.deg hcard

end Work.WilE8.E2
