import Mathlib
import Submission.Work.WilE8.E2.star_of_semipf

namespace Work.WilE8.StarOfSemipfLe

open Classical

/-- **`star_of_semipf` with a format budget fixed in advance.**  If `X` is a semi-Pfaffian set
of format `≤ F''`, then the projection of its point set is a `Star`-set of format `F''` (not
just `X.fmt`) whose degree is given by the component bound at the *fixed* budget `F''`.  This is
`Work.WilE8.E2.star_of_semipf` with the format argument decoupled from `X`, which is needed when
the degree bound must be expressed by a single polynomial independent of `X.fmt`. -/
theorem star_of_semipf_le
    (hE2 : ∀ F'' : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F'' →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n m F'' : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)) (hX : X.fmt ≤ F'') :
    WilkiesDesign.E.Star F'' ((hE2 F'').choose.eval X.deg * X.deg) n
      (WilkiesDesign.E.projFirst n m '' X.set) := by
  classical
  obtain ⟨s, hcard, hsub, hcov⟩ := (hE2 F'').choose_spec (n + m) X hX
  refine ⟨s.toList.map (fun y => (⟨m, X, y⟩ : WilkiesDesign.E.StarPiece n)), ?_, ?_, ?_⟩
  · -- the projected set is the union of the projected components through the representatives
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
  · -- every piece has format `≤ F''`, by the assumption on `X`
    intro P hP
    rw [List.mem_map] at hP
    obtain ⟨y, -, rfl⟩ := hP
    exact hX
  · -- the degrees add up to at most `s.card * X.deg ≤ p.eval X.deg * X.deg`
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
      _ ≤ (hE2 F'').choose.eval X.deg * X.deg := Nat.mul_le_mul_right X.deg hcard

end Work.WilE8.StarOfSemipfLe
