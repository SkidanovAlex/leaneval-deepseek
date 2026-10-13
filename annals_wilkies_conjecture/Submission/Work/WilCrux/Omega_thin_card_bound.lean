/-
  WilCrux : `Work.WilCrux.Omega_thin_card_bound` — cardinality bound for thin (empty-interior)
  `Ω`-sets in `ℝ¹`.

  `S.comps a` writes an `Ω`-set `A ⊆ ℝ¹` as a finite union `A = ⋃₀ s` of preconnected pieces
  with `s.card ≤ p.eval D`.  If `A` has empty interior then so does every piece `c ∈ s`
  (as `c ⊆ A`), and a preconnected subset of `ℝ¹` with empty interior is a subsingleton
  (`Work.WilG1.Calc.isPreconnected_subsingleton_of_interior_empty`).  Picking one point per
  nonempty piece — at most one per piece, so at most `s.card` points in total — gives a finite
  set `B ⊇ A` with `B.card ≤ s.card ≤ p.eval D`.  This is the cardinality bound needed by the
  one-dimensional pieces of `Work.WilCrux` (cf. `UnifMonotonePieces`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Calc.finite_of_interior_empty

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

theorem Omega_thin_card_bound (S : WilkiesDesign.SOMin) (a : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (D : ℕ) (A : Set (Fin 1 → ℝ)),
      A ∈ S.Ω a D 1 → interior A = ∅ →
        ∃ B : Finset (Fin 1 → ℝ), B.card ≤ p.eval D ∧ ∀ z : Fin 1 → ℝ, z ∉ B → z ∉ A := by
  obtain ⟨p, hp⟩ := S.comps a
  refine ⟨p, fun D A hA hint => ?_⟩
  obtain ⟨s, hcard, hconn, hAeq⟩ := hp D A hA
  -- Every piece of the decomposition is a subsingleton.
  have hpiece : ∀ c ∈ s, (c : Set (Fin 1 → ℝ)).Subsingleton := by
    intro c hc
    have hcA : (c : Set (Fin 1 → ℝ)) ⊆ A := by
      intro z hz
      rw [hAeq]
      exact Set.mem_sUnion.mpr ⟨c, hc, hz⟩
    have hintc : interior (c : Set (Fin 1 → ℝ)) = ∅ := by
      have h := interior_mono hcA
      rw [hint] at h
      exact Set.Subset.antisymm h (Set.empty_subset _)
    exact Work.WilG1.Calc.isPreconnected_subsingleton_of_interior_empty (hconn c hc) hintc
  -- One representative point per nonempty piece.
  let g : {c // c ∈ s} → (Fin 1 → ℝ) :=
    fun c => if h : (c.1 : Set (Fin 1 → ℝ)).Nonempty then Classical.choose h else 0
  let B : Finset (Fin 1 → ℝ) := s.attach.image g
  refine ⟨B, ?_, ?_⟩
  · have h1 : B.card ≤ s.card := by
      have h2 : B.card ≤ s.attach.card := Finset.card_image_le
      rw [Finset.card_attach] at h2
      exact h2
    exact le_trans h1 hcard
  · intro z hzB hzA
    rw [hAeq] at hzA
    obtain ⟨c, hc, hzc⟩ := Set.mem_sUnion.mp hzA
    have hne : (c : Set (Fin 1 → ℝ)).Nonempty := ⟨z, hzc⟩
    have hg : g ⟨c, hc⟩ = z := by
      have hcv : Classical.choose hne ∈ (c : Set (Fin 1 → ℝ)) := Classical.choose_spec hne
      have heq : z = Classical.choose hne := hpiece c hc hzc hcv
      simp only [g]
      rw [dite_eq_left hne]
      exact heq.symm
    have hmem : g ⟨c, hc⟩ ∈ B :=
      Finset.mem_image.mpr ⟨⟨c, hc⟩, Finset.mem_attach s ⟨c, hc⟩, rfl⟩
    rw [hg] at hmem
    exact hzB hmem

end Work.WilCrux
