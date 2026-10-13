import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.cells

namespace Work.WilE7

/-- For the graph cell over `C`: dropping the last coordinate recovers the base `C`. -/
private theorem init_image_graph {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    Fin.init '' {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} = C := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz.1
  · intro hx
    exact ⟨Fin.snoc x (f x), ⟨by simpa using hx, by simp⟩, by simp⟩

/-- For the band cell over `C`: dropping the last coordinate recovers the base `C`.
This is where the strict inequality `a < b` on `C` is used: the fibre of the band over a
base point is a nonempty open interval. -/
private theorem init_image_band {n : ℕ} (C : Set (Fin n → ℝ)) (a b : (Fin n → ℝ) → EReal)
    (hab : ∀ x ∈ C, a x < b x) :
    Fin.init '' {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = C := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz.1
  · intro hx
    obtain ⟨t, ht⟩ := EReal.exists_between_coe_real (hab x hx)
    exact ⟨Fin.snoc x t, ⟨by simpa using hx, by simpa using ht.1, by simpa using ht.2⟩, by simp⟩

/-- Every cylindrical cell in `ℝ^{n+1}` projects to a cylindrical cell in `ℝⁿ` (namely onto
its base cell), and the projection is nonempty when the cell is. -/
private theorem init_image_cell {n : ℕ} {B : Set (Fin (n+1) → ℝ)}
    (hB : WilkiesDesign.IsCell (n+1) B) (hne : B.Nonempty) :
    WilkiesDesign.IsCell n (Fin.init '' B) ∧ (Fin.init '' B).Nonempty := by
  cases hB with
  | graph hC f hf =>
      rw [init_image_graph]
      obtain ⟨z, hz⟩ := hne
      exact ⟨hC, Fin.init z, hz.1⟩
  | band hC a b ha hb hab =>
      rw [init_image_band _ a b hab]
      obtain ⟨z, hz⟩ := hne
      exact ⟨hC, Fin.init z, hz.1⟩

/-- A nonempty cell `A ⊆ ℝⁿ` is a cylindrical decomposition of itself: the singleton
`{A}` consists of one nonempty cell, is trivially pairwise disjoint, has union `A`, and
its projection is the corresponding singleton decomposition one dimension down. -/
private theorem singleton_isCylDecompOn : ∀ (n : ℕ) (A : Set (Fin n → ℝ)),
    WilkiesDesign.IsCell n A → A.Nonempty → WilkiesDesign.E.IsCylDecompOn n A {A} := by
  intro n
  induction n with
  | zero =>
      intro A hA hne
      cases hA
      exact Or.inl ⟨rfl, rfl⟩
  | succ k ih =>
      intro A hA hne
      obtain ⟨hcell, hne'⟩ := init_image_cell hA hne
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro c hc
        rw [Finset.mem_singleton] at hc
        subst hc
        exact ⟨hA, hne⟩
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb
        exact absurd (ha.trans hb.symm) hab
      · simp
      · simpa using ih (Fin.init '' A) hcell hne'

theorem singleton_cylDecomp :
    (∀ {n : ℕ} (A : Set (Fin n → ℝ)), WilkiesDesign.IsCell n A → A.Nonempty →
        WilkiesDesign.E.IsCylDecompOn n A {A}) ∧
    (∀ {n : ℕ} (B : Set (Fin (n + 1) → ℝ)), WilkiesDesign.IsCell (n + 1) B → B.Nonempty →
        WilkiesDesign.IsCell n (Fin.init '' B) ∧ (Fin.init '' B).Nonempty) :=
  ⟨fun A hA hne => singleton_isCylDecompOn _ A hA hne,
   fun _ hB hne => init_image_cell hB hne⟩

end Work.WilE7
