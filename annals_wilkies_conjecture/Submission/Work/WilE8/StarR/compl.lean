import Mathlib
import Submission.Work.WilE8.Basic

namespace Work.WilE8.StarR

theorem compl
    (hE7 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
      WilkiesDesign.E.Star F D n Y → WilkiesDesign.E.Star a (p.eval D) n (WilkiesDesign.E.cubeC n \ Y))
    (a0 n : ℕ) :
    ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (X : Set (Fin n → ℝ)),
      WilkiesDesign.E.StarR a0 D n X → WilkiesDesign.E.StarR a (p.eval D) n Xᶜ := by
  obtain ⟨a, p, h⟩ := hE7 a0 n
  refine ⟨a, p, ?_⟩
  intro D X hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  refine ⟨WilkiesDesign.E.cubeC n \ Z, h D Z hZ, ?_⟩
  ext x
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
  exact ⟨fun hx => ⟨WilkiesDesign.E.psiV_mem_cube x, hx⟩, fun hx => hx.2⟩

end Work.WilE8.StarR
