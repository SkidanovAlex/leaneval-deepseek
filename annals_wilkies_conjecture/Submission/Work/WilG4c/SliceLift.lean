import Mathlib
import Submission.Work.WilG4c.AlSliceBase

namespace Work.WilG4c

theorem SliceLift {p p' n : ℕ} (e : Fin p' ↪ Fin p) (C : Set (Fin p → ℝ))
    (Ψ : (Fin p' → ℝ) → (Fin p → ℝ)) (hsec : ∀ l ∈ C, Ψ (l ∘ e) = l)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (z : Fin (p + (n + 1) + 1) → ℝ) (hz : Work.WilkG4c.parPt (Fin.init z) ∈ C) :
    (z ∈ Work.WilkG4c.AlDgListSlice p n f L ↔
      (z ∘ Work.WilkG4c.cutIdxHat p p' n e) ∈
        Work.WilkG4c.AlDgListSlice p' n (fun u y => f (Ψ u) y) L) := by
  -- The lifted point `z ∘ cutIdxHat` has parameter part `parPt (Fin.init z) ∘ e` and the same
  -- cube and value coordinates as `z`.  Since `parPt (Fin.init z) ∈ C`, the section hypothesis
  -- `hsec` identifies `Ψ (parPt (Fin.init z) ∘ e)` with `parPt (Fin.init z)`, so that the two
  -- slices `y ↦ f (parPt (Fin.init z)) y` and `y ↦ f (Ψ (parPt (Fin.init (z ∘ cutIdxHat)))) y`
  -- coincide; the defining conditions of `AlDgListSlice` are then literally the same.
  have hpar := Work.WilkG4c.parPt_cutIdxHat e z
  have hcube := Work.WilkG4c.cubePt_cutIdxHat e z
  have hlast := Work.WilkG4c.last_cutIdxHat e z
  have hΨ : Ψ (fun i => Work.WilkG4c.parPt (Fin.init z) (e i)) =
      Work.WilkG4c.parPt (Fin.init z) := hsec _ hz
  simp only [Work.WilkG4c.mem_AlDgListSlice, hpar, hcube, hlast, hΨ]

end Work.WilG4c
