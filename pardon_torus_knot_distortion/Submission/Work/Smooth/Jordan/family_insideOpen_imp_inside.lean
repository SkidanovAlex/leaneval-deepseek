import Mathlib
import Submission.Work.Smooth.Jordan.Family

namespace Work.Smooth.Jordan

/-- **The containment relation `InsideOpen` refines `Inside`.**  If the curve `c i` meets the
interior of the disc spanned by `c j`, then the whole curve `c i` lies in the closed disc spanned
by `c j`.

Indeed `inside_subset` already gives `range (disc i) ⊆ range (disc j)` from `InsideOpen i j`, and
the trace of `c i` is contained in `range (disc i)` because it is the image of the boundary circle
of `𝔻` under the embedding `disc i`. -/
theorem family_insideOpen_imp_inside {A : Set LeanEval.KnotTheory.PardonDistortion.R3} {ι : Type} [Fintype ι] {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (h : FamilyDiscs A ι c) {i j : ι} (hij : h.InsideOpen i j) : h.Inside j i := by
  intro x hx
  obtain ⟨θ, rfl⟩ := hx
  have hsub : Set.range (h.disc i) ⊆ Set.range (h.disc j) := h.inside_subset j i hij
  have hmem : h.disc i (circlePoint θ) ∈ Set.range (h.disc j) := hsub ⟨circlePoint θ, rfl⟩
  rwa [h.disc_boundary i θ] at hmem

end Work.Smooth.Jordan
