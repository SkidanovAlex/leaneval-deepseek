import Mathlib
import Submission.Work.Smooth.Jordan.Family
import Submission.Work.Smooth.Jordan.family_disc_eq

namespace Work.Smooth.Jordan

open Set
open LeanEval.KnotTheory.PardonDistortion

/-- The trace of the curve `c i` is contained in the image of its spanning disc. -/
theorem range_curve_subset_range_disc {A : Set R3} {ι : Type} [Fintype ι] {c : ι → ℝ → R3}
    (h : FamilyDiscs A ι c) (i : ι) :
    Set.range (c i) ⊆ Set.range (h.disc i) := by
  rintro x ⟨θ, rfl⟩
  exact ⟨circlePoint θ, h.disc_boundary i θ⟩

/-- A point of the image of the spanning disc is either an interior point (the image of a point of
the open disc) or lies on the boundary curve. -/
theorem mem_range_disc_iff {A : Set R3} {ι : Type} [Fintype ι] {c : ι → ℝ → R3}
    (h : FamilyDiscs A ι c) (i : ι) {x : R3} :
    x ∈ Set.range (h.disc i) ↔
      (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.disc i z = x) ∨ x ∈ Set.range (c i) := by
  rw [family_disc_eq h i]
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]

/-- **The containment relation is transitive.**  If the curve `c i` lies inside the disc spanned by
`c j`, and `c j` lies inside the disc spanned by `c k`, then `c i` lies inside the disc spanned by
`c k`.

The geometric content is that the whole disc of `c i` lies in the disc of `c j` and that of `c j`
in that of `c k` (`inside_subset`), so a point of `c i` in the interior of the disc of `c j` is
also in the disc of `c k`; it cannot lie on the boundary curve `c k` (that would meet `c i`), so it
is *interior* to the disc of `c k`.  The remaining case `i = k` is impossible by antisymmetry of
the rank (`nested`). -/
theorem family_insideOpen_trans {A : Set LeanEval.KnotTheory.PardonDistortion.R3} {ι : Type} [Fintype ι] {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (h : FamilyDiscs A ι c) {i j k : ι} (hij : h.InsideOpen i j) (hjk : h.InsideOpen j k) : h.InsideOpen i k := by
  by_cases hik : i = k
  · have hjk' : h.InsideOpen j i := by rw [hik]; exact hjk
    by_cases hji : j = i
    · rw [hji] at hij
      exact absurd hij (h.not_insideOpen_self i)
    · have h1 : h.rank j < h.rank i := h.nested i j (Ne.symm hji) hjk'
      have h2 : h.rank i < h.rank j := h.nested j i hji hij
      exact absurd h1 (not_lt.mpr h2.le)
  · have hsub_ij : Set.range (h.disc i) ⊆ Set.range (h.disc j) := h.inside_subset j i hij
    have hsub_jk : Set.range (h.disc j) ⊆ Set.range (h.disc k) := h.inside_subset k j hjk
    obtain ⟨z₀, hz₀, hz₀mem⟩ := hij
    have hci : Set.range (c i) ⊆ Set.range (h.disc i) := range_curve_subset_range_disc h i
    have hxk : h.disc j z₀ ∈ Set.range (h.disc k) := hsub_jk (hsub_ij (hci hz₀mem))
    rcases (mem_range_disc_iff h k).mp hxk with ⟨w, hw, hwx⟩ | hxck
    · exact ⟨w, hw, by rw [hwx]; exact hz₀mem⟩
    · have hdisj : Disjoint (Set.range (c i)) (Set.range (c k)) := h.disjoint hik
      exact (Set.disjoint_left.mp hdisj hz₀mem hxck).elim

end Work.Smooth.Jordan
