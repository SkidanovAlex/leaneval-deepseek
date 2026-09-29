import Mathlib
import Submission.Work.Transform.Defs

namespace Work.Transform

/-- Sum of the lengths of the members of a list, when every member has length `r`. -/
private theorem sum_map_length_eq {r : ℕ} {w : List (List (ℤ × ℤ))}
    (hr : ∀ u ∈ w, u.length = r) : (w.map List.length).sum = w.length * r := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have ha : a.length = r := hr a (by simp)
    have ht : ∀ u ∈ t, u.length = r := fun u hu => hr u (by simp [hu])
    rw [List.map_cons, List.sum_cons, ih ht, ha, List.length_cons]
    ring

/-- Flattening an `M × r` matrix of `C̃◦`-vectors gives a `C̃◦`-vector of length `M * r`.
Guidance: keep every auxiliary lemma `private` (modules written in parallel in the same
`Work.Transform` namespace must remain importable together). -/
theorem inDiscFlatten {p M r : ℕ} {w : List (List (ℤ × ℤ))} (h : HvdH.InDiscArr p M r w) :
    HvdH.InDiscVec p (M * r) w.flatten := by
  obtain ⟨hlen, hmem⟩ := h
  have hr : ∀ u ∈ w, u.length = r := fun u hu => (hmem u hu).1
  refine ⟨?_, ?_⟩
  · rw [List.length_flatten, sum_map_length_eq hr, hlen]
  · intro z hz
    obtain ⟨u, hu, hzu⟩ := List.mem_flatten.mp hz
    exact (hmem u hu).2 z hzu

end Work.Transform
