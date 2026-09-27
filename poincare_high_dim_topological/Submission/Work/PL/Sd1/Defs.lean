import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.affineIndependent_bary_image

/-!
# `Work.PL.Sd1.Defs` — faces of the subdivision simplex of a flag

For a flag `l` (a list of vertices of a simplex `Δ`) and a set `J` of indices, `face l J` is
the face of the subdivision simplex `PL.simp ((prefixes l).image bary)` spanned by the
centroids of the prefix sets with indices in `J`.
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Sd1

noncomputable section

variable {N : ℕ}

/-- The face of the subdivision simplex of the flag `l` spanned by the prefix sets with
indices in `J`. -/
def face (l : List (PL.E N)) (J : Finset ℕ) : Set (PL.E N) :=
  PL.simp ((J.image (Work.PL.Shell.prefAt l)).image Work.PL.Shell.bary)

/-- Indices of the vertices of the flag `l`. -/
def flagIdx (l : List (PL.E N)) : Finset ℕ := Finset.range l.length

/-- The index set of the face common to the flag `l` and the flag `l'`. -/
def sameIdx (l l' : List (PL.E N)) : Finset ℕ :=
  (flagIdx l).filter fun j => Work.PL.Shell.prefAt l j ∈ Work.PL.Shell.prefixes l'

/-- The indices of the prefix sets of `l` that miss a given vertex. -/
def missIdx (l : List (PL.E N)) (w : PL.E N) : Finset ℕ :=
  (flagIdx l).filter fun j => w ∉ Work.PL.Shell.prefAt l j

/-- `face` is monotone in the index set. -/
theorem face_mono {l : List (PL.E N)} {J J' : Finset ℕ} (h : J ⊆ J') :
    face l J ⊆ face l J' := by
  rw [face, face]
  refine convexHull_mono ?_
  intro A hA
  rw [Finset.mem_coe] at hA ⊢
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hA
  obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hb
  exact Finset.mem_image.mpr
    ⟨b, Finset.mem_image.mpr ⟨j, h hj, hjb⟩, hba⟩

end

end Work.PL.Sd1
