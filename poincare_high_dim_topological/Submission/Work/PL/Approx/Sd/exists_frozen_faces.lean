import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.SdSubdiv
import Submission.Work.PL.Subdiv.SdBasic

/-!
# Faces of a subdivision frozen on a subcomplex

Given a finite complex `K`, a subcomplex `L ≤ K` and `r : ℕ`, there is a finite family `T` of faces
of the `r`-fold barycentric subdivision of `K` which covers `L.space` and each of whose members is
contained in a simplex of `L`.

The construction is simply to take `T` to be *all* the faces of the `r`-fold subdivision of `L`
itself: subdivision does not change the underlying space (so the union is `L.space`), every face of
a subdivision of `L` lies in a simplex of `L` (`Subdivides`), and subcomplexes are preserved by
subdivision (`sd_isSub`), so these faces are faces of the subdivision of `K` as well.
-/

namespace Work.PL.Approx.Sd

open Set

/-- **Subcomplexes are preserved by iterated barycentric subdivision.** -/
theorem sdIter_isSub_of_isSub {N : ℕ} {V W : PL.Cx N} (h : PL.IsSub V W) (r : ℕ)
    (hV : V.faces.Finite) (hW : W.faces.Finite) :
    PL.IsSub (Work.PL.Subdiv.sdIter r V hV) (Work.PL.Subdiv.sdIter r W hW) := by
  induction r with
  | zero => exact h
  | succ n ih =>
    show PL.IsSub (Work.PL.Subdiv.sd (Work.PL.Subdiv.sdIter n V hV))
      (Work.PL.Subdiv.sd (Work.PL.Subdiv.sdIter n W hW))
    exact Work.PL.Subdiv.sd_isSub ih

lemma exists_frozen_faces {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) (L : PL.Cx N)
    (hLK : PL.IsSub L K) (hLfin : L.faces.Finite) (r : ℕ) :
    ∃ T : Finset (Finset (PL.E N)),
      (∀ t ∈ T, t ∈ ((sdSubdiv N).iter r K hK).faces) ∧
      (⋃ t ∈ T, PL.simp t = L.space) ∧
      (∀ t ∈ T, ∃ ρ ∈ L.faces, PL.simp t ⊆ PL.simp ρ) := by
  classical
  refine ⟨(Work.PL.Subdiv.sdIter_faces_finite r L hLfin).toFinset, ?_, ?_, ?_⟩
  · intro t ht
    rw [Work.PL.Approx.Subdiv.iter_sdSubdiv]
    exact sdIter_isSub_of_isSub hLK r hLfin hK ((Set.Finite.mem_toFinset _).mp ht)
  · have hunion : (⋃ t ∈ (Work.PL.Subdiv.sdIter r L hLfin).faces, PL.simp t)
        = (⋃ t ∈ (Work.PL.Subdiv.sdIter_faces_finite r L hLfin).toFinset, PL.simp t) := by
      simp only [Set.Finite.mem_toFinset]
    rw [← hunion, ← (Work.PL.Subdiv.sdIter_subdivides r L hLfin).1]
    rfl
  · intro t ht
    exact (Work.PL.Subdiv.sdIter_subdivides r L hLfin).2 t
      ((Set.Finite.mem_toFinset _).mp ht)

end Work.PL.Approx.Sd
