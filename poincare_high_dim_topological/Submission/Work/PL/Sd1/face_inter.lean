import Mathlib
import Submission.Work.PL.Sd1.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.convexHull_inter_bary
import Submission.Work.PL.Shell.bary_inj
import Submission.Work.PL.Shell.face_trace

namespace Work.PL.Sd1

/-- The face of the subdivision simplex of a flag `l` spanned by the index set `J` is the
intersection of the faces spanned by `J` and by `J'`.

`face l J` is the simplex on the centroids of the prefix sets `prefAt l j`, `j ∈ J`.  The
prefix sets form a chain of nonempty subsets of `Δ`, so their centroids are affinely
independent and the faces of the simplex on them meet in the face on the intersection of the
vertex sets (`Work.PL.Shell.convexHull_inter_bary`); since `l` has no repetitions, distinct
indices give distinct prefix sets. -/
theorem face_inter {N : ℕ} {Δ : Finset (PL.E N)} (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {l : List (PL.E N)} (hl : l.Nodup) (hlΔ : l.toFinset = Δ) {J J' : Finset ℕ}
    (hJ : J ⊆ Work.PL.Sd1.flagIdx l) (hJ' : J' ⊆ Work.PL.Sd1.flagIdx l) :
    Work.PL.Sd1.face l (J ∩ J') = Work.PL.Sd1.face l J ∩ Work.PL.Sd1.face l J' := by
  classical
  have hJlen : ∀ j ∈ J, j < l.length := fun j hj => Finset.mem_range.mp (hJ hj)
  have hJ'len : ∀ j ∈ J', j < l.length := fun j hj => Finset.mem_range.mp (hJ' hj)
  -- the prefix sets of `J` and of `J'` are chains of nonempty subsets of `Δ`
  have hC : ∀ A ∈ J.image (Work.PL.Shell.prefAt l), A.Nonempty ∧ A ⊆ Δ := fun A hA =>
    ⟨Work.PL.Shell.image_prefAt_nonempty hl hJlen A hA,
      Work.PL.Shell.image_prefAt_subset hJlen hlΔ A hA⟩
  have hC' : ∀ A ∈ J'.image (Work.PL.Shell.prefAt l), A.Nonempty ∧ A ⊆ Δ := fun A hA =>
    ⟨Work.PL.Shell.image_prefAt_nonempty hl hJ'len A hA,
      Work.PL.Shell.image_prefAt_subset hJ'len hlΔ A hA⟩
  have hchain : ∀ A ∈ J.image (Work.PL.Shell.prefAt l),
      ∀ B ∈ J.image (Work.PL.Shell.prefAt l), A ⊆ B ∨ B ⊆ A :=
    fun A hA B hB => Work.PL.Shell.image_prefAt_chain A hA B hB
  have hchain' : ∀ A ∈ J'.image (Work.PL.Shell.prefAt l),
      ∀ B ∈ J'.image (Work.PL.Shell.prefAt l), A ⊆ B ∨ B ⊆ A :=
    fun A hA B hB => Work.PL.Shell.image_prefAt_chain A hA B hB
  -- faces of a simplex on an affinely independent vertex set meet in the face of the
  -- intersection of the vertex sets
  have hinter :
      PL.simp ((J.image (Work.PL.Shell.prefAt l)).image Work.PL.Shell.bary) ∩
          PL.simp ((J'.image (Work.PL.Shell.prefAt l)).image Work.PL.Shell.bary)
        = PL.simp (((J.image (Work.PL.Shell.prefAt l)) ∩
            (J'.image (Work.PL.Shell.prefAt l))).image Work.PL.Shell.bary) :=
    Work.PL.Shell.convexHull_inter_bary (N := N) (Δ := Δ)
      (C := J.image (Work.PL.Shell.prefAt l)) (C' := J'.image (Work.PL.Shell.prefAt l))
      hΔ hC hC' hchain hchain'
  -- distinct indices of the flag give distinct prefix sets
  have hCI : (J.image (Work.PL.Shell.prefAt l)) ∩ (J'.image (Work.PL.Shell.prefAt l))
      = (J ∩ J').image (Work.PL.Shell.prefAt l) := by
    ext A
    simp only [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨j, hjJ, hjA⟩, ⟨j', hj'J', hj'A⟩⟩
      have hjeq : j = j' :=
        Work.PL.Shell.prefAt_inj hl (hJlen j hjJ) (hJ'len j' hj'J')
          (hjA.trans hj'A.symm)
      exact ⟨j, ⟨hjJ, by rw [hjeq]; exact hj'J'⟩, hjA⟩
    · rintro ⟨j, hj, hjA⟩
      exact ⟨⟨j, hj.1, hjA⟩, ⟨j, hj.2, hjA⟩⟩
  simp only [Work.PL.Sd1.face]
  rw [hinter, hCI]

end Work.PL.Sd1
