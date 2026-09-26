import Mathlib
import Submission.Work.Smooth.JordanSeparation.plCutLoop
import Submission.Work.Smooth.JordanSeparation.plCutCast
import Submission.Work.Smooth.JordanSeparation.plCut

/-!
# Assembling the induction step of (B)

`joinNat_cut` (`plCutLoop`) splits the polygonal loop at a repeated vertex; the two casts on the
middle and right pieces (`plCutCast`) relate that split to the loop configuration of
`nullhomotopic_trans_trans_of_nullhomotopic` (`plCut`).  This file packages the two
cast-distribution identities needed and the resulting induction step.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **A cast outside a concatenation, start unchanged.** -/
theorem cast_trans_same {x z y y' : X} (A : Path x z) (B : Path z y) (h : y' = y) :
    Path.cast (A.trans B) rfl h = A.trans (Path.cast B rfl h) := by
  ext t
  rw [path_cast_apply, Path.trans_apply, Path.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [dif_pos ht]
  · simp only [dif_neg ht]
    exact path_cast_apply B rfl h _

/-- **A cast outside a concatenation, acting on both factors**: the cast re-labels the end of the
first factor and the start of the second along the same equality. -/
theorem cast_trans_labelled {x z y y' : X} (M : Path x z) (B : Path z y) (hs : x = z)
    (h : y' = y) :
    Path.cast (M.trans B) rfl h = (Path.cast M rfl hs).trans (Path.cast B hs h) := by
  ext t
  rw [path_cast_apply, Path.trans_apply, Path.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [dif_pos ht]
    exact path_cast_apply M rfl hs _
  · simp only [dif_neg ht]
    exact path_cast_apply B hs h _

/-- **The induction step of (B).**  If the middle piece of the cut is null-homotopic as a loop at
`p i` (after the double-point cast) and the complementary loop is null-homotopic at `p 0`, then so
is the whole polygonal loop. -/
theorem nullhomotopic_of_joinNat_cut {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) {i j k : ℕ}
    (hpt : p i = p (i + j)) (hclosed : p (i + (j + k)) = p 0)
    (hδ : Path.Homotopic
      (Path.cast (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) j) rfl hpt)
      (Path.refl (p i)))
    (hαβ : Path.Homotopic
      ((joinNat F i).trans
        (Path.cast (joinNat (p := fun l => p (i + (j + l))) (fun l => F (i + (j + l))) k)
          hpt hclosed.symm))
      (Path.refl (p 0))) :
    Path.Homotopic (Path.cast (joinNat F (i + (j + k))) rfl hclosed.symm) (Path.refl (p 0)) := by
  refine (Path.Homotopic.pathCast (joinNat_cut F i j k) rfl hclosed.symm).trans ?_
  rw [cast_trans_same, cast_trans_labelled]
  exact nullhomotopic_trans_trans_of_nullhomotopic (joinNat F i)
    (Path.cast (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) j) rfl hpt)
    (Path.cast (joinNat (p := fun l => p (i + (j + l))) (fun l => F (i + (j + l))) k) hpt hclosed.symm)
    hδ hαβ

end

end Work.Smooth.JordanSeparation
