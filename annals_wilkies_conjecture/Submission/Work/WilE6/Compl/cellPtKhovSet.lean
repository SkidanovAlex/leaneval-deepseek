import Mathlib
import Submission.Work.WilE5.Cells.khovCount
import Submission.Work.WilE5.Cells.cellBasic

namespace Work.WilE6.Compl

/-- The elementary arithmetic fact behind `cellPtKhovSet`: a real number which is either `0`
or has absolute value `> ε` is different from both `ε` and `-ε`. -/
theorem ne_pm_eps_of_abs {a ε : ℝ} (hε : 0 < ε) (ha : a ≠ 0 → ε < |a|) :
    a ≠ ε ∧ a ≠ -ε := by
  constructor
  · intro h
    have h1 : ε < |a| := ha (by rw [h]; exact hε.ne')
    rw [h, abs_of_pos hε] at h1
    exact absurd h1 (lt_irrefl ε)
  · intro h
    have h1 : ε < |a| := ha (by rw [h]; exact neg_ne_zero.mpr hε.ne')
    rw [h, abs_neg, abs_of_pos hε] at h1
    exact absurd h1 (lt_irrefl ε)

theorem cellPtKhovSet {k : ℕ} (X : WilkiesDesign.E.SemiPf k) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ (i : Fin (Work.WilE5.atomsOf X).length)
      (σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign),
      WilkiesDesign.E.eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ) ≠ 0 →
      ε < |WilkiesDesign.E.eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ)|)
    {σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign}
    (hne : (Work.WilE5.cellSemiPf X σ).set.Nonempty) :
    Work.WilE5.Cells.khovCellPt X σ ∈ (Work.WilE5.Cells.khovSet X ε).set := by
  have hpt : Work.WilE5.Cells.khovCellPt X σ ∈ (Work.WilE5.cellSemiPf X σ).set :=
    Work.WilE5.Cells.khovCellPt_mem X σ hne
  have hcube : Work.WilE5.Cells.khovCellPt X σ ∈ WilkiesDesign.E.cubeC k :=
    Work.WilE5.semiPf_set_subset_cube (Work.WilE5.cellSemiPf X σ) hpt
  rw [Work.WilE5.Cells.khovSet_mem]
  refine ⟨hcube, ?_⟩
  intro g hg
  rw [Work.WilE5.Cells.khovAtoms, List.mem_map] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  rw [Work.WilE5.Cells.khovAt_pos]
  rw [List.mem_iff_get] at hf
  obtain ⟨i, hi⟩ := hf
  subst hi
  exact ne_pm_eps_of_abs hε (hsmall i σ)

end Work.WilE6.Compl
