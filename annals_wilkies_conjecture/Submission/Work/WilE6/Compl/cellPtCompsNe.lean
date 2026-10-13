import Mathlib
import Submission.Work.WilE5.Cells.khovCount
import Submission.Work.WilE5.Cells.cellBasic
import Submission.Work.WilE6.Compl.cellPtKhovSet

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE6.Compl

open WilkiesDesign WilkiesDesign.E

/-! ## Separating the chosen points of two distinct sign cells

`Work.WilE5.Cells.khovCellPt X σ` is a point of the (possibly empty) sign cell of `σ`, and
`Work.WilE5.Cells.khovSet X ε` is the semi-Pfaffian set on which every perturbed atom
`(f + ε)² (f - ε)²` is positive, i.e. whose members avoid all the hyper-surfaces `f = ±ε`.

If `ε` is smaller than `|f_i (khovCellPt X σ)|` for every atom `f_i` that does not vanish there,
then the chosen point of a nonempty cell lies in `khovSet X ε` (this is
`Work.WilE6.Compl.cellPtKhovSet`), and two chosen points of *different* nonempty cells lie in
*different* connected components of `khovSet X ε`.

The reason is the intermediate value theorem on the connected component: the two points have
different signs of some atom `f_i` there, so the values of `f_i` at them are separated by the
threshold `±ε` (this is the elementary `KhovSignData` cross argument); a connected component of
`khovSet X ε` would therefore contain a point where `f_i = ε` or `f_i = -ε`, which is impossible
because such a point violates the positivity of the perturbed atom of `f_i`. -/

/-- **Sign data of a chosen cell point.** At the chosen point of a nonempty sign cell `σ` of `X`,
every atom `f_i` satisfies the sign condition recorded by `σ` in the *robust* form
`KhovSignData`: `σ i = zero` gives `f_i = 0`, while `σ i = pos` (resp. `neg`) gives
`ε < f_i` (resp. `f_i < -ε`), because `ε` is below the absolute value of every nonvanishing
atom value at that point. -/
theorem khovSignData_cellPt {k : ℕ} (X : WilkiesDesign.E.SemiPf k) {ε : ℝ}
    (hsmall : ∀ (i : Fin (Work.WilE5.atomsOf X).length)
      (σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign),
      WilkiesDesign.E.eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ) ≠ 0 →
      ε < |WilkiesDesign.E.eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ)|)
    {σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign}
    (hσ : (Work.WilE5.cellSemiPf X σ).set.Nonempty) (i : Fin (Work.WilE5.atomsOf X).length) :
    Work.WilE5.Cells.KhovSignData (σ i)
      (WilkiesDesign.E.eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ)) ε := by
  have hpt : Work.WilE5.Cells.khovCellPt X σ ∈ (Work.WilE5.cellSemiPf X σ).set :=
    Work.WilE5.Cells.khovCellPt_mem X σ hσ
  refine Work.WilE5.Cells.KhovSignData.of_sign (fun hz => ?_) (fun hp => ?_) (fun hn => ?_)
  · exact Work.WilE5.Cells.khovCell_zero X σ hpt hz
  · have hpos := Work.WilE5.Cells.khovCell_pos X σ hpt hp
    have h := hsmall i σ (ne_of_gt hpos)
    rwa [abs_of_pos hpos] at h
  · have hneg := Work.WilE5.Cells.khovCell_neg X σ hpt hn
    have h := hsmall i σ (ne_of_lt hneg)
    rw [abs_of_neg hneg] at h
    linarith

theorem cellPtCompsNe {k : ℕ} (X : WilkiesDesign.E.SemiPf k) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ (i : Fin (Work.WilE5.atomsOf X).length)
      (σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign),
      WilkiesDesign.E.eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ) ≠ 0 →
      ε < |WilkiesDesign.E.eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ)|)
    {σ τ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign}
    (hσ : (Work.WilE5.cellSemiPf X σ).set.Nonempty)
    (hτ : (Work.WilE5.cellSemiPf X τ).set.Nonempty) (hne : σ ≠ τ) :
    connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
        (Work.WilE5.Cells.khovCellPt X σ) ≠
      connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
        (Work.WilE5.Cells.khovCellPt X τ) := by
  intro heq
  -- a coordinate in which the two sign assignments differ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hne (funext hc)
  have hσmem : Work.WilE5.Cells.khovCellPt X σ ∈ (Work.WilE5.Cells.khovSet X ε).set :=
    cellPtKhovSet X hε hsmall hσ
  have hτmem : Work.WilE5.Cells.khovCellPt X τ ∈ (Work.WilE5.Cells.khovSet X ε).set :=
    cellPtKhovSet X hε hsmall hτ
  have hApre : IsPreconnected
      (connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
        (Work.WilE5.Cells.khovCellPt X σ)) :=
    isPreconnected_connectedComponentIn
  have hτA : Work.WilE5.Cells.khovCellPt X τ ∈
      connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
        (Work.WilE5.Cells.khovCellPt X σ) := by
    rw [heq]
    exact mem_connectedComponentIn hτmem
  have hcont : ContinuousOn (fun z : Fin k → ℝ => eaEval X.c ((Work.WilE5.atomsOf X).get i) z)
      (connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
        (Work.WilE5.Cells.khovCellPt X σ)) :=
    (Work.WilE5.Cells.khovEaEval_continuous X.c ((Work.WilE5.atomsOf X).get i)).continuousOn
  -- on the whole component the `i`-th atom avoids both thresholds
  have key : ∀ z ∈ connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
        (Work.WilE5.Cells.khovCellPt X σ),
      eaEval X.c ((Work.WilE5.atomsOf X).get i) z ≠ ε ∧
        eaEval X.c ((Work.WilE5.atomsOf X).get i) z ≠ -ε := by
    intro z hzA
    have hzY : z ∈ (Work.WilE5.Cells.khovSet X ε).set := connectedComponentIn_subset _ _ hzA
    have hgmem : Work.WilE5.Cells.khovAt ((Work.WilE5.atomsOf X).get i) ε
        ∈ Work.WilE5.Cells.khovAtoms X ε := by
      rw [Work.WilE5.Cells.khovAtoms, List.mem_map]
      exact ⟨_, List.get_mem _ _, rfl⟩
    have hpos := ((Work.WilE5.Cells.khovSet_mem X ε z).mp hzY).2 _ hgmem
    rwa [Work.WilE5.Cells.khovAt_pos] at hpos
  -- the intermediate value theorem on the component
  have reach : ∀ w : ℝ,
      ((eaEval X.c ((Work.WilE5.atomsOf X).get i) (Work.WilE5.Cells.khovCellPt X σ) ≤ w ∧
          w ≤ eaEval X.c ((Work.WilE5.atomsOf X).get i) (Work.WilE5.Cells.khovCellPt X τ)) ∨
        (eaEval X.c ((Work.WilE5.atomsOf X).get i) (Work.WilE5.Cells.khovCellPt X τ) ≤ w ∧
          w ≤ eaEval X.c ((Work.WilE5.atomsOf X).get i) (Work.WilE5.Cells.khovCellPt X σ))) →
      ∃ z ∈ connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
          (Work.WilE5.Cells.khovCellPt X σ),
        eaEval X.c ((Work.WilE5.atomsOf X).get i) z = w := by
    intro w hw
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (Set.mem_image _ _ _).mp
        (hApre.intermediate_value (mem_connectedComponentIn hσmem) hτA hcont ⟨h1, h2⟩)
    · exact (Set.mem_image _ _ _).mp
        (hApre.intermediate_value hτA (mem_connectedComponentIn hσmem) hcont ⟨h1, h2⟩)
  have hsdσ := khovSignData_cellPt X hsmall hσ i
  have hsdτ := khovSignData_cellPt X hsmall hτ i
  have hcross := Work.WilE5.Cells.khovSignData_cross hi hε hsdσ hsdτ
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨z, hzA, hz⟩ := reach ε (Or.inl ⟨h1, h2⟩)
    exact (key z hzA).1 hz
  · obtain ⟨z, hzA, hz⟩ := reach ε (Or.inr ⟨h1, h2⟩)
    exact (key z hzA).1 hz
  · obtain ⟨z, hzA, hz⟩ := reach (-ε) (Or.inl ⟨h1, h2⟩)
    exact (key z hzA).2 hz
  · obtain ⟨z, hzA, hz⟩ := reach (-ε) (Or.inr ⟨h1, h2⟩)
    exact (key z hzA).2 hz

end Work.WilE6.Compl
