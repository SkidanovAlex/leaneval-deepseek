import Mathlib
import Submission.Work.Drive.rankPatchDefs
import Submission.Work.Drive.rank_patchA
import Submission.Work.Drive.knobRank
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

/-!
# The patch `P_b` of the bad locus has differential of rank four

`Work.Drive.rank_patchB`: at every data point `x : TripleData` with nonzero chord vector
`d = dataP x - dataQ x`, the two patch conditions `(dataColl, dataYb)` of patch `P_b` have a
differential of rank at least four.

Exactly as for patch `P_a` (`Work.Drive.rank_patchA`), the four independent directions are
supplied by two "knobs": the *position* of the middle point `M` (two dimensions in the
collinearity factor) and the *velocity* at the second point `B` (two dimensions in the
tangent–chord factor).  The additive rank statement is the generic lemma
`Work.Drive.two_knob_rank`.
-/

open scoped Matrix

set_option linter.unusedVariables false

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The data perturbation that changes the velocity at the second point: `(0, 0, 0, 0, b, 0)`. -/
def rpb_dirB (b : Space) : TripleData := (0, 0, 0, 0, b, 0)

lemma rpb_contDiff_patchB : ContDiff ℝ 1 patchB := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h1 : ContDiff ℝ 1
      (fun X : TripleData => (dataP X - dataQ X, dataP X - dataM X)) := by
    unfold dataP dataQ dataM
    fun_prop
  have h2 : ContDiff ℝ 1 (fun X : TripleData => (dataB X, dataP X - dataQ X)) := by
    unfold dataB dataP dataQ
    fun_prop
  have hp := (hcross.comp h1).prodMk (hcross.comp h2)
  unfold patchB dataColl dataYb
  exact hp

lemma rpb_hasDerivAt_dataYb_dirM (x : TripleData) (m : Space) :
    HasDerivAt (fun s : ℝ => dataYb (x + s • rpa_dirM m)) (0 : Space) 0 := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0 : ℝ) (dataYb x))
  filter_upwards with s
  simp [dataYb, dataP, dataQ, dataB, rpa_dirM]

lemma rpb_hasDerivAt_dataColl_dirB (x : TripleData) (b : Space) :
    HasDerivAt (fun s : ℝ => dataColl (x + s • rpb_dirB b)) (0 : Space) 0 := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0 : ℝ) (dataColl x))
  filter_upwards with s
  simp [dataColl, dataP, dataQ, dataM, rpb_dirB]

lemma rpb_hasDerivAt_dataYb_dirB (x : TripleData) (b : Space) :
    HasDerivAt (fun s : ℝ => dataYb (x + s • rpb_dirB b))
      (cross3 b (dataP x - dataQ x)) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => s • b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const b
  have hu : HasDerivAt (fun s : ℝ => dataB x + s • b) b 0 := hbase.const_add (dataB x)
  have hv : HasDerivAt (fun _ : ℝ => dataP x - dataQ x) (0 : Space) 0 :=
    hasDerivAt_const 0 _
  have h := hasDerivAt_cross3_curves _ _ hu hv
  have h' : HasDerivAt (fun s : ℝ => dataYb (x + s • rpb_dirB b))
      (cross3 b (dataP x - dataQ x) + cross3 (dataB x + (0 : ℝ) • b) (0 : Space)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq h
    filter_upwards with s
    simp [dataYb, dataP, dataQ, dataB, rpb_dirB]
  apply HasDerivAt.congr_deriv h'
  rw [cross3_zero_right, add_zero]

lemma rpb_fderiv_dirM (x : TripleData) (m : Space) :
    (fderiv ℝ patchB x) (rpa_dirM m)
      = (cross3 m (dataP x - dataQ x), (0 : Space)) := by
  have hdiff : DifferentiableAt ℝ patchB x :=
    (rpb_contDiff_patchB.differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := patchB) (p := x) (e := rpa_dirM m) hdiff
  have h2 : HasDerivAt (fun s : ℝ => patchB (x + s • rpa_dirM m))
      (cross3 m (dataP x - dataQ x), (0 : Space)) 0 := by
    have hp := (rpa_hasDerivAt_dataColl_dirM x m).prodMk (rpb_hasDerivAt_dataYb_dirM x m)
    apply HasDerivAt.congr_of_eventuallyEq hp
    filter_upwards with s
    simp [patchB]
  exact h1.unique h2

lemma rpb_fderiv_dirB (x : TripleData) (b : Space) :
    (fderiv ℝ patchB x) (rpb_dirB b)
      = ((0 : Space), cross3 b (dataP x - dataQ x)) := by
  have hdiff : DifferentiableAt ℝ patchB x :=
    (rpb_contDiff_patchB.differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := patchB) (p := x) (e := rpb_dirB b) hdiff
  have h2 : HasDerivAt (fun s : ℝ => patchB (x + s • rpb_dirB b))
      ((0 : Space), cross3 b (dataP x - dataQ x)) 0 := by
    have hp := (rpb_hasDerivAt_dataColl_dirB x b).prodMk (rpb_hasDerivAt_dataYb_dirB x b)
    apply HasDerivAt.congr_of_eventuallyEq hp
    filter_upwards with s
    simp [patchB]
  exact h1.unique h2

theorem rank_patchB (x : Work.Drive.TripleData)
    (hd : Work.Drive.dataP x - Work.Drive.dataQ x ≠ 0)
    (hcol : Work.Drive.dataColl x = 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ Work.Drive.patchB x).toLinearMap)) := by
  set D : TripleData →ₗ[ℝ] Space × Space := (fderiv ℝ patchB x).toLinearMap with hD
  set f : Space →ₗ[ℝ] Space := rpa_crossLin (dataP x - dataQ x) with hf
  have hfr : Module.finrank ℝ (LinearMap.range f) = 2 := by
    rw [hf]
    exact rpa_finrank_range_crossLin hd
  have h₁ : ∀ u : Space, D (rpa_dirM u) = (f u, 0) := by
    intro u
    rw [hD]
    change (fderiv ℝ patchB x) (rpa_dirM u) = (f u, 0)
    rw [rpb_fderiv_dirM x u]
    rfl
  have h₂ : ∀ u : Space, D (rpb_dirB u) = (0, f u) := by
    intro u
    rw [hD]
    change (fderiv ℝ patchB x) (rpb_dirB u) = ((0 : Space), f u)
    rw [rpb_fderiv_dirB x u]
    rfl
  have := two_knob_rank (D := D) (f := f) rpa_dirM rpb_dirB h₁ h₂
  rw [hfr] at this
  omega

end

end Work.Drive
