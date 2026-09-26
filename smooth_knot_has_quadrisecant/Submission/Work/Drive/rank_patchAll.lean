import Mathlib
import Submission.Work.Drive.rankPatchDefs
import Submission.Work.Drive.rank_patchA
import Submission.Work.Drive.rank_patchM
import Submission.Work.Drive.knobRank
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

/-!
# The patch `P_abm` of the bad locus has differential of rank four

`Work.Drive.rank_patchAll`: at every data point `x : TripleData` with nonzero chord vector
`d = dataP x - dataQ x` and nonzero second tangent–chord vector `dataYb x`, the three patch
conditions `(dataColl, dataYa × dataYb, dataYb × dataYm)` of the patch `P_abm` (all three
tangents parallel modulo the chord) have a differential of rank at least four.

The four independent directions are supplied by three knobs:

* the *position* of the middle point `M`, which moves only the collinearity factor, with
  derivative `u ↦ u × d` of rank two on `d^⊥`;
* the *velocity* at the first point `A`, which moves only the first cross-product factor, with
  derivative `u ↦ (u × d) × y_b`;
* the *velocity* at the middle point `C`, which moves only the second cross-product factor, with
  derivative `u ↦ y_b × (u × d)`.

Each of the last two maps has rank one (its image is the line spanned by `d`, using
`y_b ⊥ d` and `y_b ≠ 0`), and the three knobs act in the three different factors, so their
contributions add: `2 + 1 + 1 = 4`.
-/

open scoped Matrix

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- A function that is constant along an affine line has zero derivative there. -/
lemma hasDerivAt_const_along {F : TripleData → Space} {x e : TripleData}
    (h : ∀ s : ℝ, F (x + s • e) = F x) :
    HasDerivAt (fun s : ℝ => F (x + s • e)) 0 0 := by
  have hconst : (fun s : ℝ => F (x + s • e)) = fun _ => F x := funext h
  rw [hconst]
  exact hasDerivAt_const 0 (F x)

lemma rpl_contDiff_patchAll : ContDiff ℝ 1 patchAll := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h1 : ContDiff ℝ 1
      (fun X : TripleData => (dataP X - dataQ X, dataP X - dataM X)) := by
    unfold dataP dataQ dataM
    fun_prop
  have h2 : ContDiff ℝ 1 (fun X : TripleData => (dataYa X, dataYb X)) := by
    unfold dataYa dataYb dataA dataB dataP dataQ
    fun_prop
  have h3 : ContDiff ℝ 1 (fun X : TripleData => (dataYb X, dataYm X)) := by
    unfold dataYb dataYm dataB dataC dataP dataQ
    fun_prop
  have hp : ContDiff ℝ 1 (fun X : TripleData =>
      (cross3 (dataP X - dataQ X) (dataP X - dataM X),
        (cross3 (dataYa X) (dataYb X), cross3 (dataYb X) (dataYm X)))) :=
    (hcross.comp h1).prodMk ((hcross.comp h2).prodMk (hcross.comp h3))
  have hfun : (fun X : TripleData =>
      (cross3 (dataP X - dataQ X) (dataP X - dataM X),
        (cross3 (dataYa X) (dataYb X), cross3 (dataYb X) (dataYm X)))) = patchAll := rfl
  rw [← hfun]
  exact hp

/-! ## Derivatives along the three knobs -/

lemma rpl_hasDerivAt_Yab_dirM (x : TripleData) (m : Space) :
    HasDerivAt (fun s : ℝ => cross3 (dataYa (x + s • rpa_dirM m)) (dataYb (x + s • rpa_dirM m)))
      (0 : Space) 0 := by
  refine hasDerivAt_const_along
    (F := fun X : TripleData => cross3 (dataYa X) (dataYb X)) (x := x) (e := rpa_dirM m) ?_
  intro s
  simp [dataYa, dataYb, dataP, dataQ, dataA, dataB, rpa_dirM]

lemma rpl_hasDerivAt_Ybm_dirM (x : TripleData) (m : Space) :
    HasDerivAt (fun s : ℝ => cross3 (dataYb (x + s • rpa_dirM m)) (dataYm (x + s • rpa_dirM m)))
      (0 : Space) 0 := by
  refine hasDerivAt_const_along
    (F := fun X : TripleData => cross3 (dataYb X) (dataYm X)) (x := x) (e := rpa_dirM m) ?_
  intro s
  simp [dataYb, dataYm, dataP, dataQ, dataB, dataC, rpa_dirM]

lemma rpl_fderiv_dirM (x : TripleData) (m : Space) :
    (fderiv ℝ patchAll x) (rpa_dirM m)
      = (cross3 m (dataP x - dataQ x), (0 : Space), (0 : Space)) := by
  have hdiff : DifferentiableAt ℝ patchAll x :=
    (rpl_contDiff_patchAll.differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := patchAll) (p := x) (e := rpa_dirM m) hdiff
  have h2 : HasDerivAt (fun s : ℝ => patchAll (x + s • rpa_dirM m))
      (cross3 m (dataP x - dataQ x), (0 : Space), (0 : Space)) 0 := by
    have hp := (rpa_hasDerivAt_dataColl_dirM x m).prodMk
      ((rpl_hasDerivAt_Yab_dirM x m).prodMk (rpl_hasDerivAt_Ybm_dirM x m))
    apply HasDerivAt.congr_of_eventuallyEq hp
    filter_upwards with s
    simp [patchAll]
  exact h1.unique h2

lemma rpl_hasDerivAt_Ybm_dirA (x : TripleData) (a : Space) :
    HasDerivAt (fun s : ℝ => cross3 (dataYb (x + s • rpa_dirA a)) (dataYm (x + s • rpa_dirA a)))
      (0 : Space) 0 := by
  refine hasDerivAt_const_along
    (F := fun X : TripleData => cross3 (dataYb X) (dataYm X)) (x := x) (e := rpa_dirA a) ?_
  intro s
  simp [dataYb, dataYm, dataP, dataQ, dataB, dataC, rpa_dirA]

lemma rpl_hasDerivAt_Yab_dirA (x : TripleData) (a : Space) :
    HasDerivAt (fun s : ℝ => cross3 (dataYa (x + s • rpa_dirA a)) (dataYb (x + s • rpa_dirA a)))
      (cross3 (cross3 a (dataP x - dataQ x)) (dataYb x)) 0 := by
  have h1 := rpa_hasDerivAt_dataYa_dirA x a
  have h2 : HasDerivAt (fun s : ℝ => dataYb (x + s • rpa_dirA a)) (0 : Space) 0 := by
    rw [show (fun s : ℝ => dataYb (x + s • rpa_dirA a)) = fun _ => dataYb x by
      funext s; simp [dataYb, dataP, dataQ, dataB, rpa_dirA]]
    exact hasDerivAt_const 0 (dataYb x)
  have h := hasDerivAt_cross3_curves _ _ h1 h2
  exact h.congr_deriv (by simp [cross3_zero_right, cross3_zero_left])

lemma rpl_fderiv_dirA (x : TripleData) (a : Space) :
    (fderiv ℝ patchAll x) (rpa_dirA a)
      = ((0 : Space), cross3 (cross3 a (dataP x - dataQ x)) (dataYb x), (0 : Space)) := by
  have hdiff : DifferentiableAt ℝ patchAll x :=
    (rpl_contDiff_patchAll.differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := patchAll) (p := x) (e := rpa_dirA a) hdiff
  have h2 : HasDerivAt (fun s : ℝ => patchAll (x + s • rpa_dirA a))
      ((0 : Space), cross3 (cross3 a (dataP x - dataQ x)) (dataYb x), (0 : Space)) 0 := by
    have hp := (rpa_hasDerivAt_dataColl_dirA x a).prodMk
      ((rpl_hasDerivAt_Yab_dirA x a).prodMk (rpl_hasDerivAt_Ybm_dirA x a))
    apply HasDerivAt.congr_of_eventuallyEq hp
    filter_upwards with s
    simp [patchAll]
  exact h1.unique h2

lemma rpl_hasDerivAt_Yab_dirC (x : TripleData) (c : Space) :
    HasDerivAt (fun s : ℝ => cross3 (dataYa (x + s • rpm_dirC c)) (dataYb (x + s • rpm_dirC c)))
      (0 : Space) 0 := by
  refine hasDerivAt_const_along
    (F := fun X : TripleData => cross3 (dataYa X) (dataYb X)) (x := x) (e := rpm_dirC c) ?_
  intro s
  simp [dataYa, dataYb, dataP, dataQ, dataA, dataB, rpm_dirC]

lemma rpl_hasDerivAt_Ybm_dirC (x : TripleData) (c : Space) :
    HasDerivAt (fun s : ℝ => cross3 (dataYb (x + s • rpm_dirC c)) (dataYm (x + s • rpm_dirC c)))
      (cross3 (dataYb x) (cross3 c (dataP x - dataQ x))) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => dataYb (x + s • rpm_dirC c)) (0 : Space) 0 := by
    rw [show (fun s : ℝ => dataYb (x + s • rpm_dirC c)) = fun _ => dataYb x by
      funext s; simp [dataYb, dataP, dataQ, dataB, rpm_dirC]]
    exact hasDerivAt_const 0 (dataYb x)
  have h2 := rpm_hasDerivAt_dataYm_dirC x c
  have h := hasDerivAt_cross3_curves _ _ h1 h2
  exact h.congr_deriv (by simp [cross3_zero_right, cross3_zero_left])

lemma rpl_fderiv_dirC (x : TripleData) (c : Space) :
    (fderiv ℝ patchAll x) (rpm_dirC c)
      = ((0 : Space), (0 : Space), cross3 (dataYb x) (cross3 c (dataP x - dataQ x))) := by
  have hdiff : DifferentiableAt ℝ patchAll x :=
    (rpl_contDiff_patchAll.differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := patchAll) (p := x) (e := rpm_dirC c) hdiff
  have h2 : HasDerivAt (fun s : ℝ => patchAll (x + s • rpm_dirC c))
      ((0 : Space), (0 : Space), cross3 (dataYb x) (cross3 c (dataP x - dataQ x))) 0 := by
    have hp := (rpm_hasDerivAt_dataColl_dirC x c).prodMk
      ((rpl_hasDerivAt_Yab_dirC x c).prodMk (rpl_hasDerivAt_Ybm_dirC x c))
    apply HasDerivAt.congr_of_eventuallyEq hp
    filter_upwards with s
    simp [patchAll]
  exact h1.unique h2

/-! ## The rank of the patch -/

theorem rank_patchAll (x : Work.Drive.TripleData)
    (hd : Work.Drive.dataP x - Work.Drive.dataQ x ≠ 0)
    (hcol : Work.Drive.dataColl x = 0)
    (hyb : Work.Drive.dataYb x ≠ 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ Work.Drive.patchAll x).toLinearMap)) := by
  set D : TripleData →ₗ[ℝ] Space × Space × Space := (fderiv ℝ patchAll x).toLinearMap with hD
  set f₁ : Space →ₗ[ℝ] Space := rpa_crossLin (dataP x - dataQ x) with hf₁
  set f₂ : Space →ₗ[ℝ] Space := crossCross (dataYb x) (dataP x - dataQ x) with hf₂
  have horth : inner ℝ (dataYb x) (dataP x - dataQ x) = 0 := by
    show inner ℝ (cross3 (dataB x) (dataP x - dataQ x)) (dataP x - dataQ x) = 0
    exact inner_cross3_right (dataB x) (dataP x - dataQ x)
  have hrank₁ : Module.finrank ℝ (LinearMap.range f₁) = 2 := by
    rw [hf₁]; exact rpa_finrank_range_crossLin hd
  have hrank₂ : Module.finrank ℝ (LinearMap.range f₂) = 1 := by
    rw [hf₂]; exact finrank_range_crossCross hyb hd horth
  have h₁ : ∀ u : Space, D (rpa_dirM u) = (f₁ u, 0, 0) := by
    intro u
    rw [hD]
    change (fderiv ℝ patchAll x) (rpa_dirM u) = (f₁ u, 0, 0)
    rw [rpl_fderiv_dirM x u]
    rfl
  have h₂ : ∀ u : Space, D (rpa_dirA u) = (0, (-f₂) u, 0) := by
    intro u
    rw [hD]
    change (fderiv ℝ patchAll x) (rpa_dirA u) = ((0 : Space), (-f₂) u, (0 : Space))
    rw [rpl_fderiv_dirA x u]
    simp only [Pi.neg_apply, hf₂, crossCross_apply]
    rw [cross3_anticomm (dataYb x) (cross3 u (dataP x - dataQ x))]
    rfl
  have h₃ : ∀ u : Space, D (rpm_dirC u) = (0, 0, f₂ u) := by
    intro u
    rw [hD]
    change (fderiv ℝ patchAll x) (rpm_dirC u) = (0, 0, f₂ u)
    rw [rpl_fderiv_dirC x u]
    rfl
  have hrank₂' : Module.finrank ℝ (LinearMap.range (-f₂)) = 1 := by
    rw [LinearMap.range_neg]; exact hrank₂
  have := three_knob_rank (D := D) (f₁ := f₁) (f₂ := -f₂) (f₃ := f₂)
    rpa_dirM rpa_dirA rpm_dirC h₁ h₂ h₃
  rw [hrank₁, hrank₂', hrank₂] at this
  omega

end

end Work.Drive
