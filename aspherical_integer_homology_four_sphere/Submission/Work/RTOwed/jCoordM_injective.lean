/-
# Injectivity of the junction coordinate inclusion `jCoordM`

`Work.RTOwed.jCoordM a v D cU k W kx δ` sends a point `q` of the junction box
`Work.RTOwed.jBox v cU k W kx δ` (polar coordinates `(r,θ,w₁,w₂)`) to `M̂`: for `q 0 ≤ r_J` it is
the point of the filling piece recovered by the inverse polar chart, and for `r_J < q 0` it is the
collar coordinate inclusion `cuspCoordMTop` applied to `polarToUHS v q`.

This file proves that it is injective.  The three cases are:

* **both points on the inner half `q 0 ≤ r_J`**: `incW v` is injective, so the points
  `cuspInvInner v q` of `E2 × E2` agree up to the period `ℤ²` of the filling piece; the section
  hypothesis `hsec` (the `w`-coordinates determine the torus lift) pins the lift, and the round trip
  `ThetaPolarS_cuspInvInner` recovers `q`;
* **both points on the collar half `r_J < q 0`**: `cuspCoordMTop` is injective on its box
  (`δ ≤ 1/2`) and `polarToUHS` is injective;
* **mixed** (one on each half): if the collar point lies *below* the ceiling then its value is
  `incMbar ∘ mbarLow`, which can only meet a filling point on the truncation torus `Tset`, where
  `mbarLow` does not take values strictly below the ceiling; if it lies *on or above* the ceiling
  then its value is the filling point of layer parameter `> 1/2`, while the inner point has layer
  parameter `≤ 1/2`.
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.RTOwed.cuspInvOuter_polarToUHS_eq
import Submission.Work.RTOwed.polarToUHS_isOpenEmbedding
import Submission.Work.Cusp.cuspCoordMTop_injective
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.wOf_invY
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.cuspCoordM_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped RealInnerProductSpace

namespace Work.RTOWed

/-! ### The layer parameters of the two branches -/

/-- On the inner half `q 0 ≤ r_J` the filling point recovered by the polar inverse has sup norm
`q 0 / (2 r_J)`. -/
private theorem jnrm_cuspInvInner {v : Work.Space.Cusp} {q : Work.Cusp.E4}
    (hq0 : 1 / 4 < q 0) (h : q 0 ≤ Work.Cusp.rJ) :
    Work.Cusp.nrm (Work.Cusp.cuspInvInner v q).1 = q 0 / (2 * Work.Cusp.rJ) := by
  have hpos : 0 < q 0 := lt_trans (by norm_num) hq0
  have hrJ : (0 : ℝ) < 2 * Work.Cusp.rJ := by norm_num [Work.Cusp.rJ]
  simp only [Work.Cusp.cuspInvInner]
  rw [ite_eq_left h, Work.Cusp.nrm_smul, Work.Cusp.nrm_bndOfU, mul_one,
    abs_of_pos (div_pos hpos hrJ)]

/-- On or above the ceiling of the collar box (with height below the junction height `s_J`) the
filling point recovered by the collar inverse has sup norm strictly `> 1/2`. -/
private theorem jnrm_cuspInvOuter_gt_half {v : Work.Space.Cusp} {x : Work.Cusp.E4}
    (h1 : Work.Cusp.s1 < x 3) (h2 : x 3 < Work.Cusp.sJ) :
    1 / 2 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v x).1 := by
  set b : ℝ := Work.Cusp.beta (Work.Cusp.xOf x) with hb
  have hxpos : 0 < x 3 := lt_trans (by norm_num [Work.Cusp.s1]) h1
  have hbpos : 0 < b := by rw [hb]; exact Work.Cusp.beta_pos _
  have hblt : b < Work.Cusp.sJ := by
    rw [hb]; exact lt_of_le_of_lt (Work.Cusp.beta_le_max _) Work.Cusp.betaMax_lt_sJ
  have hlogx : Real.log (x 3) < Real.log Work.Cusp.sJ := Real.log_lt_log hxpos h2
  have hlogb : Real.log b < Real.log Work.Cusp.sJ := Real.log_lt_log hbpos hblt
  have hne : Real.log b - Real.log Work.Cusp.sJ ≠ 0 := by linarith
  have hD : (2 : ℝ) * (Real.log b - Real.log Work.Cusp.sJ) ≠ 0 :=
    mul_ne_zero (by norm_num) hne
  rw [Work.Cusp.cuspInvOuter_nrm_fst, ← hb]
  have hkey : (1 + (Real.log (x 3) - Real.log b) / (2 * (Real.log b - Real.log Work.Cusp.sJ)))
      - 1 / 2
      = (Real.log (x 3) - Real.log Work.Cusp.sJ) / (2 * (Real.log b - Real.log Work.Cusp.sJ)) := by
    field_simp
    ring
  have hpos : 0 < (Real.log (x 3) - Real.log Work.Cusp.sJ)
      / (2 * (Real.log b - Real.log Work.Cusp.sJ)) :=
    div_pos_of_neg_of_neg (by linarith) (by linarith)
  have ht : 1 / 2 < 1 + (Real.log (x 3) - Real.log b)
      / (2 * (Real.log b - Real.log Work.Cusp.sJ)) := by linarith
  exact lt_of_lt_of_le ht (le_abs_self _)

/-! ### The three cases of the injectivity -/

/-- **Both points on the inner half.** -/
private theorem jCoordM_inj_inner (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (q q' : {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v cU k W kx δ})
    (h1 : q.1 0 ≤ Work.Cusp.rJ) (h2 : q'.1 0 ≤ Work.Cusp.rJ)
    (h : Work.RTOwed.jCoordM a v D cU k W kx δ q
      = Work.RTOwed.jCoordM a v D cU k W kx δ q') : q = q' := by
  unfold Work.RTOwed.jCoordM at h
  rw [dite_eq_left h1, dite_eq_left h2] at h
  have hpair := a.incW_injective v h
  have hp : (Work.Cusp.cuspInvInner v q.1).1 = (Work.Cusp.cuspInvInner v q'.1).1 := by
    have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : Work.Cusp.E2)) hpair
    simpa using hc
  have hy : ∀ i, (((Work.Cusp.cuspInvInner v q.1).2 i : ℝ) : AddCircle (1 : ℝ))
      = (((Work.Cusp.cuspInvInner v q'.1).2 i : ℝ) : AddCircle (1 : ℝ)) := by
    have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpair
    have hc' := Homeomorph.injective D.tor.symm hc
    intro i
    exact congrFun hc' i
  have hw1 : Work.Cusp.wOf v (Work.Cusp.cuspInvInner v q.1).2 ∈ W := by
    have hc : Work.Cusp.wOf v (Work.Cusp.cuspInvInner v q.1).2
        = (!₂[q.1 2, q.1 3] : Work.Cusp.E2) := by
      unfold Work.Cusp.cuspInvInner
      exact Work.Cusp.wOf_invY v (!₂[q.1 2, q.1 3] : Work.Cusp.E2)
    rw [hc]
    exact q.2.2.2.1
  have hw2 : Work.Cusp.wOf v (Work.Cusp.cuspInvInner v q'.1).2 ∈ W := by
    have hc : Work.Cusp.wOf v (Work.Cusp.cuspInvInner v q'.1).2
        = (!₂[q'.1 2, q'.1 3] : Work.Cusp.E2) := by
      unfold Work.Cusp.cuspInvInner
      exact Work.Cusp.wOf_invY v (!₂[q'.1 2, q'.1 3] : Work.Cusp.E2)
    rw [hc]
    exact q'.2.2.2.1
  have hyeq : (Work.Cusp.cuspInvInner v q.1).2 = (Work.Cusp.cuspInvInner v q'.1).2 :=
    hsec _ _ hw1 hw2 hy
  have hrt1 : Work.Cusp.ThetaPolarS v cU (Work.Cusp.cuspInvInner v q.1).1
      (Work.Cusp.cuspInvInner v q.1).2 = q.1 :=
    Work.Cusp.ThetaPolarS_cuspInvInner v cU q.1
      (Work.RTOwed.jBox_subset_polarBox v cU k W kx δ q.2) q.2.2.2.2.1
  have hrt2 : Work.Cusp.ThetaPolarS v cU (Work.Cusp.cuspInvInner v q'.1).1
      (Work.Cusp.cuspInvInner v q'.1).2 = q'.1 :=
    Work.Cusp.ThetaPolarS_cuspInvInner v cU q'.1
      (Work.RTOwed.jBox_subset_polarBox v cU k W kx δ q'.2) q'.2.2.2.2.1
  exact Subtype.ext (by rw [← hrt1, ← hrt2, hp, hyeq])

/-- **Both points on the collar half.** -/
private theorem jCoordM_inj_outer (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1 / 2)
    (q q' : {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v cU k W kx δ})
    (h1 : ¬ q.1 0 ≤ Work.Cusp.rJ) (h2 : ¬ q'.1 0 ≤ Work.Cusp.rJ)
    (h : Work.RTOwed.jCoordM a v D cU k W kx δ q
      = Work.RTOwed.jCoordM a v D cU k W kx δ q') : q = q' := by
  unfold Work.RTOwed.jCoordM at h
  rw [dite_eq_right h1, dite_eq_right h2] at h
  have hsub := Work.Cusp.cuspCoordMTop_injective a v D kx δ hδ h
  have hx : Work.Cusp.polarToUHS v q.1 = Work.Cusp.polarToUHS v q'.1 :=
    congrArg (fun z : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v kx δ} => z.1) hsub
  exact Subtype.ext ((Work.RTOWed.polarToUHS_isOpenEmbedding v).injective hx)

/-- **One point on each half** (`q` inner, `q'` collar). -/
private theorem jCoordM_inj_mixed (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ)
    (q q' : {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v cU k W kx δ})
    (h1 : q.1 0 ≤ Work.Cusp.rJ) (h2 : ¬ q'.1 0 ≤ Work.Cusp.rJ)
    (h : Work.RTOwed.jCoordM a v D cU k W kx δ q
      = Work.RTOwed.jCoordM a v D cU k W kx δ q') : q = q' := by
  have hq1 : Work.Cusp.rJ < q'.1 0 := not_le.mp h2
  have hbox' : Work.Cusp.polarToUHS v q'.1 ∈ Work.Cusp.cuspBoxTop v kx δ :=
    Work.RTOwed.polarToUHS_mem_cuspBoxTop v kx δ q'.2.2.2.2.2.2 hq1 q'.2.2.1
  have hx3 : (Work.Cusp.polarToUHS v q'.1) 3 < Work.Cusp.sJ := by
    rw [Work.RTOwed.polarToUHS_three v q'.1,
      show Work.Cusp.sJ = Real.exp (Work.Cusp.R0 - Work.Cusp.rJ) from by
        norm_num [Work.Cusp.sJ, Work.Cusp.R0, Work.Cusp.rJ]]
    exact Real.exp_lt_exp.mpr (by linarith)
  unfold Work.RTOwed.jCoordM at h
  rw [dite_eq_left h1, dite_eq_right h2] at h
  by_cases hlt : (Work.Cusp.polarToUHS v q'.1) 3 < Work.Cusp.beta (Work.Cusp.xOf (Work.Cusp.polarToUHS v q'.1))
  · -- below the ceiling: the collar point is a point of the hyperbolic piece
    unfold Work.Cusp.cuspCoordMTop at h
    rw [dite_eq_left hlt] at h
    obtain ⟨hxT, -⟩ := Work.Cusp.incMbar_eq_incW_imp a v h.symm
    exact absurd hxT (D.mbarLow_not_TsetTop kx δ hbox' hlt)
  · -- on or above the ceiling: the collar point has layer parameter `> 1/2`
    unfold Work.Cusp.cuspCoordMTop at h
    rw [dite_eq_right hlt] at h
    have hpair := a.incW_injective v h
    have hE : (Work.Cusp.cuspInvInner v q.1).1
        = (Work.Cusp.cuspInvOuter v (Work.Cusp.polarToUHS v q'.1)).1 := by
      have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : Work.Cusp.E2)) hpair
      simpa using hc
    have hleft : Work.Cusp.nrm (Work.Cusp.cuspInvInner v q.1).1 ≤ 1 / 2 := by
      rw [jnrm_cuspInvInner q.2.1 h1]
      rw [div_le_iff₀ (by norm_num [Work.Cusp.rJ] : (0 : ℝ) < 2 * Work.Cusp.rJ)]
      linarith [h1, show (1 / 2 : ℝ) * (2 * Work.Cusp.rJ) = Work.Cusp.rJ by
        norm_num [Work.Cusp.rJ]]
    have hright : 1 / 2 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v (Work.Cusp.polarToUHS v q'.1)).1 :=
      jnrm_cuspInvOuter_gt_half hbox'.2.1 hx3
    rw [← hE] at hright
    linarith

/-! ### The theorem -/

theorem jCoordM_injective (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Function.Injective (Work.RTOwed.jCoordM a v D cU k W kx δ) := by
  have _hW := hW
  intro q q' h
  by_cases h1 : q.1 0 ≤ Work.Cusp.rJ
  · by_cases h2 : q'.1 0 ≤ Work.Cusp.rJ
    · exact jCoordM_inj_inner a v D cU k W kx δ hsec q q' h1 h2 h
    · exact jCoordM_inj_mixed a v D cU k W kx δ q q' h1 h2 h
  · by_cases h2 : q'.1 0 ≤ Work.Cusp.rJ
    · exact (jCoordM_inj_mixed a v D cU k W kx δ q' q h2 h1 h.symm).symm
    · exact jCoordM_inj_outer a v D cU k W kx δ hδ q q' h1 h2 h

end Work.RTOWed
