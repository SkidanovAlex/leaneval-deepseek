import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspInvOuter_continuousOn
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-!
# Continuity of the *unslabbed* collar coordinate `cuspCoordMTop` on `M̂`

`cuspCoordMTop a v D c δ` sends a point `q = (x,s)` of the *unslabbed* chart box
`cuspBoxTop v c δ` (side `2δ` in the cusp coordinate `x`, height in `(s₁, sTop)`, and *no* condition
on the meridian coordinate `outerU v x`) to `M̂`: below the ceiling `s < β x` to the point of the
hyperbolic piece with UHS coordinates `q` (the branch `incMbar ∘ mbarLow`), at or above it to the
filling boundary point recovered by the outer chart (the branch `incW ∘ cuspInvOuter`).

The proof is the exact analogue of `cuspCoordM_continuous` (`cuspCoordM_continuous.lean`), with the
slabbed box `cuspChartBox`/`cuspSource` replaced by the unslabbed box `cuspBoxTop`/`cuspSourceTop`
and the corresponding fields `mbarLow_contTop` of `CuspGlueData`:

* the lower branch `incMbar ∘ mbarLow` is continuous on the closed below-ceiling region of the box,
  because `D.mbarLow_contTop` gives the continuity of the chart and `a.continuous_incMbar` that of
  the injection into `M̂`;
* the upper branch `incW ∘ cuspInvOuter` is continuous on the closed on-or-above-ceiling region
  `cuspSourceTop`, because `cuspInvOuter` is continuous on `{q | 0 < q 3}` (the heights of the box
  are `> s₁ > 0`) and `cuspInvOuter_mem_SqTop` supplies the square membership making it a point of
  the `v`-th filling piece;
* the two branches agree on the ceiling `s = β x` (the same computation as in the slabbed case: the
  ceiling point over `u σ_v + y` is glued to the filling boundary point of coordinates `(u,y)`);
* the two closed pieces cover the box (`le_total`), so `ContinuousOn.union_of_isClosed` pastes the
  two branches.
-/

/-- **The value of `cuspCoordMTop` on the filling side of the gluing**, as a function of a point of
the closed collar source `cuspSourceTop v c δ` of the unslabbed box (where the recovered layer
parameter lies in `(1/4,1]`, so that the outer chart lands in the square). -/
def cuspCoordMTopUp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspSourceTop v c δ}) : a.Mhat :=
  a.incW v (⟨(cuspInvOuter v q.1).1, cuspInvOuter_mem_SqTop v c δ q.1 q.2⟩,
    D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- The filling branch `incW ∘ cuspInvOuter` is continuous on the closed collar source. -/
theorem cuspCoordMTopUp_continuous (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) :
    Continuous (cuspCoordMTopUp a v D c δ) := by
  have hpos : ∀ q : {q : E4 // q ∈ cuspSourceTop v c δ}, 0 < (q.1 : E4) 3 := by
    intro q
    exact lt_trans (by norm_num [s1]) q.2.1.2.1
  have hk : Continuous fun q : {q : E4 // q ∈ cuspSourceTop v c δ} => cuspInvOuter v q.1 :=
    (cuspInvOuter_continuousOn v).comp_continuous continuous_subtype_val (fun q => hpos q)
  have hSquare : Continuous fun q : {q : E4 // q ∈ cuspSourceTop v c δ} =>
      (⟨(cuspInvOuter v q.1).1, cuspInvOuter_mem_SqTop v c δ q.1 q.2⟩ : Work.Space.SquarePt) :=
    hk.fst.subtype_mk (fun q => cuspInvOuter_mem_SqTop v c δ q.1 q.2)
  have hTorus : Continuous fun q : {q : E4 // q ∈ cuspSourceTop v c δ} =>
      D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))) := by
    apply D.tor.symm.continuous.comp
    fun_prop
  exact (a.continuous_incW v).comp (hSquare.prodMk hTorus)

/-- **The two branches of `cuspCoordMTop` agree at the ceiling.**  For `q` on the ceiling
`s = β x` of the unslabbed box, the hyperbolic branch `incMbar ∘ mbarLow` and the filling branch
`incW ∘ cuspInvOuter` produce the same point of `M̂`. -/
theorem incMbar_mbarLow_eqTop (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (q : E4) (hbox : q ∈ cuspBoxTop v c δ)
    (hceil : q 3 = beta (xOf q)) :
    a.incMbar (D.mbarLow q) =
      a.incW v (⟨(cuspInvOuter v q).1, cuspInvOuter_mem_SqTop v c δ q
            ⟨hbox, le_of_eq hceil.symm⟩⟩,
        D.tor.symm (fun i => (((cuspInvOuter v q).2 i : ℝ) : AddCircle (1 : ℝ)))) := by
  have hqc : q = ceilingPt (xOf q) := by
    ext i
    fin_cases i <;> simp [ceilingPt, xOf, hceil]
  have hL : D.mbarLow q = D.mbarPt (xOf q) := by
    conv_lhs => rw [hqc]
    rw [← D.mbarPt_eq]
  have hci : cuspInvOuter v q = (bndOfU (outerU v (xOf q)), outerY v (xOf q)) := by
    simp [cuspInvOuter, xOf, hceil]
  rw [hL, incMbar_mbarPt_eq a v D (xOf q)]
  have h1 : (⟨bndOfU (outerU v (xOf q)), by
        simpa only [Work.Space.Sq, Sq] using bndOfU_mem (outerU v (xOf q))⟩ :
      Work.Space.SquarePt) =
      ⟨(cuspInvOuter v q).1, cuspInvOuter_mem_SqTop v c δ q
        ⟨hbox, le_of_eq hceil.symm⟩⟩ :=
    Subtype.ext (congrArg Prod.fst hci).symm
  have h2 : D.tor.symm (fun i => (((outerY v (xOf q)) i : ℝ) : AddCircle (1 : ℝ))) =
      D.tor.symm (fun i => (((cuspInvOuter v q).2 i : ℝ) : AddCircle (1 : ℝ))) :=
    congrArg (fun z : E2 => D.tor.symm (fun i => (((z i : ℝ)) : AddCircle (1 : ℝ))))
      (congrArg Prod.snd hci).symm
  exact incW_pair_congr a v (Subtype.ext_iff.mp h1) h2

/-- **The lower branch computes `cuspCoordMTop` below the ceiling** (including on the ceiling,
where the two branches agree by `incMbar_mbarLow_eqTop`). -/
theorem cuspCoordMTop_eq_le (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspBoxTop v c δ})
    (hq : q.1 3 ≤ beta (xOf q.1)) :
    cuspCoordMTop a v D c δ q = a.incMbar (D.mbarLow q.1) := by
  by_cases hlt : q.1 3 < beta (xOf q.1)
  · unfold cuspCoordMTop
    rw [dif_pos hlt]
  · have heq : q.1 3 = beta (xOf q.1) := le_antisymm hq (not_lt.mp hlt)
    unfold cuspCoordMTop
    rw [dif_neg hlt]
    rw [incMbar_mbarLow_eqTop a v D c δ q.1 q.2 heq]

/-- **The upper branch computes `cuspCoordMTop` above the ceiling** (`q` lies in the closed collar
source `cuspSourceTop`, so that the outer chart lands in the square). -/
theorem cuspCoordMTop_eq_ge (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspBoxTop v c δ})
    (hq : beta (xOf q.1) ≤ q.1 3) :
    cuspCoordMTop a v D c δ q =
      cuspCoordMTopUp a v D c δ ⟨q.1, ⟨q.2, hq⟩⟩ := by
  unfold cuspCoordMTop cuspCoordMTopUp
  rw [dif_neg (not_lt.mpr hq)]

theorem cuspCoordMTop_continuous (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) :
    Continuous (cuspCoordMTop a v D c δ) := by
  let X := {q : E4 // q ∈ cuspBoxTop v c δ}
  let F : X → ℝ := fun q => q.1 3 - beta (xOf q.1)
  have hF : Continuous F := by
    show Continuous fun q : X => q.1 3 - beta (xOf q.1)
    have hx : Continuous fun q : X => xOf q.1 :=
      (by fun_prop : Continuous fun q : E4 => (!₂[q 0, q 1, q 2] : E3)).comp
        continuous_subtype_val
    have hb : Continuous fun q : X => beta (xOf q.1) := beta_continuous.comp hx
    have h3 : Continuous fun q : X => (q.1 : E4) 3 :=
      (by fun_prop : Continuous fun q : E4 => q 3).comp continuous_subtype_val
    exact h3.sub hb
  have hclosed_le : IsClosed {q : X | q.1 3 ≤ beta (xOf q.1)} := by
    have hset : {q : X | q.1 3 ≤ beta (xOf q.1)} = F ⁻¹' (Set.Iic 0) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, F, sub_nonpos]
    rw [hset]
    exact isClosed_Iic.preimage hF
  have hclosed_ge : IsClosed {q : X | beta (xOf q.1) ≤ q.1 3} := by
    have hset : {q : X | beta (xOf q.1) ≤ q.1 3} = F ⁻¹' (Set.Ici 0) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, F, sub_nonneg]
    rw [hset]
    exact isClosed_Ici.preimage hF
  have hle : ContinuousOn (fun q : X => cuspCoordMTop a v D c δ q)
      {q : X | q.1 3 ≤ beta (xOf q.1)} := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} => cuspCoordMTop a v D c δ r.1
    have hval : Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} => (r.1.1 : E4) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hm : ContinuousOn D.mbarLow
        {q : E4 | q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)} := D.mbarLow_contTop c δ
    have hmc : Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} => D.mbarLow r.1.1 :=
      hm.comp_continuous hval (fun r => ⟨r.1.2, r.2⟩)
    have hinc : Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} =>
        a.incMbar (D.mbarLow r.1.1) :=
      a.continuous_incMbar.comp hmc
    exact Continuous.congr hinc
      (fun r => (cuspCoordMTop_eq_le a v D c δ r.1 r.2).symm)
  have hge : ContinuousOn (fun q : X => cuspCoordMTop a v D c δ q)
      {q : X | beta (xOf q.1) ≤ q.1 3} := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} => cuspCoordMTop a v D c δ r.1
    have hval : Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} => (r.1.1 : E4) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hpsi : Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} =>
        (⟨r.1.1, ⟨r.1.2, r.2⟩⟩ :
          {q : E4 // q ∈ cuspSourceTop v c δ}) :=
      Continuous.subtype_mk hval (fun r => ⟨r.1.2, r.2⟩)
    have hcomp : Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} =>
        cuspCoordMTopUp a v D c δ
          ⟨r.1.1, ⟨r.1.2, r.2⟩⟩ :=
      (cuspCoordMTopUp_continuous a v D c δ).comp hpsi
    exact Continuous.congr hcomp
      (fun r => (cuspCoordMTop_eq_ge a v D c δ r.1 r.2).symm)
  have hunion : {q : X | q.1 3 ≤ beta (xOf q.1)} ∪ {q : X | beta (xOf q.1) ≤ q.1 3}
      = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total (q.1 3) (beta (xOf q.1))
  rw [← continuousOn_univ, ← hunion]
  exact hle.union_of_isClosed hge hclosed_le hclosed_ge

end Work.Cusp
