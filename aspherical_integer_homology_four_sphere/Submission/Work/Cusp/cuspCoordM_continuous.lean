import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.cuspInvOuter_continuousOn
import Submission.Work.Cusp.cuspX_outerU_outerY

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
# Continuity of the collar coordinate `cuspCoordM` on `M̂`

`cuspCoordM a v D c δ` sends a point `q = (x,s)` of the *open* chart box `cuspChartBox v c δ` to
`M̂`: below the ceiling `s < β x` to the point of the hyperbolic piece with UHS coordinates `q`
(the branch `incMbar ∘ mbarLow`), at or above it to the filling boundary point recovered by the
outer chart (the branch `incW ∘ cuspInvOuter`).

Continuity is proved by pasting the two branches along the ceiling `s = β x`.  The only point
which is not immediate from the continuity of `mbarLow` and of `cuspInvOuter` is the *agreement*
at the ceiling: there the two branches land on the same point of `M̂` because the gluing
`CuspGlueData.glue_eq` identifies the ceiling point over `cuspX v u y` with the filling boundary
point of coordinates `(u,y)`.
-/

/-- The open chart box of the collar chart is contained in the weakly closed chart box
(`cuspBox` has the weak inequality `0 ≤ outerU`, `cuspChartBox` the strict one). -/
theorem cuspChartBox_subset_cuspBox (v : Fin 5) (c : E3) (δ : ℝ) :
    cuspChartBox v c δ ⊆ cuspBox v c δ := by
  rintro q ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, le_of_lt h4, h5⟩

/-- **The value of `cuspCoordM` on the filling side of the gluing**, as a function of a point of
the closed chart box `cuspSource` of the collar (where the recovered layer parameter lies in
`[0,1]`, so that the outer chart lands in the square). -/
def cuspCoordMUp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspSource v c δ}) : a.Mhat :=
  a.incW v (⟨(cuspInvOuter v q.1).1, cuspInvOuter_mem_Sq v c δ q.1 q.2⟩,
    D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- The filling branch `incW ∘ cuspInvOuter` is continuous on the closed chart box. -/
theorem cuspCoordMUp_continuous (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) :
    Continuous (cuspCoordMUp a v D c δ) := by
  have hpos : ∀ q : {q : E4 // q ∈ cuspSource v c δ}, 0 < (q.1 : E4) 3 := by
    intro q
    exact lt_trans (by norm_num [s1]) q.2.1.2.1
  have hk : Continuous fun q : {q : E4 // q ∈ cuspSource v c δ} => cuspInvOuter v q.1 :=
    (cuspInvOuter_continuousOn v).comp_continuous continuous_subtype_val (fun q => hpos q)
  have hSquare : Continuous fun q : {q : E4 // q ∈ cuspSource v c δ} =>
      (⟨(cuspInvOuter v q.1).1, cuspInvOuter_mem_Sq v c δ q.1 q.2⟩ : Work.Space.SquarePt) :=
    hk.fst.subtype_mk (fun q => cuspInvOuter_mem_Sq v c δ q.1 q.2)
  have hTorus : Continuous fun q : {q : E4 // q ∈ cuspSource v c δ} =>
      D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))) := by
    apply D.tor.symm.continuous.comp
    fun_prop
  exact (a.continuous_incW v).comp (hSquare.prodMk hTorus)

/-- Two points of a filling piece define the same point of `M̂` as soon as their layer parameters
and their torus coordinates agree; the proofs of the square condition are irrelevant. -/
theorem incW_pair_congr (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    {p q : Work.Space.SquarePt × a.Torus v}
    (h1 : (p.1 : E2) = (q.1 : E2)) (h2 : p.2 = q.2) : a.incW v p = a.incW v q := by
  congr 1
  exact Prod.ext (Subtype.ext h1) h2

/-- **The cusp coordinate of a ceiling point of `M̄`.**  The point of `M̄` with UHS coordinates
`(x, β x)` on the truncation torus is glued to the filling boundary point whose perimeter
parameter is `outerU v x` and whose torus coordinates are `outerY v x`. -/
theorem incMbar_mbarPt_eq (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (x : E3) :
    a.incMbar (D.mbarPt x) =
      a.incW v (⟨bndOfU (outerU v x), by
          simpa only [Work.Space.Sq, Sq] using bndOfU_mem (outerU v x)⟩,
        D.tor.symm (fun i => (((outerY v x) i : ℝ) : AddCircle (1 : ℝ)))) := by
  suffices h : a.incMbar (D.mbarPt (cuspX v (outerU v x) (outerY v x))) =
      a.incW v (⟨bndOfU (outerU v x), by
          simpa only [Work.Space.Sq, Sq] using bndOfU_mem (outerU v x)⟩,
        D.tor.symm (fun i => (((outerY v x) i : ℝ) : AddCircle (1 : ℝ)))) by
    rwa [cuspX_outerU_outerY v x] at h
  rw [Work.Space.Assembly.incMbar_eq_incW a (D.mbarPt_mem (cuspX v (outerU v x) (outerY v x)))]
  rw [D.glue_eq]

/-- **The two branches of `cuspCoordM` agree at the ceiling.**  For `q` on the ceiling
`s = β x` of the chart box, the hyperbolic branch `incMbar ∘ mbarLow` and the filling branch
`incW ∘ cuspInvOuter` produce the same point of `M̂`. -/
theorem incMbar_mbarLow_eq (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : E4) (hbox : q ∈ cuspChartBox v c δ) (hceil : q 3 = beta (xOf q)) :
    a.incMbar (D.mbarLow q) =
      a.incW v (⟨(cuspInvOuter v q).1, cuspInvOuter_mem_Sq v c δ q
            ⟨cuspChartBox_subset_cuspBox v c δ hbox, le_of_eq hceil.symm⟩⟩,
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
      ⟨(cuspInvOuter v q).1, cuspInvOuter_mem_Sq v c δ q
        ⟨cuspChartBox_subset_cuspBox v c δ hbox, le_of_eq hceil.symm⟩⟩ :=
    Subtype.ext (congrArg Prod.fst hci).symm
  have h2 : D.tor.symm (fun i => (((outerY v (xOf q)) i : ℝ) : AddCircle (1 : ℝ))) =
      D.tor.symm (fun i => (((cuspInvOuter v q).2 i : ℝ) : AddCircle (1 : ℝ))) :=
    congrArg (fun z : E2 => D.tor.symm (fun i => (((z i : ℝ)) : AddCircle (1 : ℝ))))
      (congrArg Prod.snd hci).symm
  exact incW_pair_congr a v (Subtype.ext_iff.mp h1) h2

/-- **The lower branch computes `cuspCoordM` below the ceiling** (including on the ceiling,
where the two branches agree by `incMbar_mbarLow_eq`). -/
theorem cuspCoordM_eq_le (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspChartBox v c δ})
    (hq : q.1 3 ≤ beta (xOf q.1)) :
    cuspCoordM a v D c δ q = a.incMbar (D.mbarLow q.1) := by
  by_cases hlt : q.1 3 < beta (xOf q.1)
  · unfold cuspCoordM
    rw [dif_pos hlt]
  · have heq : q.1 3 = beta (xOf q.1) := le_antisymm hq (not_lt.mp hlt)
    unfold cuspCoordM
    rw [dif_neg hlt]
    rw [incMbar_mbarLow_eq a v D c δ q.1 q.2 heq]

/-- **The upper branch computes `cuspCoordM` above the ceiling** (`q` lies in the closed chart box
`cuspSource`, so that the outer chart lands in the square). -/
theorem cuspCoordM_eq_ge (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspChartBox v c δ})
    (hq : beta (xOf q.1) ≤ q.1 3) :
    cuspCoordM a v D c δ q =
      cuspCoordMUp a v D c δ ⟨q.1, ⟨cuspChartBox_subset_cuspBox v c δ q.2, hq⟩⟩ := by
  unfold cuspCoordM cuspCoordMUp
  rw [dif_neg (not_lt.mpr hq)]

theorem cuspCoordM_continuous (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) :
    Continuous (cuspCoordM a v D c δ) := by
  let X := {q : E4 // q ∈ cuspChartBox v c δ}
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
  have hle : ContinuousOn (fun q : X => cuspCoordM a v D c δ q)
      {q : X | q.1 3 ≤ beta (xOf q.1)} := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} => cuspCoordM a v D c δ r.1
    have hval : Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} => (r.1.1 : E4) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hm : ContinuousOn D.mbarLow
        {q : E4 | q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)} := D.mbarLow_cont c δ
    have hmc : Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} => D.mbarLow r.1.1 :=
      hm.comp_continuous hval (fun r => ⟨r.1.2, r.2⟩)
    have hinc : Continuous fun r : {q : X // q.1 3 ≤ beta (xOf q.1)} =>
        a.incMbar (D.mbarLow r.1.1) :=
      a.continuous_incMbar.comp hmc
    exact Continuous.congr hinc
      (fun r => (cuspCoordM_eq_le a v D c δ r.1 r.2).symm)
  have hge : ContinuousOn (fun q : X => cuspCoordM a v D c δ q)
      {q : X | beta (xOf q.1) ≤ q.1 3} := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} => cuspCoordM a v D c δ r.1
    have hval : Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} => (r.1.1 : E4) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hpsi : Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} =>
        (⟨r.1.1, ⟨cuspChartBox_subset_cuspBox v c δ r.1.2, r.2⟩⟩ :
          {q : E4 // q ∈ cuspSource v c δ}) :=
      Continuous.subtype_mk hval (fun r => ⟨cuspChartBox_subset_cuspBox v c δ r.1.2, r.2⟩)
    have hcomp : Continuous fun r : {q : X // beta (xOf q.1) ≤ q.1 3} =>
        cuspCoordMUp a v D c δ
          ⟨r.1.1, ⟨cuspChartBox_subset_cuspBox v c δ r.1.2, r.2⟩⟩ :=
      (cuspCoordMUp_continuous a v D c δ).comp hpsi
    exact Continuous.congr hcomp
      (fun r => (cuspCoordM_eq_ge a v D c δ r.1 r.2).symm)
  have hunion : {q : X | q.1 3 ≤ beta (xOf q.1)} ∪ {q : X | beta (xOf q.1) ≤ q.1 3}
      = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total (q.1 3) (beta (xOf q.1))
  rw [← continuousOn_univ, ← hunion]
  exact hle.union_of_isClosed hge hclosed_le hclosed_ge

end Work.Cusp
