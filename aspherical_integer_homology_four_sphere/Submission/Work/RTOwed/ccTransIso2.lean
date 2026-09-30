import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.collTrans_diff
import Submission.Work.RTOwed.cuspCoordMTop_add
import Submission.Work.RTOwed.cuspCoordMTop_fibre

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.RTOwed.ccTransIso2`

The collar-collar transition of `M̂` between two collar charts of the filling atlas is smooth
and an isometry of the two metric models (`Work.RTOwed.TransIso2`), for arbitrary cusps `v`, `v'`.

This is assembled from the two cases proved by colleagues:

* `Work.RTOwed.collTrans_diff` (`Submission/Work/RTOwed/collTrans_diff.lean`), the case `v ≠ v'`;
* `Work.RTOwed.collTrans_same` (`Submission/Work/RTOwed/collTrans_same.lean`), the case `v = v'`.

**A bookkeeping remark.**  The two modules `collTrans_same` and `collTrans_diff` both declare a
lemma `Work.RTOwed.cChart_symm_apply` (with the same name but slightly different signatures), so
they cannot be imported into the same file.  We therefore import `collTrans_diff` (whose
`cChart_target_eq`, `ccTransSrc_mem_cBoxR`, ... API is not duplicated anywhere else) and repeat,
under fresh names (`cChart_toFun_apply_cc`, `cChart_symm_apply_cc`, `mem_cBoxR_iff_cc`), the three
chart lemmas that the `v = v'` proof uses, together with the (verbatim) proof of that case.
-/

noncomputable section

open Set Topology Function Filter
open scoped Topology

namespace Work.RTOwed


/-! ## API for the collar chart `cChart` of the atlas -/

theorem cChart_toFun_apply_cc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (d : ℝ) (hd : d ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c d}) (y : a.Mhat) :
    cChart a D v c d hd hne y = cChartOf a D v c d hd hne y := by
  rw [cChart, OpenPartialHomeomorph.trans_apply]
  rfl

theorem cChart_symm_apply_cc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (d : ℝ) (hd : d ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c d})
    {q : Work.Cusp.E4} (hq : q ∈ Work.Cusp.cuspBoxTop v c d) :
    (cChart a D v c d hd hne).symm q = Work.Cusp.cuspCoordMTop a v (D v) c d ⟨q, hq⟩ := by
  show (cChartOf a D v c d hd hne).symm q = _
  exact @Work.Cusp.cuspChart_symm a v (D v) c d hd hne q hq

theorem mem_cBoxR_iff_cc (v : Work.Space.Cusp) (c : Work.Cusp.E3) (d : ℝ) (q : Work.Cusp.E4) :
    q ∈ cBoxR v c d ↔ q ∈ Work.Cusp.cuspBoxTop v c d ∧ q 3 < Work.Cusp.sJ := by
  rw [cBoxR]
  exact Iff.rfl

/-! ## The collar-collar transition of `M̂` -/

theorem ccTransIso2_same (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (v : Work.Space.Cusp) (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1/2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1/2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₂ δ₂}) :
    Work.RTOwed.TransIso2 Work.RTOwed.cLayer.model Work.RTOwed.cLayer.model
      (Work.RTOwed.ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v c₂ δ₂ hδ₂ hne₂)
      (Work.RTOwed.ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v c₂ δ₂ hδ₂ hne₂) := by
  unfold Work.RTOwed.TransIso2
  set F₁ := Work.RTOwed.cChart (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ with hF₁
  set F₂ := Work.RTOwed.cChart (Work.RTInstance.assemblyOf g) D v c₂ δ₂ hδ₂ hne₂ with hF₂
  set T := Work.RTOwed.ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v c₂ δ₂ hδ₂ hne₂ with hT
  set S := Work.RTOwed.ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v c₂ δ₂ hδ₂ hne₂ with hS
  have hSeq : S = F₁.target ∩ F₁.symm ⁻¹' F₂.source := by
    rw [hS, Work.RTOwed.ccTransSrc]
    rfl
  rw [hSeq]
  have hSopen : IsOpen (F₁.target ∩ F₁.symm ⁻¹' F₂.source) := by
    rw [show F₁.target ∩ F₁.symm ⁻¹' F₂.source = (F₁.symm.trans F₂).source from rfl]
    exact (F₁.symm.trans F₂).open_source
  have hW : ∀ L : Work.Cusp.E3, IsOpen (F₁.target ∩ F₁.symm ⁻¹' F₂.source ∩
      {z : Work.Cusp.E4 | z + Work.RTOwed.liftE4 L ∈ Work.RTOwed.cBoxR v c₂ δ₂}) := fun L =>
    hSopen.inter ((isOpen_cBoxR v c₂ δ₂).preimage (continuous_id.add continuous_const))
  have key : ∀ q : Work.Cusp.E4, q ∈ F₁.target ∩ F₁.symm ⁻¹' F₂.source →
      ∃ L : Work.Cusp.E3, Work.RTOwed.latVec v L ∧ T q = q + Work.RTOwed.liftE4 L ∧
        T =ᶠ[𝓝 q] (fun z : Work.Cusp.E4 => z + Work.RTOwed.liftE4 L) := by
    intro q hq
    obtain ⟨hqt, hqs⟩ := hq
    have hqbox : q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁ := by
      have h := hqt
      rw [hF₁, cChart_target_eq] at h
      exact (mem_cBoxR_iff_cc v c₁ δ₁ q).mp h |>.1
    have hsymmq : F₁.symm q =
        Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₁ δ₁ ⟨q, hqbox⟩ := by
      rw [hF₁]; exact cChart_symm_apply_cc _ _ _ _ _ _ _ hqbox
    obtain ⟨qq, hqqbox, hqqm⟩ : ∃ qq : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₂ δ₂},
        (qq : Work.Cusp.E4) ∈ Work.RTOwed.cBoxR v c₂ δ₂ ∧
          Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₂ δ₂ qq = F₁.symm q := by
      have h := hqs
      rw [Set.mem_preimage] at h
      rw [hF₂, Work.RTOwed.cChart_source, Set.mem_image] at h
      exact h
    have heq : Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₁ δ₁ ⟨q, hqbox⟩
        = Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₂ δ₂ qq := by
      rw [← hsymmq, hqqm]
    obtain ⟨hL, h3⟩ := Work.RTOWed.cuspCoordMTop_fibre g D R v c₁ δ₁ q hqbox c₂ δ₂ (qq : Work.Cusp.E4) qq.2 heq
    have hqqeq : (qq : Work.Cusp.E4)
        = q + Work.RTOwed.liftE4 (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q) := by
      ext j
      fin_cases j <;> simp [Work.Cusp.xOf, Work.RTOwed.liftE4] <;> linarith [h3]
    refine ⟨Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q, hL, ?_, ?_⟩
    · have ht : T q = (qq : Work.Cusp.E4) := by
        have hsh : T q = F₂ (F₁.symm q) := rfl
        rw [hsh]
        change Work.RTOwed.cChart (Work.RTInstance.assemblyOf g) D v c₂ δ₂ hδ₂ hne₂ (F₁.symm q)
          = (qq : Work.Cusp.E4)
        rw [cChart_toFun_apply_cc, ← hqqm]
        exact cChartOf_apply (Work.RTInstance.assemblyOf g) D v c₂ δ₂ hδ₂ hne₂ (qq : Work.Cusp.E4) qq.2
      rw [ht]
      exact hqqeq
    · refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨_, (hW (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q)).mem_nhds
          ⟨⟨hqt, hqs⟩, ?_⟩, ?_⟩
      · have hmem : q + Work.RTOwed.liftE4 (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q)
            ∈ Work.RTOwed.cBoxR v c₂ δ₂ := by
          rw [← hqqeq]; exact hqqbox
        exact hmem
      · intro z hz
        obtain ⟨hzt, hzs⟩ := hz.1
        have hzbox : z ∈ Work.Cusp.cuspBoxTop v c₁ δ₁ := by
          have h := hzt
          rw [hF₁, cChart_target_eq] at h
          exact (mem_cBoxR_iff_cc v c₁ δ₁ z).mp h |>.1
        have hsymmz : F₁.symm z =
            Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₁ δ₁ ⟨z, hzbox⟩ := by
          rw [hF₁]; exact cChart_symm_apply_cc _ _ _ _ _ _ _ hzbox
        have hz2box : z + Work.RTOwed.liftE4
            (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q) ∈ Work.Cusp.cuspBoxTop v c₂ δ₂ :=
          (mem_cBoxR_iff_cc v c₂ δ₂ _).mp hz.2 |>.1
        have hper := Work.RTOWed.cuspCoordMTop_add g D R v c₁ δ₁ z hzbox
          (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q) hL c₂ δ₂ hz2box
        have htz : T z = z + Work.RTOwed.liftE4
            (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q) := by
          have hsh : T z = F₂ (F₁.symm z) := rfl
          rw [hsh]
          change Work.RTOwed.cChart (Work.RTInstance.assemblyOf g) D v c₂ δ₂ hδ₂ hne₂ (F₁.symm z)
            = z + Work.RTOwed.liftE4 (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q)
          rw [cChart_toFun_apply_cc, hsymmz, hper]
          exact cChartOf_apply (Work.RTInstance.assemblyOf g) D v c₂ δ₂ hδ₂ hne₂
            (z + Work.RTOwed.liftE4 (Work.Cusp.xOf (qq : Work.Cusp.E4) - Work.Cusp.xOf q)) hz2box
        exact htz
  constructor
  · intro q hq
    obtain ⟨L, hL, hTq, hev⟩ := key q hq
    have hcont : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : Work.Cusp.E4 => z + Work.RTOwed.liftE4 L) q := by
      rw [show (fun z : Work.Cusp.E4 => z + Work.RTOwed.liftE4 L)
          = (fun z => id z + Work.RTOwed.liftE4 L) from rfl]
      exact contDiffAt_id.add contDiffAt_const
    exact (hcont.congr_of_eventuallyEq hev).contDiffWithinAt
  · intro q hq u w
    obtain ⟨L, hL, hTq, hev⟩ := key q hq
    have hfd : fderiv ℝ T q = ContinuousLinearMap.id ℝ Work.Cusp.E4 := by
      rw [hev.fderiv_eq]
      rw [show (fun z : Work.Cusp.E4 => z + Work.RTOwed.liftE4 L)
          = (fun z => id z + Work.RTOwed.liftE4 L) from rfl]
      rw [fderiv_add_const, fderiv_id]
    rw [hfd, hTq]
    simp only [ContinuousLinearMap.id_apply]
    have h3 : (q + Work.RTOwed.liftE4 L) 3 = q 3 := by simp [Work.RTOwed.liftE4]
    show Work.RTInstance.uhsModel Work.RTOwed.cδ (q + Work.RTOwed.liftE4 L) u w
      = Work.RTInstance.uhsModel Work.RTOwed.cδ q u w
    rw [Work.RTInstance.uhsModel_apply, Work.RTInstance.uhsModel_apply, h3]


/-- **The collar-collar transition of `M̂` is smooth and is an isometry of the metric models**,
for arbitrary (possibly distinct) cusps `v`, `v'`: the `v ≠ v'` case is `collTrans_diff`, the
`v = v'` case is `ccTransIso2_same` above. -/
theorem ccTransIso2 (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (v v' : Work.Space.Cusp)
    (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1/2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1/2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂}) :
    Work.RTOwed.TransIso2 Work.RTOwed.cLayer.model Work.RTOwed.cLayer.model
      (Work.RTOwed.ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂)
      (Work.RTOwed.ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) := by
  rcases eq_or_ne v v' with hv | hne
  · subst hv
    exact ccTransIso2_same g D R v c₁ δ₁ hδ₁ hne₁ c₂ δ₂ hδ₂ hne₂
  · exact collTrans_diff g D R v v' hne c₁ δ₁ hδ₁ hne₁ c₂ δ₂ hδ₂ hne₂

end Work.RTOwed
