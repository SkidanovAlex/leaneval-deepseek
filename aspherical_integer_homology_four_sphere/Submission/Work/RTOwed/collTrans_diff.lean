import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.mobius_inv_apply
import Submission.Work.RTOwed.contDiffOn_of_localMobius
import Submission.Work.RTOwed.isometry_of_localMobius

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Work.RTInstance
open Filter
open scoped Topology

/-! ## Chart bookkeeping for the collar charts -/

theorem cChart_target_eq (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1 / 2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (cChart a D v c δ hδ hne).target = cBoxR v c δ := by
  rw [cChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.ofSet_target,
    OpenPartialHomeomorph.ofSet_symm, cChartOf_target, OpenPartialHomeomorph.ofSet_apply]
  exact Set.inter_eq_left.mpr Set.inter_subset_left

theorem cChart_symm_apply (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1 / 2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (q : Work.Cusp.E4) (hq : q ∈ Work.Cusp.cuspBoxTop v c δ) (hq' : q ∈ cBoxR v c δ) :
    (cChart a D v c δ hδ hne).symm q = Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq⟩ := by
  have hx : Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq⟩ ∈ (cChart a D v c δ hδ hne).source := by
    rw [cChart_source]; exact ⟨⟨q, hq⟩, hq', rfl⟩
  have h1 : cChart a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq⟩) = q :=
    cChart_apply a D v c δ hδ hne q hq hq'
  have h2 := (cChart a D v c δ hδ hne).left_inv hx
  rw [h1] at h2
  exact h2

theorem ccTransSrc_mem_cBoxR (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1 / 2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (v' : Work.Space.Cusp) (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1 / 2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂})
    {q : Work.Cusp.E4} (hq : q ∈ ccTransSrc a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) :
    q ∈ cBoxR v c₁ δ₁ := by
  rw [ccTransSrc, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff] at hq
  rw [OpenPartialHomeomorph.symm_source, cChart_target_eq a D v c₁ δ₁ hδ₁ hne₁] at hq
  exact hq.1

theorem ccTransMap_mem_cBoxR (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1 / 2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (v' : Work.Space.Cusp) (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1 / 2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂})
    {q : Work.Cusp.E4} (hq : q ∈ ccTransSrc a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) :
    ccTransMap a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q ∈ cBoxR v' c₂ δ₂ := by
  have h2 : (cChart a D v c₁ δ₁ hδ₁ hne₁).symm q ∈ (cChart a D v' c₂ δ₂ hδ₂ hne₂).source := by
    rw [ccTransSrc, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage] at hq
    exact hq.2
  have hthis := (cChart a D v' c₂ δ₂ hδ₂ hne₂).map_source h2
  rw [ccTransMap]
  rwa [cChart_target_eq a D v' c₂ δ₂ hδ₂ hne₂] at hthis

theorem cuspCoordMTop_collision (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    {v v' : Work.Space.Cusp} (hne : v ≠ v')
    {c₁ : Work.Cusp.E3} {δ₁ : ℝ} {c₂ : Work.Cusp.E3} {δ₂ : ℝ}
    {q q' : Work.Cusp.E4}
    (hq : q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁) (hq' : q' ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂)
    (h : Work.Cusp.cuspCoordMTop a v (D v) c₁ δ₁ ⟨q, hq⟩ =
      Work.Cusp.cuspCoordMTop a v' (D v') c₂ δ₂ ⟨q', hq'⟩) :
    q 3 < Work.Cusp.beta (Work.Cusp.xOf q) ∧ q' 3 < Work.Cusp.beta (Work.Cusp.xOf q') ∧
      (D v).mbarLow q = (D v').mbarLow q' := by
  by_cases hlt : q 3 < Work.Cusp.beta (Work.Cusp.xOf q)
  · by_cases hlt' : q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')
    · have hL : Work.Cusp.cuspCoordMTop a v (D v) c₁ δ₁ ⟨q, hq⟩ =
          a.incMbar ((D v).mbarLow q) := by
        rw [Work.Cusp.cuspCoordMTop, dite_eq_left hlt]
      have hR : Work.Cusp.cuspCoordMTop a v' (D v') c₂ δ₂ ⟨q', hq'⟩ =
          a.incMbar ((D v').mbarLow q') := by
        rw [Work.Cusp.cuspCoordMTop, dite_eq_left hlt']
      rw [hL, hR] at h
      exact ⟨hlt, hlt', a.incMbar_injective h⟩
    · exfalso
      have hL : Work.Cusp.cuspCoordMTop a v (D v) c₁ δ₁ ⟨q, hq⟩ =
          a.incMbar ((D v).mbarLow q) := by
        rw [Work.Cusp.cuspCoordMTop, dite_eq_left hlt]
      rw [hL, Work.Cusp.cuspCoordMTop, dite_eq_right hlt'] at h
      exact (D v).mbarLow_not_TsetTop c₁ δ₁ hq hlt (Work.Cusp.incMbar_eq_incW_imp a v' h).1
  · exfalso
    rw [Work.Cusp.cuspCoordMTop, dite_eq_right hlt] at h
    by_cases hlt' : q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')
    · rw [Work.Cusp.cuspCoordMTop, dite_eq_left hlt'] at h
      exact (D v').mbarLow_not_TsetTop c₂ δ₂ hq' hlt'
        (Work.Cusp.incMbar_eq_incW_imp a v h.symm).1
    · rw [Work.Cusp.cuspCoordMTop, dite_eq_right hlt'] at h
      exact hne (congrArg Sigma.fst (a.incY_injective h))

theorem ccTrans_low (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v v' : Work.Space.Cusp) (hne : v ≠ v')
    (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1 / 2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1 / 2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂}) :
    ∀ q ∈ ccTransSrc a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂,
      q 3 < Work.Cusp.beta (Work.Cusp.xOf q) ∧
      (ccTransMap a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q) 3 <
        Work.Cusp.beta (Work.Cusp.xOf (ccTransMap a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q)) ∧
      (D v).mbarLow q
        = (D v').mbarLow (ccTransMap a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q) := by
  intro q hq
  rw [ccTransSrc, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
    Set.mem_preimage] at hq
  obtain ⟨hq1, hq2⟩ := hq
  have hqR : q ∈ cBoxR v c₁ δ₁ := by
    rwa [OpenPartialHomeomorph.symm_source, cChart_target_eq a D v c₁ δ₁ hδ₁ hne₁] at hq1
  have hqtop : q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁ := by
    rw [cBoxR, Set.mem_inter_iff] at hqR; exact hqR.1
  have hsym : (cChart a D v c₁ δ₁ hδ₁ hne₁).symm q
      = Work.Cusp.cuspCoordMTop a v (D v) c₁ δ₁ ⟨q, hqtop⟩ :=
    cChart_symm_apply a D v c₁ δ₁ hδ₁ hne₁ q hqtop hqR
  rw [hsym, cChart_source] at hq2
  obtain ⟨⟨q', hq'top⟩, hq'R, hq'eq⟩ := hq2
  have hcol := cuspCoordMTop_collision a D hne hqtop hq'top hq'eq.symm
  obtain ⟨hlt, hlt', hmLow⟩ := hcol
  have ht : ccTransMap a D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q = q' := by
    rw [ccTransMap, hsym, ← hq'eq]
    exact cChart_apply a D v' c₂ δ₂ hδ₂ hne₂ q' hq'top hq'R
  exact ⟨hlt, by rw [ht]; exact hlt', by rw [ht]; exact hmLow⟩



theorem ccTrans_local (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (v v' : Work.Space.Cusp) (hne : v ≠ v')
    (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1/2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1/2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂}) :
    ∀ q ∈ ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂,
      ∃ (V : Set Work.Cusp.E4) (B : Matrix (Fin 5) (Fin 5) ℝ),
        IsOpen V ∧ q ∈ V ∧ Work.HypModel.IsLorentzMat B ∧
          ∀ q' ∈ V,
            ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q'
              = Work.HypModel.mobius B q' := by
  intro q hq
  obtain ⟨hlt, hlt', hmLow⟩ :=
    ccTrans_low (Work.RTInstance.assemblyOf g) D v v' hne c₁ δ₁ hδ₁ hne₁ c₂ δ₂ hδ₂ hne₂ q hq
  have hqR : q ∈ cBoxR v c₁ δ₁ :=
    ccTransSrc_mem_cBoxR (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ hq
  have hqtop : q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁ := by
    rw [cBoxR, Set.mem_inter_iff] at hqR; exact hqR.1
  have htqR : ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q
      ∈ cBoxR v' c₂ δ₂ :=
    ccTransMap_mem_cBoxR (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ hq
  have htqtop : ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q
      ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂ := by
    rw [cBoxR, Set.mem_inter_iff] at htqR; exact htqR.1
  have hzT : (D v).mbarLow q ∉ (Work.RTInstance.assemblyOf g).Tset :=
    (D v).mbarLow_not_TsetTop c₁ δ₁ hqtop hlt
  obtain ⟨i, hi⟩ := Work.FoldInst.mem_foldChart_source hzT
  have h11 : 11/10 < q 3 := by have h := hqtop.2.1; rw [Work.Cusp.s1] at h; exact h
  obtain ⟨V₁, B₁, hV₁open, hqV₁, hB₁, hfold₁⟩ := (R v).foldLocal i h11 hlt hi
  have h11' : 11/10 < (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁
      v' c₂ δ₂ hδ₂ hne₂ q) 3 := by
    have h := htqtop.2.1; rw [Work.Cusp.s1] at h; exact h
  have hi' : (D v').mbarLow (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁
      v' c₂ δ₂ hδ₂ hne₂ q) ∈ (Work.FoldInst.foldChart i).source := by
    rw [← hmLow]; exact hi
  obtain ⟨V₂, B₂, hV₂open, htqV₂, hB₂, hfold₂⟩ := (R v').foldLocal i h11' hlt' hi'
  have hSopen : IsOpen (ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) := by
    rw [ccTransSrc]; exact OpenPartialHomeomorph.open_source _
  have hceil_open : IsOpen {q' : Work.Cusp.E4 | q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')} := by
    apply isOpen_lt
    · fun_prop
    · exact Work.Cusp.beta_continuous.comp (by unfold Work.Cusp.xOf; fun_prop)
  have hmbNhds : (D v).mbarLow ⁻¹' (Work.FoldInst.foldChart i).source ∈ 𝓝 q := by
    have hmem1 : q ∈ ({q' : Work.Cusp.E4 | q' ∈ Work.Cusp.cuspBoxTop v c₁ δ₁} ∩
        {q' : Work.Cusp.E4 | q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')}) := ⟨hqtop, hlt⟩
    have hopen1 : IsOpen ({q' : Work.Cusp.E4 | q' ∈ Work.Cusp.cuspBoxTop v c₁ δ₁} ∩
        {q' : Work.Cusp.E4 | q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')}) :=
      (Work.Cusp.isOpen_cuspBoxTop v c₁ δ₁).inter hceil_open
    have hcont : ContinuousAt (D v).mbarLow q :=
      ((D v).mbarLow_contTop c₁ δ₁).continuousAt
        (Filter.mem_of_superset (hopen1.mem_nhds hmem1) (fun x hx => ⟨hx.1, le_of_lt hx.2⟩))
    exact hcont.preimage_mem_nhds ((Work.FoldInst.foldChart i).open_source.mem_nhds hi)
  have htNhds : (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) ⁻¹' V₂ ∈ 𝓝 q := by
    have hcont : ContinuousAt (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) q := by
      refine ContinuousOn.continuousAt ?_ (hSopen.mem_nhds hq)
      rw [ccTransSrc]
      exact OpenPartialHomeomorph.continuousOn _
    exact hcont.preimage_mem_nhds (hV₂open.mem_nhds htqV₂)
  have hnb : (ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂
      ∩ V₁ ∩ ((D v).mbarLow ⁻¹' (Work.FoldInst.foldChart i).source)
      ∩ {q' : Work.Cusp.E4 | q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')}
      ∩ ((ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) ⁻¹' V₂))
      ∈ 𝓝 q :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem (hSopen.mem_nhds hq) (hV₁open.mem_nhds hqV₁)) hmbNhds)
      (hceil_open.mem_nhds hlt)) htNhds
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnb
  refine ⟨Metric.ball q ε, B₂⁻¹ * B₁, Metric.isOpen_ball, Metric.mem_ball_self hεpos,
    Work.HypModel.IsLorentzMat.mul (Work.FoldInst.isLorentzMat_inv hB₂) hB₁, ?_⟩
  intro q' hq'ball
  have hmem := hε hq'ball
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hmem
  obtain ⟨⟨⟨⟨hq'S, hq'V₁⟩, hq'mb⟩, hq'lt⟩, hq'tV₂⟩ := hmem
  obtain ⟨hlt₂, hlt₂', hmLow₂⟩ :=
    ccTrans_low (Work.RTInstance.assemblyOf g) D v v' hne c₁ δ₁ hδ₁ hne₁ c₂ δ₂ hδ₂ hne₂ q' hq'S
  have hq'R : q' ∈ cBoxR v c₁ δ₁ :=
    ccTransSrc_mem_cBoxR (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ hq'S
  have hq'top : q' ∈ Work.Cusp.cuspBoxTop v c₁ δ₁ := by
    rw [cBoxR, Set.mem_inter_iff] at hq'R; exact hq'R.1
  have hq'3pos : 0 < q' 3 := by
    have h := hq'top.2.1; rw [Work.Cusp.s1] at h; linarith
  have htq'R : ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q'
      ∈ cBoxR v' c₂ δ₂ :=
    ccTransMap_mem_cBoxR (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ hq'S
  have htq'top : ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q'
      ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂ := by
    rw [cBoxR, Set.mem_inter_iff] at htq'R; exact htq'R.1
  have htq'3pos : 0 < (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q') 3 := by
    have h := htq'top.2.1; rw [Work.Cusp.s1] at h; linarith
  have h1 := hfold₁ q' hq'V₁ hq'mb
  have h2 := hfold₂ (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q')
    hq'tV₂ (by rw [← hmLow₂]; exact hq'mb)
  have hmob : Work.HypModel.mobius B₁ q'
      = Work.HypModel.mobius B₂ (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q') := by
    rw [← h1, hmLow₂, h2]
  calc ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q'
      = Work.HypModel.mobius B₂⁻¹ (Work.HypModel.mobius B₂
          (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂ q')) :=
        (mobius_inv_apply hB₂ htq'3pos).symm
    _ = Work.HypModel.mobius B₂⁻¹ (Work.HypModel.mobius B₁ q') := by rw [hmob]
    _ = Work.HypModel.mobius (B₂⁻¹ * B₁) q' :=
        (Work.HypModel.mobius_mul (Work.FoldInst.isLorentzMat_inv hB₂) hB₁ hq'3pos).symm

theorem collTrans_diff (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (v v' : Work.Space.Cusp) (hne : v ≠ v')
    (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1/2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1/2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂}) :
    Work.RTOwed.TransIso2 Work.RTOwed.cLayer.model Work.RTOwed.cLayer.model
      (Work.RTOwed.ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂)
      (Work.RTOwed.ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) := by
  have hloc := ccTrans_local g D R v v' hne c₁ δ₁ hδ₁ hne₁ c₂ δ₂ hδ₂ hne₂
  refine ⟨?_, ?_⟩
  · refine contDiffOn_of_localMobius (fun z hz => ?_) (fun z hz => hloc z hz)
    have hzR := ccTransSrc_mem_cBoxR (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁
      v' c₂ δ₂ hδ₂ hne₂ hz
    have hztop : z ∈ Work.Cusp.cuspBoxTop v c₁ δ₁ := by
      rw [cBoxR, Set.mem_inter_iff] at hzR; exact hzR.1
    have hs1pos : (0:ℝ) < Work.Cusp.s1 := by norm_num [Work.Cusp.s1]
    exact ne_of_gt (lt_trans hs1pos hztop.2.1)
  · have hT : ∀ z ∈ ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂,
        Work.RTOwed.cδ ≤ (ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁
          v' c₂ δ₂ hδ₂ hne₂ z) 3 := by
      intro z hz
      have hzR := ccTransMap_mem_cBoxR (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁
        v' c₂ δ₂ hδ₂ hne₂ hz
      have hztop : ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁
          v' c₂ δ₂ hδ₂ hne₂ z ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂ := by
        rw [cBoxR, Set.mem_inter_iff] at hzR; exact hzR.1
      exact le_of_lt hztop.2.1
    have hT' : ∀ z ∈ ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂,
        Work.RTOwed.cδ ≤ z 3 := by
      intro z hz
      have hzR := ccTransSrc_mem_cBoxR (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁
        v' c₂ δ₂ hδ₂ hne₂ hz
      have hztop : z ∈ Work.Cusp.cuspBoxTop v c₁ δ₁ := by
        rw [cBoxR, Set.mem_inter_iff] at hzR; exact hzR.1
      exact le_of_lt hztop.2.1
    have hδpos : (0:ℝ) < Work.RTOwed.cδ := by norm_num [Work.RTOwed.cδ]
    intro z hz u w
    exact isometry_of_localMobius (δ := Work.RTOwed.cδ) hδpos hT hT'
      (fun z hz => hloc z hz) z hz u w

end Work.RTOwed
