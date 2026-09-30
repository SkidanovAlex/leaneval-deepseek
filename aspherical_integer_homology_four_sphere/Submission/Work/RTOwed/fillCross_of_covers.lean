import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.Instance
import Submission.Work.RTOwed.FillCrossDef
import Submission.Work.RTOwed.atlas_empty
import Submission.Work.RTOwed.coreTrans
import Submission.Work.RTOwed.atlas_junction_cover_polar
import Submission.Work.RTOwed.atlas_junction_cover_collar
import Submission.Work.RTOwed.jTrans_coll_iso
import Submission.Work.RTOwed.kcInter_empty
import Submission.Work.RTOwed.mobius_inv_apply
import Submission.Work.RTOwed.contDiffOn_of_localMobius
import Submission.Work.RTOwed.jjTransIso2
import Submission.Work.RTOwed.ccTransIso2
import Submission.Work.RTOwed.jkTransIso2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Matrix
open scoped Matrix RealInnerProductSpace ContDiff Topology Manifold

namespace Work.RTOwed

open Work.RTInstance

-- ===== copied from foldTrans_coll.lean (cChart_symm_apply renamed) =====
/-
# The fold–collar transitions of the atlas of `M̂`

This file proves that the transition between a *transported fold chart* `(foldDataOf g).foldM i` of
`M̂` (with its upper half space metric `uhsModel (foldDataOf g).δ`) and a *collar chart*
`cChart a D v c δ` of the `v`-th cusp (with its upper half space metric `cLayer.model = uhsModel cδ`)
is smooth and isometric, in both directions.

The mathematical input is the rigidity of the cusp chart of `M̄`
(`Work.RTOwed.CuspRigid.foldLocal`): on every point of the chimney strictly below the ceiling, the
composite `foldChart i ∘ mbarLow` is *locally one Möbius transformation* `mobius B` of the upper
half space model.  Since the collar chart of `M̂` is, on its source, the inverse of the coordinate
inclusion `cuspCoordMTop` (which is `incMbar ∘ mbarLow` below the ceiling and `incW` above it), and
the fold charts only meet the collar charts below the ceiling, the two transitions are the Möbius
maps `mobius B⁻¹` (fold → collar) and `mobius B` (collar → fold).

## Contents

* `transIso2_uhs_of_localMobius` — the engine: a map which is locally Möbius on an open set `S`
  whose heights are bounded below is `C^∞` on `S` and is an isometry between the two upper half
  space models (`TransIso2`);
* `cChart_target'`, `fc_cChart_symm_apply` — the two elementary facts about the collar chart that the
  computation of its source needs;
* `foldCTransSrc_exists`, `cFoldTransSrc_exists` — the structure of the sources: below the ceiling;
* `foldCTrans_local`, `cFoldTrans_local` — the local Möbius form of the two transitions;
* `foldTrans_coll` — the target.
-/



open Set Topology Function Filter Matrix
open scoped Matrix RealInnerProductSpace ContDiff Topology Manifold


abbrev E4 := Work.RTInstance.E4

/-! ## The engine: a locally Möbius map of an open set -/

/-- **Smoothness and isometry of a locally Möbius map between two upper half space models.**

If `w` agrees with a Möbius transformation `mobius B` (`B` Lorentz) near every point of an open set
`S`, and if the heights of `z` and `w z` are bounded below by `δ₁` and `δ₂` on `S`, then `w` is
`C^∞` on `S` and `w` pulls the model `uhsModel δ₂` back to `uhsModel δ₁`.

The two models are total extensions of the honest upper half space metric `uhsMetric`, agreeing with
it above their margin, so the pointwise claim is exactly the Möbius isometry
`Work.HypModel.mobius_isometry`. -/
theorem transIso2_uhs_of_localMobius {w : E4 → E4} {S : Set E4} {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hS : IsOpen S)
    (h₁ : ∀ z ∈ S, δ₁ ≤ z 3) (h₂ : ∀ z ∈ S, δ₂ ≤ w z 3)
    (hloc : ∀ z ∈ S, ∃ (V : Set E4) (B : Matrix (Fin 5) (Fin 5) ℝ),
      IsOpen V ∧ z ∈ V ∧ Work.HypModel.IsLorentzMat B ∧
      ∀ z' ∈ V ∩ S, w z' = Work.HypModel.mobius B z') :
    TransIso2 (Work.RTInstance.uhsModel δ₁) (Work.RTInstance.uhsModel δ₂) w S := by
  have hne : ∀ z ∈ S, z 3 ≠ 0 := fun z hz => ne_of_gt (lt_of_lt_of_le hδ₁ (h₁ z hz))
  constructor
  · intro z hz
    obtain ⟨V, B, hVopen, hzV, hB, hEq⟩ := hloc z hz
    have hmob : ContDiffWithinAt ℝ ∞ (Work.HypModel.mobius B) S z := by
      have hnu : ({q : E4 | q 3 ≠ 0} : Set E4) ∈ 𝓝 z := by
        have hc : Continuous fun q : E4 => q 3 := by fun_prop
        rcases lt_or_gt_of_ne (hne z hz) with h | h
        · exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds h)
            (fun q hq => ne_of_lt hq)
        · exact Filter.mem_of_superset ((isOpen_lt continuous_const hc).mem_nhds h)
            (fun q hq => ne_of_gt hq)
      refine (contDiffWithinAt_iff_contDiffAt (hS.mem_nhds hz)).mpr ?_
      have h2 : ContDiffAt ℝ ⊤ (Work.HypModel.mobius B) z :=
        (contDiffWithinAt_iff_contDiffAt hnu).mp
          ((contDiffOn_mobius_height_ne hB).contDiffWithinAt (hne z hz))
      exact h2.of_le le_top
    have hev : (w : E4 → E4) =ᶠ[𝓝[S] z] Work.HypModel.mobius B := by
      change ∀ᶠ x in 𝓝[S] z, w x = Work.HypModel.mobius B x
      rw [eventually_nhdsWithin_iff]
      exact Filter.eventually_of_mem (hVopen.mem_nhds hzV)
        (fun z' hz'V hz'S => hEq z' ⟨hz'V, hz'S⟩)
    exact ContDiffWithinAt.congr_of_eventuallyEq hmob hev (hEq z ⟨hzV, hz⟩)
  · intro z hz u v
    obtain ⟨V, B, hVopen, hzV, hB, hEq⟩ := hloc z hz
    have hev : w =ᶠ[𝓝 z] Work.HypModel.mobius B :=
      Filter.eventually_of_mem (inter_mem (hVopen.mem_nhds hzV) (hS.mem_nhds hz))
        (fun z' hz' => hEq z' hz')
    have hwz : w z = Work.HypModel.mobius B z := hEq z ⟨hzV, hz⟩
    have hfd : fderiv ℝ w z = fderiv ℝ (Work.HypModel.mobius B) z := hev.fderiv_eq
    rw [hfd, hwz]
    rw [Work.RTInstance.uhsModel_eq_uhsMetric hδ₂ (by rw [← hwz]; exact h₂ z hz),
      Work.RTInstance.uhsModel_eq_uhsMetric hδ₁ (h₁ z hz)]
    exact Work.HypModel.mobius_isometry hB (lt_of_lt_of_le hδ₁ (h₁ z hz)) u v


/-! ## Elementary facts about the collar chart -/

/-- **The target of the collar chart is the box `cBoxR`.** -/
theorem cChart_target' (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (cChart a D v c δ hδ hne).target = cBoxR v c δ := by
  rw [cChart, OpenPartialHomeomorph.trans_target, cChartOf_target,
    OpenPartialHomeomorph.ofSet_target, OpenPartialHomeomorph.ofSet_symm,
    OpenPartialHomeomorph.ofSet_apply, Set.preimage_id]
  exact Set.inter_eq_left.mpr (by rw [cBoxR]; exact Set.inter_subset_left)

/-- **The inverse of the collar chart is the coordinate inclusion `cuspCoordMTop`.** -/
theorem fc_cChart_symm_apply (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (q : E4) (hq : q ∈ cBoxR v c δ) :
    (cChart a D v c δ hδ hne).symm q = Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq.1⟩ := by
  have hsrc : Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq.1⟩ ∈
      (cChart a D v c δ hδ hne).source := by
    rw [cChart_source]
    exact ⟨⟨q, hq.1⟩, hq, rfl⟩
  have hval := cChart_apply a D v c δ hδ hne q hq.1 hq
  have h := OpenPartialHomeomorph.left_inv (cChart a D v c δ hδ hne) hsrc
  rwa [hval] at h

/-! ## The upper half space branching of `cuspCoordMTop` -/

/-- **Below the ceiling** `cuspCoordMTop` is `incMbar ∘ mbarLow`. -/
theorem cuspCoordMTop_eq_incMbar_of_lt (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (c : Work.Cusp.E3) (δ : ℝ)
    (q : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (h : (q : Work.Cusp.E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (q : Work.Cusp.E4))) :
    Work.Cusp.cuspCoordMTop a v D c δ q = a.incMbar (D.mbarLow q.1) := by
  rw [Work.Cusp.cuspCoordMTop, dite_eq_left h]

/-- **Above the ceiling** `cuspCoordMTop` lands in a filling piece. -/
theorem cuspCoordMTop_eq_incY_of_not_lt (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (c : Work.Cusp.E3) (δ : ℝ)
    (q : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (h : ¬ (q : Work.Cusp.E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (q : Work.Cusp.E4))) :
    ∃ y : a.Y, Work.Cusp.cuspCoordMTop a v D c δ q = a.incY y := by
  rw [Work.Cusp.cuspCoordMTop, dite_eq_right h]
  exact ⟨_, rfl⟩

/-- **Above the ceiling** the values of `cuspCoordMTop` hit `M̄` only on the cusped boundary. -/
theorem cuspCoordMTop_mem_Tset_of_not_lt (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (c : Work.Cusp.E3) (δ : ℝ)
    (q : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (h : ¬ (q : Work.Cusp.E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (q : Work.Cusp.E4)))
    {x : a.Mbar} (hx : Work.Cusp.cuspCoordMTop a v D c δ q = a.incMbar x) : x ∈ a.Tset := by
  obtain ⟨y, hy⟩ := cuspCoordMTop_eq_incY_of_not_lt a v D c δ q h
  by_contra hcon
  exact a.incMbar_ne_incY (fun ⟨hxT, _⟩ => hcon hxT) (hx.symm.trans hy)

/-- The height of a point of the target of a fold chart of a `FoldData`. -/
theorem foldData_target_height {a : Work.Space.Assembly} (F : Work.RTInstance.FoldData a)
    (i : Fin F.nF) {z : E4} (hz : z ∈ (F.foldM i).target) : F.δ ≤ z 3 := by
  have hzt : z ∈ (F.foldChart i).target := by rwa [Work.RTInstance.FoldData.foldM_target] at hz
  have hsrc : (F.foldChart i).symm z ∈ (F.foldChart i).source := (F.foldChart i).map_target hzt
  have hok := F.fold_ok i hsrc
  have h1 : (F.foldChart i) ((F.foldChart i).symm z) = z := (F.foldChart i).right_inv hzt
  rw [h1] at hok
  obtain ⟨-, h2⟩ := hok
  exact le_of_lt h2

/-! ## The structure of the two transition sources -/

/-- **The structure of the source of the fold → collar transition.**  A point of the source is a
value of the transported fold chart `foldM i` whose underlying point of `M̄` is `mbarLow q` for a
collar coordinate `q` *strictly below the ceiling*; the transition value is that coordinate `q`. -/
theorem foldCTransSrc_exists (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2) (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {z : E4} (hz : z ∈ foldCTransSrc g D i v c δ hδ hne) :
    ∃ q : E4,
      q ∈ Work.Cusp.cuspBoxTop v c δ ∧ q ∈ cBoxR v c δ ∧
        q 3 < Work.Cusp.beta (Work.Cusp.xOf q) ∧
        (D v).mbarLow q = ((foldDataOf g).foldChart i).symm z ∧
        foldCTransMap g D i v c δ hδ hne z = q := by
  classical
  have hz0 : z ∈ (((foldDataOf g).foldM i).symm ≫ₕ
      cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).source := hz
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz0
  obtain ⟨hz1, hz2⟩ := hz0
  have hsym := Work.RTInstance.FoldData.foldM_symm (foldDataOf g) i hz1
  rw [cChart_source] at hz2
  obtain ⟨q, hqR, hqeq⟩ := hz2
  rw [hsym] at hqeq
  have hxs : ((foldDataOf g).foldChart i).symm z ∈ ((foldDataOf g).foldChart i).source := by
    have hzt : z ∈ ((foldDataOf g).foldChart i).target := by
      rwa [Work.RTInstance.FoldData.foldM_target] at hz1
    exact ((foldDataOf g).foldChart i).map_target hzt
  by_cases hq3 : (q : E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (q : E4))
  · have hbranch := cuspCoordMTop_eq_incMbar_of_lt (Work.RTInstance.assemblyOf g) v (D v) c δ q hq3
    have hmb : (D v).mbarLow (q : E4) = ((foldDataOf g).foldChart i).symm z := by
      have h2 : (Work.RTInstance.assemblyOf g).incMbar ((D v).mbarLow (q : E4))
          = (Work.RTInstance.assemblyOf g).incMbar (((foldDataOf g).foldChart i).symm z) := by
        rw [← hbranch, hqeq]
      exact Work.Space.Assembly.incMbar_injective _ h2
    refine ⟨(q : E4), q.2, hqR, hq3, hmb, ?_⟩
    show cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne
      (((foldDataOf g).foldM i).symm z) = (q : E4)
    rw [hsym, ← hqeq, cChart_apply (Work.RTInstance.assemblyOf g) D v c δ hδ hne (q : E4) q.2 hqR]
  · have hTset : ((foldDataOf g).foldChart i).symm z ∈ (Work.RTInstance.assemblyOf g).Tset :=
      cuspCoordMTop_mem_Tset_of_not_lt (Work.RTInstance.assemblyOf g) v (D v) c δ q hq3 hqeq
    exact absurd hTset ((Work.RTInstance.FoldData.fold_source (foldDataOf g) i) hxs)

/-- **The structure of the source of the collar → fold transition.**  A point of the source is a
collar coordinate `q` strictly below the ceiling; the transition value is the fold chart value of
`mbarLow q`. -/
theorem cFoldTransSrc_exists (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2) (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q : E4} (hq : q ∈ cFoldTransSrc g D i v c δ hδ hne) :
    q ∈ cBoxR v c δ ∧ q 3 < Work.Cusp.beta (Work.Cusp.xOf q) ∧
      (D v).mbarLow q ∈ (Work.FoldInst.foldChart i).source ∧
      cFoldTransMap g D i v c δ hδ hne q = (Work.FoldInst.foldChart i) ((D v).mbarLow q) := by
  classical
  have hq0 : q ∈ ((cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).symm ≫ₕ
      (foldDataOf g).foldM i).source := hq
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hq0
  obtain ⟨hq1, hq2⟩ := hq0
  have hqR : q ∈ cBoxR v c δ := by
    rw [← cChart_target' (Work.RTInstance.assemblyOf g) D v c δ hδ hne]
    exact hq1
  have hsymC := fc_cChart_symm_apply (Work.RTInstance.assemblyOf g) D v c δ hδ hne q hqR
  rw [Set.mem_preimage] at hq2
  rw [hsymC] at hq2
  rw [Work.RTInstance.FoldData.foldM_source] at hq2
  obtain ⟨x, hxsrc, hxeq⟩ := hq2
  have hxT : (Work.RTInstance.assemblyOf g).incMbar x
      = Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c δ ⟨q, hqR.1⟩ := hxeq
  by_cases hq3 : q 3 < Work.Cusp.beta (Work.Cusp.xOf q)
  · have hbranch := cuspCoordMTop_eq_incMbar_of_lt (Work.RTInstance.assemblyOf g) v (D v) c δ
      ⟨q, hqR.1⟩ hq3
    have hlow : x = (D v).mbarLow q := by
      apply Work.Space.Assembly.incMbar_injective (Work.RTInstance.assemblyOf g)
      rw [hbranch] at hxT
      exact hxT
    have hsrc : (D v).mbarLow q ∈ (Work.FoldInst.foldChart i).source := by
      rw [← hlow]; exact hxsrc
    refine ⟨hqR, hq3, hsrc, ?_⟩
    show (foldDataOf g).foldM i
      ((cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).symm q)
        = (Work.FoldInst.foldChart i) ((D v).mbarLow q)
    rw [hsymC, cuspCoordMTop_eq_incMbar_of_lt (Work.RTInstance.assemblyOf g) v (D v) c δ
      ⟨q, hqR.1⟩ hq3]
    exact Work.RTInstance.FoldData.foldM_apply (foldDataOf g) i hsrc
  · have hTset : x ∈ (Work.RTInstance.assemblyOf g).Tset :=
      cuspCoordMTop_mem_Tset_of_not_lt (Work.RTInstance.assemblyOf g) v (D v) c δ
        ⟨q, hqR.1⟩ hq3 hxT.symm
    exact absurd hTset ((Work.RTInstance.FoldData.fold_source (foldDataOf g) i) hxsrc)

/-! ## The local Möbius form of the two transitions -/

/-- **The fold → collar transition is locally the inverse Möbius map.**

At a point `z` of the source, `z = foldChart i (mbarLow q)` where `q` is the collar coordinate
strictly below the ceiling, and `CuspRigid.foldLocal` gives `foldChart i ∘ mbarLow = mobius B` near
`q`; hence the transition is `mobius B⁻¹` near `z` (the heights control ensures that every point of
a small neighbourhood of `z` still maps into the neighbourhood of `q`). -/
theorem foldCTrans_local (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2) (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {z : E4} (hz : z ∈ foldCTransSrc g D i v c δ hδ hne) :
    ∃ (V : Set E4) (B : Matrix (Fin 5) (Fin 5) ℝ), IsOpen V ∧ z ∈ V ∧
      Work.HypModel.IsLorentzMat B ∧
      ∀ z' ∈ V ∩ foldCTransSrc g D i v c δ hδ hne,
        foldCTransMap g D i v c δ hδ hne z' = Work.HypModel.mobius B z' := by
  classical
  obtain ⟨q, -, hqR, hq3, hmb, hTz⟩ := foldCTransSrc_exists g D i v c δ hδ hne hz
  have hgt : (11 : ℝ)/10 < q 3 := by
    have h := hqR.1.2.1
    simpa [Work.Cusp.s1] using h
  have hsrc : (D v).mbarLow q ∈ (Work.FoldInst.foldChart i).source := by
    rw [hmb]
    have hzt : z ∈ ((foldDataOf g).foldChart i).target := by
      have h1 := hz
      rw [foldCTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Work.RTInstance.FoldData.foldM_target] at h1
      exact h1.1
    exact ((foldDataOf g).foldChart i).map_target hzt
  obtain ⟨V₀, B, hV₀open, hqV₀, hB, hfoldlocal⟩ := (R v).foldLocal i hgt hq3 hsrc
  have hcont : ContinuousWithinAt (fun z' => foldCTransMap g D i v c δ hδ hne z')
      (foldCTransSrc g D i v c δ hδ hne) z :=
    (OpenPartialHomeomorph.continuousOn (((foldDataOf g).foldM i).symm ≫ₕ
      cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne)).continuousWithinAt hz
  have hnb : (fun z' => foldCTransMap g D i v c δ hδ hne z') ⁻¹' V₀ ∈
      𝓝[foldCTransSrc g D i v c δ hδ hne] z :=
    hcont (hV₀open.mem_nhds (by simpa only [hTz] using hqV₀))
  obtain ⟨V, hVopen, hzV, hVsub⟩ := mem_nhdsWithin.mp hnb
  refine ⟨V, B⁻¹, hVopen, hzV, Work.FoldInst.isLorentzMat_inv hB, ?_⟩
  intro z' hz'
  obtain ⟨hz'V, hz'S⟩ := hz'
  have hz'V₀ : foldCTransMap g D i v c δ hδ hne z' ∈ V₀ := hVsub ⟨hz'V, hz'S⟩
  obtain ⟨q', -, hq'R, -, hq'mb, hq'Tz'⟩ := foldCTransSrc_exists g D i v c δ hδ hne hz'S
  have hz'tgt : z' ∈ ((foldDataOf g).foldChart i).target := by
    have h1 := hz'S
    rw [foldCTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Work.RTInstance.FoldData.foldM_target] at h1
    exact h1.1
  have hq'src : (D v).mbarLow (foldCTransMap g D i v c δ hδ hne z') ∈
      (Work.FoldInst.foldChart i).source := by
    rw [hq'Tz', hq'mb]
    exact ((foldDataOf g).foldChart i).map_target hz'tgt
  have hstep := hfoldlocal (foldCTransMap g D i v c δ hδ hne z') hz'V₀ hq'src
  have hzeq : z' = Work.HypModel.mobius B (foldCTransMap g D i v c δ hδ hne z') := by
    calc z' = ((foldDataOf g).foldChart i) (((foldDataOf g).foldChart i).symm z') :=
          (((foldDataOf g).foldChart i).right_inv hz'tgt).symm
      _ = ((foldDataOf g).foldChart i) ((D v).mbarLow q') := by rw [hq'mb]
      _ = ((foldDataOf g).foldChart i)
            ((D v).mbarLow (foldCTransMap g D i v c δ hδ hne z')) := by rw [← hq'Tz']
      _ = Work.HypModel.mobius B (foldCTransMap g D i v c δ hδ hne z') := hstep
  have hpos : 0 < foldCTransMap g D i v c δ hδ hne z' 3 := by
    rw [hq'Tz']
    have h := hq'R.1.2.1
    have h2 : (11 : ℝ)/10 < q' 3 := by simpa [Work.Cusp.s1] using h
    linarith
  exact (mobius_inv_apply hB hpos).symm.trans
    (congrArg (Work.HypModel.mobius B⁻¹) hzeq).symm

/-- **The collar → fold transition is locally the Möbius map itself.** -/
theorem cFoldTrans_local (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2) (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q : E4} (hq : q ∈ cFoldTransSrc g D i v c δ hδ hne) :
    ∃ (V : Set E4) (B : Matrix (Fin 5) (Fin 5) ℝ), IsOpen V ∧ q ∈ V ∧
      Work.HypModel.IsLorentzMat B ∧
      ∀ q' ∈ V ∩ cFoldTransSrc g D i v c δ hδ hne,
        cFoldTransMap g D i v c δ hδ hne q' = Work.HypModel.mobius B q' := by
  classical
  obtain ⟨hqR, hq3, hsrc, -⟩ := cFoldTransSrc_exists g D i v c δ hδ hne hq
  have hgt : (11 : ℝ)/10 < q 3 := by
    have h := hqR.1.2.1
    simpa [Work.Cusp.s1] using h
  obtain ⟨V, B, hVopen, hqV, hB, hfoldlocal⟩ := (R v).foldLocal i hgt hq3 hsrc
  refine ⟨V, B, hVopen, hqV, hB, ?_⟩
  intro q' hq'
  obtain ⟨hq'V, hq'S⟩ := hq'
  obtain ⟨-, -, hq'src, hq'val⟩ := cFoldTransSrc_exists g D i v c δ hδ hne hq'S
  rw [hq'val]
  exact hfoldlocal q' hq'V hq'src

/-! ## The fold–collar transitions -/

/-- **The fold–collar transitions of the atlas of `M̂` are smooth and isometric.**

Both transitions are locally Möbius (`foldCTrans_local`, `cFoldTrans_local`), so the engine
`transIso2_uhs_of_localMobius` applies: the two layers `uhsModel (foldDataOf g).δ` and
`cLayer.model = uhsModel cδ` are the total upper half space models of the fold charts and of the
collar box, and the relevant heights are controlled by `fold_ok` and by the collar box. -/
theorem foldTrans_coll (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (i : Fin (Work.RTOwed.foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2) (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    Work.RTOwed.TransIso2 (Work.RTInstance.uhsModel (Work.RTOwed.foldDataOf g).δ)
        Work.RTOwed.cLayer.model
        (Work.RTOwed.foldCTransMap g D i v c δ hδ hne)
        (Work.RTOwed.foldCTransSrc g D i v c δ hδ hne) ∧
      Work.RTOwed.TransIso2 Work.RTOwed.cLayer.model
        (Work.RTInstance.uhsModel (Work.RTOwed.foldDataOf g).δ)
        (Work.RTOwed.cFoldTransMap g D i v c δ hδ hne)
        (Work.RTOwed.cFoldTransSrc g D i v c δ hδ hne) := by
  constructor
  · have hS : IsOpen (foldCTransSrc g D i v c δ hδ hne) :=
      show IsOpen (((foldDataOf g).foldM i).symm ≫ₕ
        cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).source from
        OpenPartialHomeomorph.open_source _
    have h₁ : ∀ z ∈ foldCTransSrc g D i v c δ hδ hne, (foldDataOf g).δ ≤ z 3 := by
      intro z hz
      exact foldData_target_height (foldDataOf g) i (by
        have h1 := hz
        rw [foldCTransSrc, OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.symm_source] at h1
        exact h1.1)
    have h₂ : ∀ z ∈ foldCTransSrc g D i v c δ hδ hne,
        cδ ≤ foldCTransMap g D i v c δ hδ hne z 3 := by
      intro z hz
      have hmem : foldCTransMap g D i v c δ hδ hne z ∈
          (cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).target :=
        (cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).map_source (by
          have h1 := hz
          rw [foldCTransSrc, OpenPartialHomeomorph.trans_source] at h1
          exact h1.2)
      rw [cChart_target'] at hmem
      exact le_of_lt (by simpa [cδ, Work.Cusp.s1] using hmem.1.2.1)
    exact transIso2_uhs_of_localMobius (w := foldCTransMap g D i v c δ hδ hne)
      (S := foldCTransSrc g D i v c δ hδ hne) (δ₁ := (foldDataOf g).δ) (δ₂ := cδ)
      (foldDataOf g).hδ cδ_pos hS h₁ h₂
      (fun z hz => foldCTrans_local g D R i v c δ hδ hne hz)
  · have hS : IsOpen (cFoldTransSrc g D i v c δ hδ hne) :=
      show IsOpen ((cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).symm ≫ₕ
        (foldDataOf g).foldM i).source from OpenPartialHomeomorph.open_source _
    have h₁ : ∀ z ∈ cFoldTransSrc g D i v c δ hδ hne, cδ ≤ z 3 := by
      intro z hz
      have hmem : z ∈ (cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).target := by
        have h1 := hz
        rw [cFoldTransSrc, OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.symm_source] at h1
        exact h1.1
      rw [cChart_target'] at hmem
      exact le_of_lt (by simpa [cδ, Work.Cusp.s1] using hmem.1.2.1)
    have h₂ : ∀ z ∈ cFoldTransSrc g D i v c δ hδ hne,
        (foldDataOf g).δ ≤ cFoldTransMap g D i v c δ hδ hne z 3 := by
      intro z hz
      have hmem : cFoldTransMap g D i v c δ hδ hne z ∈ ((foldDataOf g).foldM i).target :=
        ((foldDataOf g).foldM i).map_source (by
          have h1 := hz
          rw [cFoldTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
            at h1
          exact h1.2)
      exact foldData_target_height (foldDataOf g) i hmem
    exact transIso2_uhs_of_localMobius (w := cFoldTransMap g D i v c δ hδ hne)
      (S := cFoldTransSrc g D i v c δ hδ hne) (δ₁ := cδ) (δ₂ := (foldDataOf g).δ)
      cδ_pos (foldDataOf g).hδ hS h₁ h₂
      (fun z hz => cFoldTrans_local g D R i v c δ hδ hne hz)


/-! ## The transition facts, from the available sources -/

theorem jjTransIso2_ph : ∀ (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : Work.RTOwed.JPin a v),
    Work.RTOwed.TransIso2 (Work.RTOwed.jLayer v).model (Work.RTOwed.jLayer v).model
      (Work.RTOwed.jjTransMap a D v P Q) (Work.RTOwed.jjTransSrc a D v P Q) :=
  Work.RTOwed.jjTransIso2

theorem ccTransIso2_ph : ∀ (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (v v' : Work.Space.Cusp)
    (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1/2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1/2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂}),
    Work.RTOwed.TransIso2 Work.RTOwed.cLayer.model Work.RTOwed.cLayer.model
      (Work.RTOwed.ccTransMap (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂)
      (Work.RTOwed.ccTransSrc (Work.RTInstance.assemblyOf g) D v c₁ δ₁ hδ₁ hne₁ v' c₂ δ₂ hδ₂ hne₂) :=
  Work.RTOwed.ccTransIso2

theorem foldTransCollIso2_ph (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (i : Fin (Work.RTOwed.foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2) (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    Work.RTOwed.TransIso2 (Work.RTInstance.uhsModel (Work.RTOwed.foldDataOf g).δ)
        Work.RTOwed.cLayer.model
        (Work.RTOwed.foldCTransMap g D i v c δ hδ hne)
        (Work.RTOwed.foldCTransSrc g D i v c δ hδ hne) ∧
      Work.RTOwed.TransIso2 Work.RTOwed.cLayer.model
        (Work.RTInstance.uhsModel (Work.RTOwed.foldDataOf g).δ)
        (Work.RTOwed.cFoldTransMap g D i v c δ hδ hne)
        (Work.RTOwed.cFoldTransSrc g D i v c δ hδ hne) :=
  foldTrans_coll g D R i v c δ hδ hne

theorem jkTransIso2_ph (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : Work.RTOwed.JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Work.RTOwed.TransIso2 (Work.RTOwed.jLayer v).model (Work.RTOwed.kLayer v).model
        (Work.RTOwed.jkTransMap a D (fun w => (D w).tor) v P W hW hsec)
        (Work.RTOwed.jkTransSrc a D (fun w => (D w).tor) v P W hW hsec) ∧
      Work.RTOwed.TransIso2 (Work.RTOwed.kLayer v).model (Work.RTOwed.jLayer v).model
        (Work.RTOwed.kjTransMap a D (fun w => (D w).tor) v P W hW hsec)
        (Work.RTOwed.kjTransSrc a D (fun w => (D w).tor) v P W hW hsec) :=
  Work.RTOwed.jkTransIso2 a D v P W hW hsec
/-! ## Index bookkeeping for the four chart families -/

def fcB1 (n₁ n₂ n₃ n₄ : ℕ) : Fin n₁ → Fin (n₁ + (n₂ + (n₃ + n₄))) :=
  Fin.castAdd (n₂ + (n₃ + n₄))

def fcB2 (n₁ n₂ n₃ n₄ : ℕ) : Fin n₂ → Fin (n₁ + (n₂ + (n₃ + n₄))) :=
  fun i => Fin.natAdd n₁ (Fin.castAdd (n₃ + n₄) i)

def fcB3 (n₁ n₂ n₃ n₄ : ℕ) : Fin n₃ → Fin (n₁ + (n₂ + (n₃ + n₄))) :=
  fun i => Fin.natAdd n₁ (Fin.natAdd n₂ (Fin.castAdd n₄ i))

def fcB4 (n₁ n₂ n₃ n₄ : ℕ) : Fin n₄ → Fin (n₁ + (n₂ + (n₃ + n₄))) :=
  fun i => Fin.natAdd n₁ (Fin.natAdd n₂ (Fin.natAdd n₃ i))

def fc_addCases4 {n₁ n₂ n₃ n₄ : ℕ}
    {motive : Fin (n₁ + (n₂ + (n₃ + n₄))) → Sort*}
    (h₁ : ∀ i : Fin n₁, motive (Fin.castAdd (n₂ + (n₃ + n₄)) i))
    (h₂ : ∀ i : Fin n₂, motive (Fin.natAdd n₁ (Fin.castAdd (n₃ + n₄) i)))
    (h₃ : ∀ i : Fin n₃, motive (Fin.natAdd n₁ (Fin.natAdd n₂ (Fin.castAdd n₄ i))))
    (h₄ : ∀ i : Fin n₄, motive (Fin.natAdd n₁ (Fin.natAdd n₂ (Fin.natAdd n₃ i)))) :
    ∀ i, motive i := by
  intro i
  refine Fin.addCases (motive := motive) h₁ ?_ i
  intro j
  refine Fin.addCases (motive := fun j => motive (Fin.natAdd n₁ j)) h₂ ?_ j
  intro k
  refine Fin.addCases (motive := fun k => motive (Fin.natAdd n₁ (Fin.natAdd n₂ k))) h₃ ?_ k
  intro l
  exact h₄ l

def fc_pair4 {n₁ n₂ n₃ n₄ : ℕ}
    {motive : Fin (n₁ + (n₂ + (n₃ + n₄))) → Fin (n₁ + (n₂ + (n₃ + n₄))) → Sort*}
    (h₁₁ : ∀ i j : Fin n₁, motive (fcB1 n₁ n₂ n₃ n₄ i) (fcB1 n₁ n₂ n₃ n₄ j))
    (h₁₂ : ∀ i : Fin n₁, ∀ j : Fin n₂, motive (fcB1 n₁ n₂ n₃ n₄ i) (fcB2 n₁ n₂ n₃ n₄ j))
    (h₁₃ : ∀ i : Fin n₁, ∀ j : Fin n₃, motive (fcB1 n₁ n₂ n₃ n₄ i) (fcB3 n₁ n₂ n₃ n₄ j))
    (h₁₄ : ∀ i : Fin n₁, ∀ j : Fin n₄, motive (fcB1 n₁ n₂ n₃ n₄ i) (fcB4 n₁ n₂ n₃ n₄ j))
    (h₂₁ : ∀ i : Fin n₂, ∀ j : Fin n₁, motive (fcB2 n₁ n₂ n₃ n₄ i) (fcB1 n₁ n₂ n₃ n₄ j))
    (h₂₂ : ∀ i j : Fin n₂, motive (fcB2 n₁ n₂ n₃ n₄ i) (fcB2 n₁ n₂ n₃ n₄ j))
    (h₂₃ : ∀ i : Fin n₂, ∀ j : Fin n₃, motive (fcB2 n₁ n₂ n₃ n₄ i) (fcB3 n₁ n₂ n₃ n₄ j))
    (h₂₄ : ∀ i : Fin n₂, ∀ j : Fin n₄, motive (fcB2 n₁ n₂ n₃ n₄ i) (fcB4 n₁ n₂ n₃ n₄ j))
    (h₃₁ : ∀ i : Fin n₃, ∀ j : Fin n₁, motive (fcB3 n₁ n₂ n₃ n₄ i) (fcB1 n₁ n₂ n₃ n₄ j))
    (h₃₂ : ∀ i : Fin n₃, ∀ j : Fin n₂, motive (fcB3 n₁ n₂ n₃ n₄ i) (fcB2 n₁ n₂ n₃ n₄ j))
    (h₃₃ : ∀ i j : Fin n₃, motive (fcB3 n₁ n₂ n₃ n₄ i) (fcB3 n₁ n₂ n₃ n₄ j))
    (h₃₄ : ∀ i : Fin n₃, ∀ j : Fin n₄, motive (fcB3 n₁ n₂ n₃ n₄ i) (fcB4 n₁ n₂ n₃ n₄ j))
    (h₄₁ : ∀ i : Fin n₄, ∀ j : Fin n₁, motive (fcB4 n₁ n₂ n₃ n₄ i) (fcB1 n₁ n₂ n₃ n₄ j))
    (h₄₂ : ∀ i : Fin n₄, ∀ j : Fin n₂, motive (fcB4 n₁ n₂ n₃ n₄ i) (fcB2 n₁ n₂ n₃ n₄ j))
    (h₄₃ : ∀ i : Fin n₄, ∀ j : Fin n₃, motive (fcB4 n₁ n₂ n₃ n₄ i) (fcB3 n₁ n₂ n₃ n₄ j))
    (h₄₄ : ∀ i j : Fin n₄, motive (fcB4 n₁ n₂ n₃ n₄ i) (fcB4 n₁ n₂ n₃ n₄ j)) :
    ∀ i j, motive i j := by
  intro i
  refine fc_addCases4 (motive := fun i => ∀ j, motive i j) ?_ ?_ ?_ ?_ i
  · intro p
    exact fc_addCases4 (motive := fun j => motive (fcB1 n₁ n₂ n₃ n₄ p) j)
      (h₁₁ p) (h₁₂ p) (h₁₃ p) (h₁₄ p)
  · intro p
    exact fc_addCases4 (motive := fun j => motive (fcB2 n₁ n₂ n₃ n₄ p) j)
      (h₂₁ p) (h₂₂ p) (h₂₃ p) (h₂₄ p)
  · intro p
    exact fc_addCases4 (motive := fun j => motive (fcB3 n₁ n₂ n₃ n₄ p) j)
      (h₃₁ p) (h₃₂ p) (h₃₃ p) (h₃₄ p)
  · intro p
    exact fc_addCases4 (motive := fun j => motive (fcB4 n₁ n₂ n₃ n₄ p) j)
      (h₄₁ p) (h₄₂ p) (h₄₃ p) (h₄₄ p)

theorem fc_notMem_of_empty {α : Type*} {S T : Set α} (hd : S ∩ T = ∅) {x : α}
    (hx : x ∈ S) (hy : x ∈ T) : False := by
  have h : x ∈ S ∩ T := ⟨hx, hy⟩
  rw [hd] at h
  exact h

/-! ## Generic helpers relating `TransIso2` to chart transitions -/

theorem fc_trans_src_eq_empty {α : Type*} [TopologicalSpace α]
    {e₁ e₂ : OpenPartialHomeomorph α E4} (h : e₁.source ∩ e₂.source = ∅) :
    (e₁.symm ≫ₕ e₂).source = ∅ := by
  rw [← Set.subset_empty_iff]
  intro q hq
  rw [OpenPartialHomeomorph.trans_source] at hq
  have h1 : e₁.symm q ∈ e₁.source ∩ e₂.source := ⟨e₁.map_target hq.1, hq.2⟩
  rw [h] at h1
  exact h1

theorem fc_transIso2_of_empty {m₁ m₂ : E4 → E4 →L[ℝ] E4 →L[ℝ] ℝ} {t : E4 → E4} {S : Set E4}
    (hS : S = ∅) : TransIso2 m₁ m₂ t S := by
  rw [hS]
  exact ⟨contDiffOn_empty, fun q hq => absurd hq (Set.notMem_empty q)⟩

theorem fc_contDiffOn_of_empty {f : E4 → E4} {S : Set E4} (hS : S = ∅) :
    ContDiffOn ℝ ∞ f S := by
  rw [hS]; exact contDiffOn_empty

theorem fc_transIso2_pair {α : Type*} [TopologicalSpace α]
    {m₁ m₂ : E4 → E4 →L[ℝ] E4 →L[ℝ] ℝ}
    {e₁ e₂ : OpenPartialHomeomorph α E4}
    (h : TransIso2 m₁ m₂ ((e₂ : α → E4) ∘ e₁.symm) ((e₁.symm ≫ₕ e₂).source)) :
    ContDiffOn ℝ ∞ ((e₂ : α → E4) ∘ e₁.symm) ((e₁.symm ≫ₕ e₂).source) ∧
    ∀ ⦃y : α⦄, y ∈ e₁.source → y ∈ e₂.source → ∀ u v : E4,
      m₂ (e₂ y) (fderiv ℝ ((e₂ : α → E4) ∘ e₁.symm) (e₁ y) u)
                (fderiv ℝ ((e₂ : α → E4) ∘ e₁.symm) (e₁ y) v) = m₁ (e₁ y) u v := by
  refine ⟨h.1, ?_⟩
  intro y hy₁ hy₂ u v
  have hsymm : (e₁.symm) (e₁ y) = y := OpenPartialHomeomorph.left_inv e₁ hy₁
  have hq : e₁ y ∈ (e₁.symm ≫ₕ e₂).source := by
    refine ⟨e₁.map_source hy₁, ?_⟩
    show (e₁.symm) (e₁ y) ∈ e₂.source
    rw [hsymm]; exact hy₂
  have hkey := h.2 hq u v
  simpa only [Function.comp_apply, hsymm] using hkey

/-! ## Two-cusp forms of the same-cusp transitions -/

theorem fc_jj (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v v' : Work.Space.Cusp) (hv : v = v')
    (P : Work.RTOwed.JPin a v) (Q : Work.RTOwed.JPin a v') :
    TransIso2 (jLayer v).model (jLayer v').model
      (fun q => jChart a D v' Q ((jChart a D v P).symm q))
      ((jChart a D v P).symm ≫ₕ jChart a D v' Q).source := by
  subst hv
  exact jjTransIso2_ph a D _ P Q

theorem fc_jc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v v' : Work.Space.Cusp) (hv : v = v') (P : Work.RTOwed.JPin a v)
    (c : Work.Cusp.E3) (δc : ℝ) (hδ : δc ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c δc}) :
    TransIso2 (jLayer v).model cLayer.model
      (fun q => cChart a D v' c δc hδ hne ((jChart a D v P).symm q))
      ((jChart a D v P).symm ≫ₕ cChart a D v' c δc hδ hne).source := by
  subst hv
  exact (jTrans_coll_iso a D _ P c δc hδ hne).1

theorem fc_cj (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v v' : Work.Space.Cusp) (hv : v = v') (P : Work.RTOwed.JPin a v')
    (c : Work.Cusp.E3) (δc : ℝ) (hδ : δc ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δc}) :
    TransIso2 cLayer.model (jLayer v').model
      (fun q => jChart a D v' P ((cChart a D v c δc hδ hne).symm q))
      ((cChart a D v c δc hδ hne).symm ≫ₕ jChart a D v' P).source := by
  subst hv
  exact (jTrans_coll_iso a D _ P c δc hδ hne).2

theorem fc_jk (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v v' : Work.Space.Cusp) (hv : v = v') (P : Work.RTOwed.JPin a v)
    (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v' y ∈ W → Work.Cusp.wOf v' y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    TransIso2 (jLayer v).model (kLayer v').model
      (fun q => kChartOf a (fun w => (D w).tor) v' W hW hsec ((jChart a D v P).symm q))
      ((jChart a D v P).symm ≫ₕ kChartOf a (fun w => (D w).tor) v' W hW hsec).source := by
  subst hv
  exact (jkTransIso2_ph a D _ P W hW hsec).1

theorem fc_kj (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v v' : Work.Space.Cusp) (hv : v = v') (P : Work.RTOwed.JPin a v')
    (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    TransIso2 (kLayer v).model (jLayer v').model
      (fun q => jChart a D v' P ((kChartOf a (fun w => (D w).tor) v W hW hsec).symm q))
      ((kChartOf a (fun w => (D w).tor) v W hW hsec).symm ≫ₕ jChart a D v' P).source := by
  subst hv
  exact (jkTransIso2_ph a D _ P W hW hsec).2

theorem fc_kk (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v v' : Work.Space.Cusp) (hv : v = v')
    (W₁ : Set Work.Cusp.E2) (hW₁ : IsOpen W₁)
    (hsec₁ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₁ → Work.Cusp.wOf v y' ∈ W₁ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (W₂ : Set Work.Cusp.E2) (hW₂ : IsOpen W₂)
    (hsec₂ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v' y ∈ W₂ → Work.Cusp.wOf v' y' ∈ W₂ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    TransIso2 (kLayer v).model (kLayer v').model
      (fun q => kChartOf a (fun w => (D w).tor) v' W₂ hW₂ hsec₂
        ((kChartOf a (fun w => (D w).tor) v W₁ hW₁ hsec₁).symm q))
      ((kChartOf a (fun w => (D w).tor) v W₁ hW₁ hsec₁).symm ≫ₕ
        kChartOf a (fun w => (D w).tor) v' W₂ hW₂ hsec₂).source := by
  subst hv
  exact (coreTrans a (fun w => (D w).tor) _ W₁ W₂ hW₁ hW₂ hsec₁ hsec₂).1

theorem fc_kc_empty (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v v' : Work.Space.Cusp) (hv : v = v')
    (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (c : Work.Cusp.E3) (δc : ℝ) (hδ : δc ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c δc}) :
    (kChartOf a tor v W hW hsec).source ∩ (cChart a D v' c δc hδ hne).source = ∅ := by
  subst hv
  exact kcInter_empty a D tor _ W hW hsec c δc hδ hne

/-! ## The assembly theorem -/

theorem fillCross_of_covers (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (N₁ : ℕ) (par₁ : Fin N₁ → Σ v : Work.Space.Cusp,
      Work.RTOwed.JPin (Work.RTInstance.assemblyOf g) v)
    (hpol : ∀ (v : Work.Space.Cusp)
      (q : Work.Space.SquarePt × (Work.RTInstance.assemblyOf g).Torus v),
      q ∈ Work.Cusp.polarLayer ((Work.RTInstance.assemblyOf g).Torus v) →
      Work.Cusp.nrm (q.1 : Work.Cusp.E2) < 1/2 →
      ∃ i, (par₁ i).1 = v ∧ (Work.RTInstance.assemblyOf g).incW v q ∈
        (Work.RTOwed.jChart (Work.RTInstance.assemblyOf g) D (par₁ i).1 (par₁ i).2).source)
    (N₂ : ℕ) (par₂ : Fin N₂ → Σ v : Work.Space.Cusp,
      Work.RTOwed.JPin (Work.RTInstance.assemblyOf g) v)
    (hcol : ∀ (v : Work.Space.Cusp)
      (q : Work.Space.SquarePt × (Work.RTInstance.assemblyOf g).Torus v),
      q ∈ Work.Cusp.collarLayer ((Work.RTInstance.assemblyOf g).Torus v) →
      Work.Cusp.nrm (q.1 : Work.Cusp.E2) ≤ 51/100 →
      ∃ i, (par₂ i).1 = v ∧ (Work.RTInstance.assemblyOf g).incW v q ∈
        (Work.RTOwed.jChart (Work.RTInstance.assemblyOf g) D (par₂ i).1 (par₂ i).2).source)
    (N₃ : ℕ) (par₃ : Fin N₃ → Σ v : Work.Space.Cusp, (Work.Cusp.E3 × ℝ))
    (hδ : ∀ i, (par₃ i).2.2 ≤ 1/2)
    (hne : ∀ i, Nonempty {q : Work.Cusp.E4 //
      q ∈ Work.Cusp.cuspBoxTop (par₃ i).1 (par₃ i).2.1 (par₃ i).2.2})
    (hccol : ∀ (v : Work.Space.Cusp)
      (q : Work.Space.SquarePt × (Work.RTInstance.assemblyOf g).Torus v),
      q ∈ Work.Cusp.collarLayer ((Work.RTInstance.assemblyOf g).Torus v) →
      Work.Cusp.nrm (q.1 : Work.Cusp.E2) > 51/100 →
      ∃ i, (par₃ i).1 = v ∧ (Work.RTInstance.assemblyOf g).incW v q ∈
        (Work.RTOwed.cChart (Work.RTInstance.assemblyOf g) D (par₃ i).1 (par₃ i).2.1
          (par₃ i).2.2 (hδ i) (hne i)).source)
    (N₄ : ℕ) (par₄ : Fin N₄ → Σ v : Work.Space.Cusp, Set Work.Cusp.E2)
    (hkop : ∀ i, IsOpen (par₄ i).2)
    (hksec : ∀ i, ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf (par₄ i).1 y ∈ (par₄ i).2 →
      Work.Cusp.wOf (par₄ i).1 y' ∈ (par₄ i).2 →
      (∀ j, ((y j : ℝ) : AddCircle (1 : ℝ)) = ((y' j : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (hcore : ∀ (v : Work.Space.Cusp)
      (q : Work.Space.SquarePt × (Work.RTInstance.assemblyOf g).Torus v),
      q ∈ Work.Cusp.coreLayer ((Work.RTInstance.assemblyOf g).Torus v) →
      ∃ i, (par₄ i).1 = v ∧ (Work.RTInstance.assemblyOf g).incW v q ∈
        (Work.RTOwed.kChartOf (Work.RTInstance.assemblyOf g) (fun w => (D w).tor)
          (par₄ i).1 (par₄ i).2 (hkop i) (hksec i)).source) :
    Nonempty (Work.RTOwed.FillCross g) := by
  classical
  let a : Work.Space.Assembly := Work.RTInstance.assemblyOf g
  let L₁ : Fin N₁ → ChartLayer := fun i => jLayer (par₁ i).1
  let L₂ : Fin N₂ → ChartLayer := fun i => jLayer (par₂ i).1
  let L₃ : Fin N₃ → ChartLayer := fun _ => cLayer
  let L₄ : Fin N₄ → ChartLayer := fun i => kLayer (par₄ i).1
  let A₁ : Fin N₁ → OpenPartialHomeomorph a.Mhat E4 :=
    fun i => jChart a D (par₁ i).1 (par₁ i).2
  let A₂ : Fin N₂ → OpenPartialHomeomorph a.Mhat E4 :=
    fun i => jChart a D (par₂ i).1 (par₂ i).2
  let A₃ : Fin N₃ → OpenPartialHomeomorph a.Mhat E4 :=
    fun i => cChart a D (par₃ i).1 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i)
  let A₄ : Fin N₄ → OpenPartialHomeomorph a.Mhat E4 :=
    fun i => kChartOf a (fun w => (D w).tor) (par₄ i).1 (par₄ i).2 (hkop i) (hksec i)
  let FCh : Fin (N₁ + (N₂ + (N₃ + N₄))) → OpenPartialHomeomorph a.Mhat E4 :=
    Fin.addCases A₁ (Fin.addCases A₂ (Fin.addCases A₃ A₄))
  let FL : Fin (N₁ + (N₂ + (N₃ + N₄))) → ChartLayer :=
    Fin.addCases L₁ (Fin.addCases L₂ (Fin.addCases L₃ L₄))
  have htrans : ∀ i j : Fin (N₁ + (N₂ + (N₃ + N₄))), TransIso2 (FL i).model (FL j).model
      (fun q => FCh j ((FCh i).symm q)) ((FCh i).symm ≫ₕ FCh j).source := by
    refine fc_pair4 (motive := fun i j => TransIso2 (FL i).model (FL j).model
      (fun q => FCh j ((FCh i).symm q)) ((FCh i).symm ≫ₕ FCh j).source)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- J₁ / J₁
      intro i j
      simp only [FCh, FL, A₁, L₁, fcB1, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₁ i).1 = (par₁ j).1
      · exact fc_jj a D (par₁ i).1 (par₁ j).1 hv (par₁ i).2 (par₁ j).2
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (jChart_source_subset a D (par₁ i).1 (par₁ i).2)
          (jChart_source_subset a D (par₁ j).1 (par₁ j).2)))
    · -- J₁ / J₂
      intro i j
      simp only [FCh, FL, A₁, A₂, L₁, L₂, fcB1, fcB2, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₁ i).1 = (par₂ j).1
      · exact fc_jj a D (par₁ i).1 (par₂ j).1 hv (par₁ i).2 (par₂ j).2
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (jChart_source_subset a D (par₁ i).1 (par₁ i).2)
          (jChart_source_subset a D (par₂ j).1 (par₂ j).2)))
    · -- J₁ / C
      intro i j
      simp only [FCh, FL, A₁, A₃, L₁, L₃, fcB1, fcB3, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₁ i).1 = (par₃ j).1
      · exact fc_jc a D (par₁ i).1 (par₃ j).1 hv (par₁ i).2 (par₃ j).2.1 (par₃ j).2.2 (hδ j) (hne j)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW_union a hv
          (jChart_source_subset a D (par₁ i).1 (par₁ i).2)
          (cChart_source_subset a D (par₃ j).1 (par₃ j).2.1 (par₃ j).2.2 (hδ j) (hne j))))
    · -- J₁ / K
      intro i j
      simp only [FCh, FL, A₁, A₄, L₁, L₄, fcB1, fcB4, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₁ i).1 = (par₄ j).1
      · exact fc_jk a D (par₁ i).1 (par₄ j).1 hv (par₁ i).2 (par₄ j).2 (hkop j) (hksec j)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (jChart_source_subset a D (par₁ i).1 (par₁ i).2)
          (kChart_source_subset a (fun w => (D w).tor) (par₄ j).1 (par₄ j).2 (hkop j) (hksec j))))
    · -- J₂ / J₁
      intro i j
      simp only [FCh, FL, A₁, A₂, L₁, L₂, fcB1, fcB2, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₂ i).1 = (par₁ j).1
      · exact fc_jj a D (par₂ i).1 (par₁ j).1 hv (par₂ i).2 (par₁ j).2
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (jChart_source_subset a D (par₂ i).1 (par₂ i).2)
          (jChart_source_subset a D (par₁ j).1 (par₁ j).2)))
    · -- J₂ / J₂
      intro i j
      simp only [FCh, FL, A₂, L₂, fcB2, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₂ i).1 = (par₂ j).1
      · exact fc_jj a D (par₂ i).1 (par₂ j).1 hv (par₂ i).2 (par₂ j).2
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (jChart_source_subset a D (par₂ i).1 (par₂ i).2)
          (jChart_source_subset a D (par₂ j).1 (par₂ j).2)))
    · -- J₂ / C
      intro i j
      simp only [FCh, FL, A₂, A₃, L₂, L₃, fcB2, fcB3, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₂ i).1 = (par₃ j).1
      · exact fc_jc a D (par₂ i).1 (par₃ j).1 hv (par₂ i).2 (par₃ j).2.1 (par₃ j).2.2 (hδ j) (hne j)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW_union a hv
          (jChart_source_subset a D (par₂ i).1 (par₂ i).2)
          (cChart_source_subset a D (par₃ j).1 (par₃ j).2.1 (par₃ j).2.2 (hδ j) (hne j))))
    · -- J₂ / K
      intro i j
      simp only [FCh, FL, A₂, A₄, L₂, L₄, fcB2, fcB4, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₂ i).1 = (par₄ j).1
      · exact fc_jk a D (par₂ i).1 (par₄ j).1 hv (par₂ i).2 (par₄ j).2 (hkop j) (hksec j)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (jChart_source_subset a D (par₂ i).1 (par₂ i).2)
          (kChart_source_subset a (fun w => (D w).tor) (par₄ j).1 (par₄ j).2 (hkop j) (hksec j))))
    · -- C / J₁
      intro i j
      simp only [FCh, FL, A₁, A₃, L₁, L₃, fcB1, fcB3, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₃ i).1 = (par₁ j).1
      · exact fc_cj a D (par₃ i).1 (par₁ j).1 hv (par₁ j).2 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (by
          rw [Set.inter_comm]
          exact inter_eq_empty_incW_union a (Ne.symm hv)
            (jChart_source_subset a D (par₁ j).1 (par₁ j).2)
            (cChart_source_subset a D (par₃ i).1 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i))))
    · -- C / J₂
      intro i j
      simp only [FCh, FL, A₂, A₃, L₂, L₃, fcB2, fcB3, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₃ i).1 = (par₂ j).1
      · exact fc_cj a D (par₃ i).1 (par₂ j).1 hv (par₂ j).2 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (by
          rw [Set.inter_comm]
          exact inter_eq_empty_incW_union a (Ne.symm hv)
            (jChart_source_subset a D (par₂ j).1 (par₂ j).2)
            (cChart_source_subset a D (par₃ i).1 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i))))
    · -- C / C
      intro i j
      simp only [FCh, FL, A₃, L₃, fcB3, Fin.addCases_left, Fin.addCases_right]
      exact ccTransIso2_ph g D R (par₃ i).1 (par₃ j).1 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i)
        (par₃ j).2.1 (par₃ j).2.2 (hδ j) (hne j)
    · -- C / K
      intro i j
      simp only [FCh, FL, A₃, A₄, L₃, L₄, fcB3, fcB4, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₄ j).1 = (par₃ i).1
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (by
          rw [Set.inter_comm]
          exact fc_kc_empty a D (fun w => (D w).tor) (par₄ j).1 (par₃ i).1 hv (par₄ j).2 (hkop j)
            (hksec j) (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i)))
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (by
          rw [Set.inter_comm]
          exact inter_eq_empty_incW_union a hv
            (kChart_source_subset a (fun w => (D w).tor) (par₄ j).1 (par₄ j).2 (hkop j) (hksec j))
            (cChart_source_subset a D (par₃ i).1 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i))))
    · -- K / J₁
      intro i j
      simp only [FCh, FL, A₁, A₄, L₁, L₄, fcB1, fcB4, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₄ i).1 = (par₁ j).1
      · exact fc_kj a D (par₄ i).1 (par₁ j).1 hv (par₁ j).2 (par₄ i).2 (hkop i) (hksec i)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (kChart_source_subset a (fun w => (D w).tor) (par₄ i).1 (par₄ i).2 (hkop i) (hksec i))
          (jChart_source_subset a D (par₁ j).1 (par₁ j).2)))
    · -- K / J₂
      intro i j
      simp only [FCh, FL, A₂, A₄, L₂, L₄, fcB2, fcB4, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₄ i).1 = (par₂ j).1
      · exact fc_kj a D (par₄ i).1 (par₂ j).1 hv (par₂ j).2 (par₄ i).2 (hkop i) (hksec i)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (kChart_source_subset a (fun w => (D w).tor) (par₄ i).1 (par₄ i).2 (hkop i) (hksec i))
          (jChart_source_subset a D (par₂ j).1 (par₂ j).2)))
    · -- K / C
      intro i j
      simp only [FCh, FL, A₃, A₄, L₃, L₄, fcB3, fcB4, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₄ i).1 = (par₃ j).1
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty
          (fc_kc_empty a D (fun w => (D w).tor) (par₄ i).1 (par₃ j).1 hv (par₄ i).2 (hkop i)
            (hksec i) (par₃ j).2.1 (par₃ j).2.2 (hδ j) (hne j)))
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW_union a hv
          (kChart_source_subset a (fun w => (D w).tor) (par₄ i).1 (par₄ i).2 (hkop i) (hksec i))
          (cChart_source_subset a D (par₃ j).1 (par₃ j).2.1 (par₃ j).2.2 (hδ j) (hne j))))
    · -- K / K
      intro i j
      simp only [FCh, FL, A₄, L₄, fcB4, Fin.addCases_left, Fin.addCases_right]
      by_cases hv : (par₄ i).1 = (par₄ j).1
      · exact fc_kk a D (par₄ i).1 (par₄ j).1 hv (par₄ i).2 (hkop i) (hksec i)
          (par₄ j).2 (hkop j) (hksec j)
      · exact fc_transIso2_of_empty (fc_trans_src_eq_empty (inter_eq_empty_incW a hv
          (kChart_source_subset a (fun w => (D w).tor) (par₄ i).1 (par₄ i).2 (hkop i) (hksec i))
          (kChart_source_subset a (fun w => (D w).tor) (par₄ j).1 (par₄ j).2 (hkop j) (hksec j))))
  let G : FillCharts a :=
    { nC := N₁ + (N₂ + (N₃ + N₄))
      fillChart := FCh
      fillLayer := FL
      fill_anywhere := by
        refine fc_addCases4 (motive := fun j => (FL j).okAnywhere) ?_ ?_ ?_ ?_
        · intro i
          simp only [FL, L₁, fcB1, Fin.addCases_left]
          exact pLayer_okAnywhere (par₁ i).1
        · intro i
          simp only [FL, L₂, fcB2, Fin.addCases_left, Fin.addCases_right]
          exact pLayer_okAnywhere (par₂ i).1
        · intro i
          simp only [FL, L₃, fcB3, Fin.addCases_left, Fin.addCases_right]
          exact cLayer_okAnywhere
        · intro i
          simp only [FL, L₄, fcB4, Fin.addCases_left, Fin.addCases_right]
          exact kLayer_okAnywhere (par₄ i).1
      fill_smooth := fun i j => (fc_transIso2_pair (htrans i j)).1
      fill_iso := by
        intro i j y hyi hyj u v
        exact (fc_transIso2_pair (htrans i j)).2 hyi hyj u v
      fill_ok := by
        intro j
        refine fc_addCases4 (motive := fun j => ∀ ⦃x : a.Mhat⦄, x ∈ (FCh j).source →
          (FL j).ok (FCh j x)) ?_ ?_ ?_ ?_ j
        · intro i x hx
          simp only [FCh, FL, A₁, L₁, fcB1, Fin.addCases_left, Fin.addCases_right] at hx ⊢
          have hmap := OpenPartialHomeomorph.map_source (jChart a D (par₁ i).1 (par₁ i).2) hx
          rw [Work.RTOwed.jChart_target] at hmap
          exact pLayer_ok (par₁ i).1 hmap.1.1
        · intro i x hx
          simp only [FCh, FL, A₂, L₂, fcB2, Fin.addCases_left, Fin.addCases_right] at hx ⊢
          have hmap := OpenPartialHomeomorph.map_source (jChart a D (par₂ i).1 (par₂ i).2) hx
          rw [Work.RTOwed.jChart_target] at hmap
          exact pLayer_ok (par₂ i).1 hmap.1.1
        · intro i x hx
          simp only [FCh, FL, A₃, L₃, fcB3, Fin.addCases_left, Fin.addCases_right] at hx ⊢
          have hmap := OpenPartialHomeomorph.map_source
            (cChart a D (par₃ i).1 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i)) hx
          rw [Work.RTOwed.cChart_target'] at hmap
          have h3 : Work.Cusp.s1
              < (cChart a D (par₃ i).1 (par₃ i).2.1 (par₃ i).2.2 (hδ i) (hne i) x) 3 :=
            hmap.1.2.1
          exact cLayer_ok (by simpa only [cδ, Work.Cusp.s1] using h3)
        · intro i x hx
          simp only [FCh, FL, A₄, L₄, fcB4, Fin.addCases_left, Fin.addCases_right] at hx ⊢
          exact kLayer_ok (par₄ i).1 (kChartOf a (fun w => (D w).tor) (par₄ i).1 (par₄ i).2
            (hkop i) (hksec i) x)
      collar_cover := by
        intro v q hq
        by_cases hn : Work.Cusp.nrm (q.1 : Work.Cusp.E2) ≤ 51/100
        · obtain ⟨i, -, hmem⟩ := hcol v q hq hn
          refine ⟨fcB2 N₁ N₂ N₃ N₄ i, ?_⟩
          simpa only [FCh, A₂, fcB2, Fin.addCases_left, Fin.addCases_right] using hmem
        · obtain ⟨i, -, hmem⟩ := hccol v q hq (not_le.mp hn)
          refine ⟨fcB3 N₁ N₂ N₃ N₄ i, ?_⟩
          simpa only [FCh, A₃, fcB3, Fin.addCases_left, Fin.addCases_right] using hmem
      polar_cover := by
        intro v q hq hn
        obtain ⟨i, -, hmem⟩ := hpol v q hq hn
        refine ⟨fcB1 N₁ N₂ N₃ N₄ i, ?_⟩
        simpa only [FCh, A₁, fcB1, Fin.addCases_left, Fin.addCases_right] using hmem
      core_cover := by
        intro v q hq
        obtain ⟨i, -, hmem⟩ := hcore v q hq
        refine ⟨fcB4 N₁ N₂ N₃ N₄ i, ?_⟩
        simpa only [FCh, A₄, fcB4, Fin.addCases_left, Fin.addCases_right] using hmem }
  refine ⟨⟨G, ?_⟩⟩
  refine { cross_smooth_fg := ?_, cross_smooth_gf := ?_, cross_iso_fg := ?_, cross_iso_gf := ?_ }
  · intro i j
    refine fc_addCases4 (motive := fun j => ContDiffOn ℝ ∞
      (((FCh j) : a.Mhat → E4) ∘ ((foldDataOf g).foldM i).symm)
      (((foldDataOf g).foldM i).symm ≫ₕ FCh j).source) ?_ ?_ ?_ ?_ j
    · intro k
      have hd : ((foldDataOf g).foldM i).source ∩ (A₁ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₁ k).1 (par₁ k).2)
      simpa only [FCh, A₁, Fin.addCases_left, Fin.addCases_right] using
        fc_contDiffOn_of_empty (fc_trans_src_eq_empty hd)
    · intro k
      have hd : ((foldDataOf g).foldM i).source ∩ (A₂ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₂ k).1 (par₂ k).2)
      simpa only [FCh, A₂, Fin.addCases_left, Fin.addCases_right] using
        fc_contDiffOn_of_empty (fc_trans_src_eq_empty hd)
    · intro k
      have hconj := foldTransCollIso2_ph g D R i (par₃ k).1 (par₃ k).2.1 (par₃ k).2.2
        (hδ k) (hne k)
      have hcd : ContDiffOn ℝ ∞
          (fun q => cChart (Work.RTInstance.assemblyOf g) D (par₃ k).1 (par₃ k).2.1
            (par₃ k).2.2 (hδ k) (hne k) (((foldDataOf g).foldM i).symm q))
          (foldCTransSrc g D i (par₃ k).1 (par₃ k).2.1 (par₃ k).2.2 (hδ k) (hne k)) :=
        hconj.1.1
      simp only [FCh, A₃, Fin.addCases_left, Fin.addCases_right] at hcd ⊢
      exact hcd
    · intro k
      have hd : ((foldDataOf g).foldM i).source ∩ (A₄ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (kChart_source_subset a (fun w => (D w).tor) (par₄ k).1 (par₄ k).2 (hkop k) (hksec k))
      simpa only [FCh, A₄, Fin.addCases_left, Fin.addCases_right] using
        fc_contDiffOn_of_empty (fc_trans_src_eq_empty hd)
  · intro i j
    refine fc_addCases4 (motive := fun j => ContDiffOn ℝ ∞
      (((foldDataOf g).foldM i : a.Mhat → E4) ∘ (FCh j).symm)
      ((FCh j).symm ≫ₕ (foldDataOf g).foldM i).source) ?_ ?_ ?_ ?_ j
    · intro k
      have hd : (A₁ k).source ∩ ((foldDataOf g).foldM i).source = ∅ := by
        rw [Set.inter_comm]
        exact inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₁ k).1 (par₁ k).2)
      simpa only [FCh, A₁, Fin.addCases_left, Fin.addCases_right] using
        fc_contDiffOn_of_empty (fc_trans_src_eq_empty hd)
    · intro k
      have hd : (A₂ k).source ∩ ((foldDataOf g).foldM i).source = ∅ := by
        rw [Set.inter_comm]
        exact inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₂ k).1 (par₂ k).2)
      simpa only [FCh, A₂, Fin.addCases_left, Fin.addCases_right] using
        fc_contDiffOn_of_empty (fc_trans_src_eq_empty hd)
    · intro k
      have hconj := foldTransCollIso2_ph g D R i (par₃ k).1 (par₃ k).2.1 (par₃ k).2.2
        (hδ k) (hne k)
      have hcd : ContDiffOn ℝ ∞
          (fun q => (foldDataOf g).foldM i
            ((cChart (Work.RTInstance.assemblyOf g) D (par₃ k).1 (par₃ k).2.1 (par₃ k).2.2
              (hδ k) (hne k)).symm q))
          (cFoldTransSrc g D i (par₃ k).1 (par₃ k).2.1 (par₃ k).2.2 (hδ k) (hne k)) :=
        hconj.2.1
      simp only [FCh, A₃, Fin.addCases_left, Fin.addCases_right] at hcd ⊢
      exact hcd
    · intro k
      have hd : (A₄ k).source ∩ ((foldDataOf g).foldM i).source = ∅ := by
        rw [Set.inter_comm]
        exact inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (kChart_source_subset a (fun w => (D w).tor) (par₄ k).1 (par₄ k).2 (hkop k) (hksec k))
      simpa only [FCh, A₄, Fin.addCases_left, Fin.addCases_right] using
        fc_contDiffOn_of_empty (fc_trans_src_eq_empty hd)
  · intro i j
    refine fc_addCases4 (motive := fun j => ∀ ⦃y : a.Mhat⦄,
      y ∈ ((foldDataOf g).foldM i).source → y ∈ (FCh j).source → ∀ u v : E4,
      (FL j).model (FCh j y)
        (fderiv ℝ (((FCh j) : a.Mhat → E4) ∘ ((foldDataOf g).foldM i).symm)
          (((foldDataOf g).foldM i) y) u)
        (fderiv ℝ (((FCh j) : a.Mhat → E4) ∘ ((foldDataOf g).foldM i).symm)
          (((foldDataOf g).foldM i) y) v)
        = Work.RTInstance.uhsModel (foldDataOf g).δ (((foldDataOf g).foldM i) y) u v)
      ?_ ?_ ?_ ?_ j
    · intro k y hyi hyj u v
      have hyj' : y ∈ (A₁ k).source := by
        simpa only [FCh, A₁, Fin.addCases_left, Fin.addCases_right] using hyj
      have hd : ((foldDataOf g).foldM i).source ∩ (A₁ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₁ k).1 (par₁ k).2)
      exact (fc_notMem_of_empty hd hyi hyj').elim
    · intro k y hyi hyj u v
      have hyj' : y ∈ (A₂ k).source := by
        simpa only [FCh, A₂, Fin.addCases_left, Fin.addCases_right] using hyj
      have hd : ((foldDataOf g).foldM i).source ∩ (A₂ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₂ k).1 (par₂ k).2)
      exact (fc_notMem_of_empty hd hyi hyj').elim
    · intro k y hyi hyj u v
      have hyj' : y ∈ (cChart a D (par₃ k).1 (par₃ k).2.1 (par₃ k).2.2 (hδ k) (hne k)).source := by
        simpa only [FCh, A₃, Fin.addCases_left, Fin.addCases_right] using hyj
      have hconj := (fc_transIso2_pair (foldTransCollIso2_ph g D R i (par₃ k).1 (par₃ k).2.1
        (par₃ k).2.2 (hδ k) (hne k)).1).2 hyi hyj' u v
      simpa only [FCh, FL, A₃, L₃, Fin.addCases_left, Fin.addCases_right, foldCTransMap,
        a, Function.comp_apply] using hconj
    · intro k y hyi hyj u v
      have hyj' : y ∈ (A₄ k).source := by
        simpa only [FCh, A₄, Fin.addCases_left, Fin.addCases_right] using hyj
      have hd : ((foldDataOf g).foldM i).source ∩ (A₄ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (kChart_source_subset a (fun w => (D w).tor) (par₄ k).1 (par₄ k).2
            (hkop k) (hksec k))
      exact (fc_notMem_of_empty hd hyi hyj').elim
  · intro i j
    refine fc_addCases4 (motive := fun j => ∀ ⦃y : a.Mhat⦄,
      y ∈ (FCh j).source → y ∈ ((foldDataOf g).foldM i).source → ∀ u v : E4,
      Work.RTInstance.uhsModel (foldDataOf g).δ (((foldDataOf g).foldM i) y)
        (fderiv ℝ (((foldDataOf g).foldM i : a.Mhat → E4) ∘ (FCh j).symm) ((FCh j) y) u)
        (fderiv ℝ (((foldDataOf g).foldM i : a.Mhat → E4) ∘ (FCh j).symm) ((FCh j) y) v)
        = (FL j).model (FCh j y) u v)
      ?_ ?_ ?_ ?_ j
    · intro k y hyj hyi u v
      have hyj' : y ∈ (A₁ k).source := by
        simpa only [FCh, A₁, Fin.addCases_left, Fin.addCases_right] using hyj
      have hd : ((foldDataOf g).foldM i).source ∩ (A₁ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₁ k).1 (par₁ k).2)
      exact (fc_notMem_of_empty hd hyi hyj').elim
    · intro k y hyj hyi u v
      have hyj' : y ∈ (A₂ k).source := by
        simpa only [FCh, A₂, Fin.addCases_left, Fin.addCases_right] using hyj
      have hd : ((foldDataOf g).foldM i).source ∩ (A₂ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (jChart_source_subset a D (par₂ k).1 (par₂ k).2)
      exact (fc_notMem_of_empty hd hyi hyj').elim
    · intro k y hyj hyi u v
      have hyj' : y ∈ (cChart a D (par₃ k).1 (par₃ k).2.1 (par₃ k).2.2 (hδ k) (hne k)).source := by
        simpa only [FCh, A₃, Fin.addCases_left, Fin.addCases_right] using hyj
      have hconj := (fc_transIso2_pair (foldTransCollIso2_ph g D R i (par₃ k).1 (par₃ k).2.1
        (par₃ k).2.2 (hδ k) (hne k)).2).2 hyj' hyi u v
      simpa only [FCh, FL, A₃, L₃, Fin.addCases_left, Fin.addCases_right, cFoldTransMap,
        Function.comp_apply] using hconj
    · intro k y hyj hyi u v
      have hyj' : y ∈ (A₄ k).source := by
        simpa only [FCh, A₄, Fin.addCases_left, Fin.addCases_right] using hyj
      have hd : ((foldDataOf g).foldM i).source ∩ (A₄ k).source = ∅ :=
        inter_eq_empty_incMbar a (foldM_source_subset a (foldDataOf g) i)
          (kChart_source_subset a (fun w => (D w).tor) (par₄ k).1 (par₄ k).2
            (hkop k) (hksec k))
      exact (fc_notMem_of_empty hd hyi hyj').elim
end Work.RTOwed
