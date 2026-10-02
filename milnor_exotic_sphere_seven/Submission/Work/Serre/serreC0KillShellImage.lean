import Mathlib
import Submission.Work.Serre.serreC0KillHomologySets
import Submission.Work.Serre.serreC0SigmaHomology
import Submission.Work.Serre.Wedge.shellHomotopyEquiv
import Submission.Work.Serre.AttachCompress.Partition
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.Cohomology.localCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

/-! ## Auxiliary: the range of a `Sigma.desc` -/

theorem range_Sigma_desc {ι : Type} {M : ι → ModuleCat ℤ} {N : ModuleCat ℤ}
    (f : ∀ i, M i ⟶ N) :
    LinearMap.range (ModuleCat.Hom.hom (Limits.Sigma.desc f))
      = Submodule.span ℤ (⋃ i, LinearMap.range (ModuleCat.Hom.hom (f i))) := by
  classical
  haveI : DecidableEq ι := Classical.decEq ι
  set P : Submodule ℤ ↑(∐ M) :=
    ⨆ i, LinearMap.range (ModuleCat.Hom.hom (Limits.Sigma.ι M i)) with hP
  have htopP : P = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    have hgen : ∀ y : DirectSum ι (fun i => ↑(M i)),
        ModuleCat.Hom.hom (ModuleCat.coprodIsoDirectSum M).inv y ∈ P := by
      intro y
      induction y using DFinsupp.induction with
      | h0 => simp
      | ha i b g hgi hb ih =>
        rw [map_add, DirectSum.single_eq_lof (R := ℤ) (M := fun j => ↑(M j)) i b]
        refine P.add_mem ?_ ih
        have hE : (ModuleCat.coprodIsoDirectSum M).hom ((Limits.Sigma.ι M i) b)
            = (DirectSum.lof ℤ ι (fun i => ↑(M i)) i) b := by
          have hc := congrArg (fun φ => ModuleCat.Hom.hom φ b)
            (ModuleCat.ι_coprodIsoDirectSum_hom M i)
          exact hc
        have h1 : (ModuleCat.coprodIsoDirectSum M).inv
            ((DirectSum.lof ℤ ι (fun i => ↑(M i)) i) b) = (Limits.Sigma.ι M i) b := by
          have h2 : (ModuleCat.coprodIsoDirectSum M).inv
              ((ModuleCat.coprodIsoDirectSum M).hom ((Limits.Sigma.ι M i) b))
              = (Limits.Sigma.ι M i) b := by
            have h := ModuleCat.comp_apply (ModuleCat.coprodIsoDirectSum M).hom
              (ModuleCat.coprodIsoDirectSum M).inv ((Limits.Sigma.ι M i) b)
            rw [Iso.hom_inv_id] at h
            simpa [ModuleCat.id_apply] using h.symm
          rw [← h2, hE]
        rw [h1]
        exact Submodule.mem_iSup_of_mem i ⟨b, rfl⟩
    have hx : x = ModuleCat.Hom.hom (ModuleCat.coprodIsoDirectSum M).inv
        (ModuleCat.Hom.hom (ModuleCat.coprodIsoDirectSum M).hom x) := by
      have h := congrArg (fun φ => ModuleCat.Hom.hom φ x)
        (Iso.hom_inv_id (ModuleCat.coprodIsoDirectSum M))
      simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply] using h.symm
    rw [hx]
    exact hgen _
  set S : Submodule ℤ ↑N :=
    Submodule.span ℤ (⋃ i, LinearMap.range (ModuleCat.Hom.hom (f i))) with hS
  have hle : P ≤ Submodule.comap (ModuleCat.Hom.hom (Limits.Sigma.desc f)) S := by
    refine iSup_le fun i => ?_
    rintro z ⟨b, rfl⟩
    show ModuleCat.Hom.hom (Limits.Sigma.desc f)
      (ModuleCat.Hom.hom (Limits.Sigma.ι M i) b) ∈ S
    rw [← ModuleCat.comp_apply, Limits.Sigma.ι_desc]
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨b, rfl⟩⟩)
  have htop : Submodule.comap (ModuleCat.Hom.hom (Limits.Sigma.desc f)) S = ⊤ := by
    rw [htopP] at hle
    rw [top_le_iff] at hle
    exact hle
  refine le_antisymm ?_ ?_
  · rw [hS]
    rw [show LinearMap.range (ModuleCat.Hom.hom (Limits.Sigma.desc f))
        = Submodule.map (ModuleCat.Hom.hom (Limits.Sigma.desc f)) ⊤ from
      LinearMap.range_eq_map _]
    rw [show (⊤ : Submodule ℤ ↑(∐ M))
        = Submodule.comap (ModuleCat.Hom.hom (Limits.Sigma.desc f)) S from htop.symm]
    exact Submodule.map_comap_le _ _
  · rw [hS]
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hzi
    refine LinearMap.mem_range.mpr ⟨ModuleCat.Hom.hom (Limits.Sigma.ι M i) b, ?_⟩
    rw [← ModuleCat.comp_apply, Limits.Sigma.ι_desc]

/-! ## The range of the map induced by a single sphere -/

theorem serreRangeHurewiczClass {n : ℕ} (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (g : C(Work.Stems.sphere n, X)) :
    LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere n)) (TopCat.of X)
          (TopCat.ofHom g)) n))
      = Submodule.span ℤ {Work.Stems.hurewiczClass n hn g} := by
  classical
  let e := Classical.choice (Work.Cohomology.sphereHomologyTop n hn)
  have he1 : ModuleCat.Hom.hom e.inv (1 : ℤ) = Work.Stems.sphereGenerator n hn := rfl
  have hone : Submodule.span ℤ ({(1 : ℤ)} : Set ℤ) = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    have h : x • (1 : ℤ) ∈ Submodule.span ℤ ({(1 : ℤ)} : Set ℤ) :=
      Submodule.smul_mem _ x (Submodule.subset_span (Set.mem_singleton 1))
    simpa using h
  have hsurj : Function.Surjective (ModuleCat.Hom.hom e.inv) :=
    (Work.Cohomology.moduleIsoToLinearEquiv' e.symm).surjective
  have hmap : Submodule.span ℤ ({ModuleCat.Hom.hom e.inv (1 : ℤ)} : Set _)
      = Submodule.map (ModuleCat.Hom.hom e.inv)
          (Submodule.span ℤ ({(1 : ℤ)} : Set ℤ)) := by
    rw [Submodule.map_span, Set.image_singleton]
  have hgen : Submodule.span ℤ ({Work.Stems.sphereGenerator n hn} : Set _) = ⊤ := by
    rw [← he1, hmap, hone, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  set L := ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere n)) (TopCat.of X)
        (TopCat.ofHom g)) n) with hL
  have hLu : L (Work.Stems.sphereGenerator n hn) = Work.Stems.hurewiczClass n hn g := rfl
  show LinearMap.range L = Submodule.span ℤ {Work.Stems.hurewiczClass n hn g}
  rw [LinearMap.range_eq_map, ← hgen, Submodule.map_span, Set.image_singleton, hLu]

/-! ## The range of the map induced by a disjoint union -/

theorem serreRangeSigmaDesc {ι : Type} (T : ι → Type) [∀ i, TopologicalSpace (T i)]
    {Z : Type} [TopologicalSpace Z] (n : ℕ) (g : C(Σ i, T i, Z)) :
    LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, T i)) (TopCat.of Z)
          (TopCat.ofHom g)) n))
      = Submodule.span ℤ (⋃ i, LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (T i)) (TopCat.of Z)
            (TopCat.ofHom (g.comp ⟨Sigma.mk i, continuous_sigmaMk⟩))) n))) := by
  classical
  let Φ : ∀ i, (Work.Cohomology.singularChains ℤ (TopCat.of (T i))).homology n ⟶
      (Work.Cohomology.singularChains ℤ (TopCat.of (Σ j, T j))).homology n :=
    fun i => HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (T i))
      (TopCat.of (Σ j, T j)) (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) n
  let Λ : ∀ i, (Work.Cohomology.singularChains ℤ (TopCat.of (T i))).homology n ⟶
      (Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology n :=
    fun i => HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (T i))
      (TopCat.of Z) (TopCat.ofHom (g.comp ⟨Sigma.mk i, continuous_sigmaMk⟩))) n
  haveI hIso : IsIso (Limits.Sigma.desc Φ) := serreC0SigmaHomology T n
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (Limits.Sigma.desc Φ)) :=
    (ConcreteCategory.bijective_of_isIso (Limits.Sigma.desc Φ)).2
  have hkey : (Limits.Sigma.desc Φ) ≫ (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Σ j, T j)) (TopCat.of Z)
          (TopCat.ofHom g)) n) = Limits.Sigma.desc Λ := by
    rw [sigma_desc_comp]
    congr 1
    funext i
    rw [← HomologicalComplex.homologyMap_comp, ← Work.Cohomology.chainMap_comp',
      ← TopCat.ofHom_comp]
  have hrange : LinearMap.range (ModuleCat.Hom.hom ((Limits.Sigma.desc Φ) ≫
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (Σ j, T j))
          (TopCat.of Z) (TopCat.ofHom g)) n)))
      = LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Σ j, T j)) (TopCat.of Z)
          (TopCat.ofHom g)) n)) := by
    rw [ModuleCat.hom_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj,
      Submodule.map_top]
  rw [← hrange, hkey]
  exact range_Sigma_desc Λ

/-! ## The homeomorphism between the shell cover and the disjoint union of model shells -/

theorem serreC0KillZShellHomeo {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Nonempty (↥(Work.Serre.KillZ f) ≃ₜ
      (Σ i : ι, ↥(Work.Serre.cellShellSet n (1 / 4) (1 / 2)))) := by
  classical
  let sh : Set (Work.RatHurewicz.cellDisk n) := Work.Serre.cellShellSet n (1 / 4) (1 / 2)
  have hshopen : IsOpen sh := Work.Serre.isOpen_cellShellSet n _ _
  have hshinner : sh ⊆ Work.RatHurewicz.cellInner n :=
    Work.Serre.cellShellSet_subset_cellInner (by norm_num)
  let Φ₀ : (Σ i : ι, ↥sh) → Work.Serre.KillX f :=
    fun p => Work.RatHurewicz.cellMap n Y ι f p.1 (p.2 : Work.RatHurewicz.cellDisk n)
  have hΦ₀c : Continuous Φ₀ := by
    refine continuous_sigma ?_
    intro i
    exact (Work.RatHurewicz.cellMap n Y ι f i).continuous.comp continuous_subtype_val
  have hmem : ∀ p : Σ i : ι, ↥sh, Φ₀ p ∈ Work.Serre.KillZ f := by
    intro p
    rw [Work.Serre.KillZ_eq_iUnion_KillQ]
    exact Set.mem_iUnion.mpr ⟨p.1, (Work.Serre.mem_KillQ f p.1 (Φ₀ p)).mpr
      ⟨p.2.1, (Work.Serre.mem_cellShellSet.mp p.2.2).1,
        (Work.Serre.mem_cellShellSet.mp p.2.2).2, rfl⟩⟩
  let Φ : (Σ i : ι, ↥sh) → ↥(Work.Serre.KillZ f) := fun p => ⟨Φ₀ p, hmem p⟩
  have hΦc : Continuous Φ := Continuous.subtype_mk hΦ₀c hmem
  have hinj : Function.Injective Φ := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hval : (Work.RatHurewicz.cellMap n Y ι f i) (x : Work.RatHurewicz.cellDisk n)
        = (Work.RatHurewicz.cellMap n Y ι f j) (y : Work.RatHurewicz.cellDisk n) :=
      congrArg Subtype.val h
    have hrel : Relation.EqvGen (Work.RatHurewicz.attachRel n Y ι f)
        (Sum.inr (⟨i, (x : Work.RatHurewicz.cellDisk n)⟩ :
          Σ _ : ι, Work.RatHurewicz.cellDisk n))
        (Sum.inr (⟨j, (y : Work.RatHurewicz.cellDisk n)⟩ :
          Σ _ : ι, Work.RatHurewicz.cellDisk n)) := Quotient.exact hval
    obtain ⟨hij, hxy⟩ := Work.Serre.AttachCompress.cls_inner_inj f (hshinner x.2) (hshinner y.2)
      (Work.RatHurewicz.AttachRange.eqvGen_le_cls n Y ι f hrel)
    subst hij
    exact congrArg (fun t => (⟨i, t⟩ : Σ k, ↥sh)) (Subtype.ext hxy)
  have hsurj : Function.Surjective Φ := by
    intro z
    have hz : (z : Work.Serre.KillX f) ∈ ⋃ i, Work.Serre.KillQ f i := by
      rw [← Work.Serre.KillZ_eq_iUnion_KillQ]; exact z.2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, hx1, hx2, hxz⟩ := (Work.Serre.mem_KillQ f i (z : Work.Serre.KillX f)).mp hi
    exact ⟨⟨i, ⟨x, ⟨hx1, hx2⟩⟩⟩, Subtype.ext hxz⟩
  have hopen : IsOpenMap Φ := by
    intro U hU
    have hUi : ∀ i, IsOpen ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ⁻¹' U) :=
      fun i => isOpen_sigma_iff.mp hU i
    choose W hWopen hWeq using fun i => isOpen_induced_iff.mp (hUi i)
    have hopen_i : ∀ i, IsOpen {z : Work.Serre.KillX f | ∃ x ∈ W i ∩ sh,
        Work.RatHurewicz.cellMap n Y ι f i x = z} := fun i =>
      Work.RatHurewicz.isOpen_cellMap_image ((hWopen i).inter hshopen)
        (Set.inter_subset_right.trans hshinner)
    have himg : ∀ i, Φ₀ '' ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ''
          ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ⁻¹' U))
        = {z : Work.Serre.KillX f | ∃ x ∈ W i ∩ sh,
            Work.RatHurewicz.cellMap n Y ι f i x = z} := by
      intro i
      ext z
      constructor
      · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
        exact ⟨(q : Work.RatHurewicz.cellDisk n),
          ⟨(Set.ext_iff.mp (hWeq i) q).mpr hq, q.2⟩, rfl⟩
      · rintro ⟨x, ⟨hxW, hxsh⟩, rfl⟩
        exact ⟨⟨i, ⟨x, hxsh⟩⟩,
          ⟨⟨x, hxsh⟩, (Set.ext_iff.mp (hWeq i) ⟨x, hxsh⟩).mp hxW, rfl⟩, rfl⟩
    have hUeq : U = ⋃ i, (fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ''
        ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ⁻¹' U) := by
      ext p
      constructor
      · intro hp
        exact Set.mem_iUnion.mpr ⟨p.1, ⟨p.2, hp, rfl⟩⟩
      · intro hp
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
        obtain ⟨q, hq, hqp⟩ := hi
        rw [← hqp]
        exact hq
    have hΦ₀img : Φ₀ '' U = ⋃ i, Φ₀ '' ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ''
        ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ⁻¹' U)) := by
      conv_lhs => rw [hUeq]
      rw [Set.image_iUnion]
    have hKillZ : (Subtype.val : ↥(Work.Serre.KillZ f) → Work.Serre.KillX f) ⁻¹'
        (Φ₀ '' U) = Φ '' U := by
      ext z
      constructor
      · rintro ⟨p, hp, hpz⟩
        exact ⟨p, hp, Subtype.ext hpz⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, rfl⟩
    rw [show Φ '' U = (Subtype.val : ↥(Work.Serre.KillZ f) → Work.Serre.KillX f) ⁻¹'
        (⋃ i, Φ₀ '' ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ''
          ((fun x : ↥sh => (⟨i, x⟩ : Σ k : ι, ↥sh)) ⁻¹' U))) from by
      rw [← hKillZ, hΦ₀img]]
    rw [Set.preimage_iUnion]
    apply isOpen_iUnion
    intro i
    rw [himg i]
    exact (hopen_i i).preimage continuous_subtype_val
  exact ⟨((Equiv.ofBijective Φ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hΦc hopen).symm⟩

/-! ## Assembly -/

theorem span_iUnion_span_singleton {ι : Type} {M : Type} [AddCommGroup M] [Module ℤ M]
    (a : ι → M) :
    Submodule.span ℤ (⋃ i, Submodule.span ℤ ({a i} : Set M))
      = Submodule.span ℤ (Set.range a) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have h2 : ({a i} : Set M) ⊆ Set.range a := Set.singleton_subset_iff.mpr ⟨i, rfl⟩
    exact Submodule.span_mono h2 hi
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    have h1 : a i ∈ (⋃ j, Submodule.span ℤ ({a j} : Set M)) :=
      Set.mem_iUnion.mpr ⟨i, by
        show a i ∈ Submodule.span ℤ ({a i} : Set M)
        exact Submodule.subset_span (Set.mem_singleton (a i))⟩
    exact Submodule.subset_span h1

theorem serreC0KillShellImage {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    ∃ e : ↥(Work.Serre.KillZ f) ≃ₜ (Σ i : ι, ↥(Work.Serre.cellShellSet n (1 / 4) (1 / 2))),
      LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of ↥(Work.Serre.KillZ f))
            (TopCat.of ↥(Work.Serre.KillA f))
            (TopCat.ofHom ((Work.Serre.KillShellToA f).comp
              ⟨e, e.continuous_toFun⟩))) (n + 1)))
        = Submodule.span ℤ (Set.range (fun i : ι =>
            Work.Stems.hurewiczClass (n + 1) (by omega)
              ⟨fun z => ⟨Work.RatHurewicz.attachIncl n Y ι f (f i z), ⟨f i z, rfl⟩⟩, by fun_prop⟩)) := by
  classical
  obtain ⟨e⟩ := serreC0KillZShellHomeo (f := f)
  refine ⟨e, ?_⟩
  let sh : Set (Work.RatHurewicz.cellDisk n) := Work.Serre.cellShellSet n (1 / 4) (1 / 2)
  let X : TopCat := TopCat.of ↥(Work.Serre.KillZ f)
  let S : TopCat := TopCat.of (Σ i : ι, ↥sh)
  let A : TopCat := TopCat.of ↥(Work.Serre.KillA f)
  let E : X ≅ S := TopCat.isoOfHomeo e
  let hr : (0 : ℝ) < 1 / 4 := by norm_num
  let hrr : (1 : ℝ) / 4 < 1 / 2 := by norm_num
  let hR1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  let AI : ι → C(Work.RatHurewicz.cellSphere n, ↥(Work.Serre.KillA f)) :=
    fun i => ⟨fun z => ⟨Work.RatHurewicz.attachIncl n Y ι f (f i z), ⟨f i z, rfl⟩⟩,
      Continuous.subtype_mk
        ((Work.RatHurewicz.attachIncl n Y ι f).continuous.comp (f i).continuous)
        (fun z => ⟨f i z, rfl⟩)⟩
  let sg : ι → C(↥sh, (Σ k : ι, ↥sh)) := fun i =>
    ⟨fun x => (⟨i, x⟩ : Σ k : ι, ↥sh), continuous_sigmaMk (σ := fun _ : ι => ↥sh) (i := i)⟩
  let RM : C(↥sh, Work.RatHurewicz.cellSphere n) :=
    Work.Serre.Wedge.shellRadialMap n (1 / 4) (1 / 2) hr
  let IC : C(Work.RatHurewicz.cellSphere n, ↥sh) :=
    Work.Serre.Wedge.shellIncl n (1 / 4) (1 / 2) hr hrr hR1
  have hEhom : E.hom = TopCat.ofHom ⟨e, e.continuous_toFun⟩ := by
    rw [TopCat.isoOfHomeo_hom]
  have hcomp : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X A
        (TopCat.ofHom ((Work.Serre.KillShellToA f).comp ⟨e, e.continuous_toFun⟩))) (n + 1)
      = HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X S E.hom) (n + 1)
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ S A
            (TopCat.ofHom (Work.Serre.KillShellToA f))) (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← Work.Cohomology.chainMap_comp',
      TopCat.ofHom_comp, ← hEhom]
  haveI hIso' : IsIso (Work.Cohomology.chainMap ℤ X S E.hom) := by
    rw [Work.Cohomology.chainMap]
    exact Functor.map_isIso _ _
  haveI hIso : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X S E.hom)
      (n + 1)) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso
      (asIso (Work.Cohomology.chainMap ℤ X S E.hom)) (n + 1))
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ X S E.hom) (n + 1))) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have hrange : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ X A
          (TopCat.ofHom ((Work.Serre.KillShellToA f).comp ⟨e, e.continuous_toFun⟩))) (n + 1)))
      = LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ S A (TopCat.ofHom (Work.Serre.KillShellToA f))) (n + 1))) := by
    rw [hcomp, ModuleCat.hom_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hdir : ∀ x : ↥sh, Work.Serre.shellDir x = RM x := by
    intro x
    refine Subtype.ext ?_
    rfl
  have hgi : ∀ i, (Work.Serre.KillShellToA f).comp (sg i) = (AI i).comp RM := by
    intro i
    refine ContinuousMap.ext fun x => Subtype.ext ?_
    show Work.RatHurewicz.attachIncl n Y ι f (f i (Work.Serre.shellDir x))
      = Work.RatHurewicz.attachIncl n Y ι f (f i (RM x))
    rw [hdir x]
  have hcomp2 : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (Work.RatHurewicz.cellSphere n)) (TopCat.of ↥sh)
        (TopCat.ofHom IC)) (n + 1)
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of ↥sh)
        (TopCat.of (Work.RatHurewicz.cellSphere n)) (TopCat.ofHom RM)) (n + 1)
      = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← Work.Cohomology.chainMap_comp',
      ← TopCat.ofHom_comp,
      show (RM.comp IC : C(Work.RatHurewicz.cellSphere n, Work.RatHurewicz.cellSphere n))
        = ContinuousMap.id (Work.RatHurewicz.cellSphere n) from
        Work.Serre.Wedge.shellRadialMap_comp_shellIncl n (1 / 4) (1 / 2) hr hrr hR1,
      show TopCat.ofHom (ContinuousMap.id (Work.RatHurewicz.cellSphere n))
        = 𝟙 (TopCat.of (Work.RatHurewicz.cellSphere n)) from rfl,
      Work.Cohomology.chainMap_id', HomologicalComplex.homologyMap_id]
  have hsurjR : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥sh) (TopCat.of (Work.RatHurewicz.cellSphere n))
        (TopCat.ofHom RM)) (n + 1))) := by
    intro y
    refine ⟨ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (Work.RatHurewicz.cellSphere n)) (TopCat.of ↥sh) (TopCat.ofHom IC)) (n + 1)) y, ?_⟩
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ y) hcomp2
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply] using h
  have hper : ∀ i, LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥sh) (TopCat.of ↥(Work.Serre.KillA f))
        (TopCat.ofHom ((Work.Serre.KillShellToA f).comp (sg i))))
        (n + 1)))
      = Submodule.span ℤ {Work.Stems.hurewiczClass (n + 1) (by omega) (AI i)} := by
    intro i
    rw [hgi i, TopCat.ofHom_comp,
      Work.Cohomology.chainMap_comp' (X := TopCat.of ↥sh)
        (Y := TopCat.of (Work.RatHurewicz.cellSphere n))
        (Z := TopCat.of ↥(Work.Serre.KillA f)) (TopCat.ofHom RM) (TopCat.ofHom (AI i)),
      HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurjR, Submodule.map_top]
    exact serreRangeHurewiczClass (n := n + 1) (by omega) (AI i)
  rw [hrange, serreRangeSigmaDesc (fun _ : ι => ↥sh) (n + 1) (Work.Serre.KillShellToA f)]
  show Submodule.span ℤ (⋃ i, LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of ↥sh) (TopCat.of ↥(Work.Serre.KillA f))
          (TopCat.ofHom ((Work.Serre.KillShellToA f).comp (sg i)))) (n + 1))))
      = Submodule.span ℤ (Set.range (fun i : ι =>
          Work.Stems.hurewiczClass (n + 1) (by omega) (AI i)))
  simp only [hper]
  rw [span_iUnion_span_singleton]

end

end Work.Serre
