import Mathlib
import Submission.Work.Serre.serreC0KillHomologySets
import Submission.Work.Serre.serreC0KillRhoDefs

/-!
# `serreC0KillRho`: the retraction of `KillU` onto `KillA` and the shell parametrisation

`Work.Serre.KillU f = cellU f (1/4)` is the complement of the images of the closed model balls of
radius `1/4`; it contains the old part `KillA f = range (attachIncl n Y ι f)` and the shell region
`KillZ f`.  The radial push of every punctured cell onto its boundary sphere retracts `KillU f`
onto `KillA f` (`killUPushFun f`), and on a shell point `cellMap i x` it is the attaching map
`attachIncl (f i (x/‖x‖))` (`killUPushFun_shell`).  The shell region is parametrised by the disjoint
union of the model shells via `killZShellMap f`, `(i,x) ↦ cellMap i x`, which is a homeomorphism
(`killZShellMap_bijective`, `killZShellMap_isOpenMap`).  Assembling these gives
`Work.Serre.serreC0KillRho`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-! ### The radial push of a shell point -/

/-- At time `1` the radial push of a shell point is the projection onto the boundary sphere. -/
theorem cellPush_one_eq (x : ↥(cellShellSet n (1 / 4) (1 / 2)))
    (hx : ((x : cellDisk n) : CellVec n) ≠ 0) :
    cellPush n (⟨(x : cellDisk n), hx⟩, 1) = cellSphereToDisk n (shellDir x) := by
  apply Subtype.ext
  show cellPushVec n (1 : I) ((x : cellDisk n) : CellVec n) = shellDirVec x
  rw [cellPushVec, shellDirVec]
  have h1 : ((1 : I) : ℝ) = 1 := rfl
  simp [h1]

/-! ### The shell parametrisation is a bijection -/

theorem killZShellMap_injective (f : ι → C(cellSphere n, Y)) :
    Function.Injective (killZShellMap f) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have h' : cellMap n Y ι f i (x : cellDisk n) = cellMap n Y ι f j (y : cellDisk n) := by
    have := congrArg (fun w : ↥(KillZ f) => (w : KillX f)) h
    simpa only [killZShellMap_apply] using this
  have hgen' : Relation.EqvGen (attachRel n Y ι f) (Sum.inr ⟨j, (y : cellDisk n)⟩)
      (Sum.inr ⟨i, (x : cellDisk n)⟩) := Quotient.exact h'.symm
  have h2 := eq_of_eqvGen_inr_cellInner (f := f) (i := i) (x := (x : cellDisk n))
    (lt_trans x.2.2 (by norm_num)) hgen'
  have h2' : (⟨j, (y : cellDisk n)⟩ : Σ _ : ι, cellDisk n) = ⟨i, (x : cellDisk n)⟩ :=
    Sum.inr.inj h2
  have hij : j = i := congrArg (fun p : Σ _ : ι, cellDisk n => p.1) h2'
  have hxy : (y : cellDisk n) = (x : cellDisk n) :=
    congrArg (fun p : Σ _ : ι, cellDisk n => p.2) h2'
  exact Sigma.ext hij.symm (heq_of_eq (Subtype.ext hxy.symm))

theorem killZShellMap_surjective (f : ι → C(cellSphere n, Y)) :
    Function.Surjective (killZShellMap f) := by
  rintro ⟨z, hzKillZ⟩
  have hz : z ∈ ⋃ i, KillQ f i := by
    rw [← KillZ_eq_iUnion_KillQ]
    exact hzKillZ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨x, hx1, hx2, hxeq⟩ := (mem_KillQ f i z).mp hi
  refine ⟨⟨i, ⟨x, hx1, hx2⟩⟩, ?_⟩
  apply Subtype.ext
  simpa only [killZShellMap_apply] using hxeq

theorem killZShellMap_bijective (f : ι → C(cellSphere n, Y)) :
    Function.Bijective (killZShellMap f) :=
  ⟨killZShellMap_injective f, killZShellMap_surjective f⟩

/-! ### The shell parametrisation is an open map -/

/-- The image under `cellMap i` of the points of `U` in the shell is `KillQ f i` intersected with
the image of `U`. -/
theorem cellMap_image_cellShellSet (f : ι → C(cellSphere n, Y)) (i : ι) {U : Set (cellDisk n)}
    (hU : U ⊆ cellInner n) :
    (cellMap n Y ι f i) '' (U ∩ cellShellSet n (1 / 4) (1 / 2))
      = KillQ f i ∩ (cellMap n Y ι f i) '' U := by
  ext z
  constructor
  · rintro ⟨x, ⟨hxU, hx1, hx2⟩, rfl⟩
    exact ⟨(mem_KillQ f i _).mpr ⟨x, hx1, hx2, rfl⟩, ⟨x, hxU, rfl⟩⟩
  · rintro ⟨hQ, ⟨x, hxU, rfl⟩⟩
    obtain ⟨x', hx'1, hx'2, hx'eq⟩ := (mem_KillQ f i _).mp hQ
    have hx'in : x' ∈ cellInner n := lt_trans hx'2 (by norm_num)
    have h' : (⟨x, hU hxU⟩ : ↥(cellInner n)) = ⟨x', hx'in⟩ :=
      cellMap_injective_cellInner (f := f) i (by
        change cellMap n Y ι f i x = cellMap n Y ι f i x'
        rw [← hx'eq])
    have hxx' : x = x' := congrArg Subtype.val h'
    exact ⟨x, ⟨hxU, by rw [hxx']; exact hx'1, by rw [hxx']; exact hx'2⟩, rfl⟩

/-- The image of the `i`-th piece of the shell parametrisation. -/
theorem killZShellMap_image_piece (f : ι → C(cellSphere n, Y)) (i : ι)
    (S : Set ↥(cellShellSet n (1 / 4) (1 / 2))) :
    killZShellMap f '' ((fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
        (⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) '' S)
      = (fun z : ↥(KillZ f) => (z : KillX f)) ⁻¹'
          ((cellMap n Y ι f i) '' ((fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
            (x : cellDisk n)) '' S)) := by
  ext z
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, hz⟩
    refine ⟨(x : cellDisk n), ⟨x, hx, rfl⟩, ?_⟩
    rw [← hz]
    exact (killZShellMap_apply f ⟨i, x⟩).symm
  · rintro ⟨x, hx, hxz⟩
    obtain ⟨x', hx'S, hx'eq⟩ := hx
    refine ⟨⟨i, x'⟩, ⟨x', hx'S, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [← hx'eq] at hxz
    exact hxz

theorem killZShellMap_isOpenMap (f : ι → C(cellSphere n, Y)) :
    IsOpenMap (killZShellMap f) := by
  intro W hW
  have hdecomp : W = ⋃ i, (fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
        (⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) ''
        ((fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
          (⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) ⁻¹' W) := by
    ext p
    constructor
    · intro hp
      exact Set.mem_iUnion.mpr ⟨p.1, p.2, hp, rfl⟩
    · intro hp
      obtain ⟨i, q, hq, hqp⟩ := Set.mem_iUnion.mp hp
      rw [← hqp]
      exact hq
  have hWi : ∀ i, IsOpen ((fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
      (⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) ⁻¹' W) :=
    fun i => isOpen_sigma_iff.mp hW i
  choose U hUopen hUeq using fun i => isOpen_induced_iff.mp (hWi i)
  have hxU : ∀ (i : ι) (x : ↥(cellShellSet n (1 / 4) (1 / 2))),
      ((x : cellDisk n) ∈ U i) ↔
        ((⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2))) ∈ W) := by
    intro i x
    have h := congrArg (fun s : Set ↥(cellShellSet n (1 / 4) (1 / 2)) => x ∈ s) (hUeq i)
    simpa only [Set.mem_preimage] using (iff_of_eq h)
  rw [hdecomp, Set.image_iUnion]
  refine isOpen_iUnion fun i => ?_
  have hSval : (fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) => (x : cellDisk n)) ''
      ((fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
        (⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) ⁻¹' W)
      = U i ∩ cellShellSet n (1 / 4) (1 / 2) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hxU i x).mpr hx, x.2⟩
    · rintro ⟨hyU, hyS⟩
      exact ⟨⟨y, hyS⟩, (hxU i ⟨y, hyS⟩).mp hyU, rfl⟩
  have hUsh : U i ∩ cellShellSet n (1 / 4) (1 / 2)
      = (U i ∩ cellInner n) ∩ cellShellSet n (1 / 4) (1 / 2) := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, lt_trans h2.2 (by norm_num)⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
  have hpiece : killZShellMap f '' ((fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
        (⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) ''
        ((fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
          (⟨i, x⟩ : Σ k : ι, ↥(cellShellSet n (1 / 4) (1 / 2)))) ⁻¹' W))
      = (fun z : ↥(KillZ f) => (z : KillX f)) ⁻¹'
          (KillQ f i ∩ (cellMap n Y ι f i) '' (U i ∩ cellInner n)) := by
    rw [killZShellMap_image_piece]
    congr 1
    rw [hSval, hUsh, cellMap_image_cellShellSet f i Set.inter_subset_right]
  rw [hpiece]
  exact ((isOpen_KillQ f i).inter
    (isOpen_cellMap_image ((hUopen i).inter (isOpen_cellInner n)) Set.inter_subset_right)).preimage
      continuous_subtype_val

/-! ### The properties of the retraction -/

theorem killUPushFun_fix (f : ι → C(cellSphere n, Y)) (a : ↥(KillA f))
    (h : (a : KillX f) ∈ KillU f) :
    killUPushFun f ⟨(a : KillX f), h⟩ = a := by
  apply Subtype.ext
  change pushGarbage n Y ι f
      ((Classical.choose (killUQuot_surjective f ⟨(a : KillX f), h⟩) : ↥(KillUpre f)) :
        Y ⊕ (Σ _ : ι, cellDisk n)) 1 = (a : KillX f)
  have hspec := Classical.choose_spec (killUQuot_surjective f ⟨(a : KillX f), h⟩)
  have hAval : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
      ((Classical.choose (killUQuot_surjective f ⟨(a : KillX f), h⟩) : ↥(KillUpre f)) :
        Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f) = (a : KillX f) := by
    simpa only [killUQuot_apply] using
      congrArg (fun w : ↥(KillU f) => (w : KillX f)) hspec
  rw [pushGarbage_fix (KillUpre_subset_pushDomain f
      (Classical.choose (killUQuot_surjective f ⟨(a : KillX f), h⟩)).2) ?_ 1]
  · exact hAval
  · rw [hAval]
    exact a.2

theorem killUPushFun_shell (f : ι → C(cellSphere n, Y)) (i : ι)
    (x : ↥(cellShellSet n (1 / 4) (1 / 2)))
    (h : cellMap n Y ι f i (x : cellDisk n) ∈ KillZ f) :
    killUPushFun f
        ⟨cellMap n Y ι f i (x : cellDisk n), KillZ_subset_KillU f h⟩
      = KillShellToA f ⟨i, x⟩ := by
  apply Subtype.ext
  change pushGarbage n Y ι f
      ((Classical.choose (killUQuot_surjective f ⟨cellMap n Y ι f i (x : cellDisk n),
        KillZ_subset_KillU f h⟩) : ↥(KillUpre f)) : Y ⊕ (Σ _ : ι, cellDisk n)) 1
    = attachIncl n Y ι f (f i (shellDir x))
  have hspec := Classical.choose_spec (killUQuot_surjective f
    ⟨cellMap n Y ι f i (x : cellDisk n), KillZ_subset_KillU f h⟩)
  have hAval : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
      ((Classical.choose (killUQuot_surjective f ⟨cellMap n Y ι f i (x : cellDisk n),
        KillZ_subset_KillU f h⟩) : ↥(KillUpre f)) : Y ⊕ (Σ _ : ι, cellDisk n)) :
        attachCells n Y ι f) = cellMap n Y ι f i (x : cellDisk n) := by
    simpa only [killUQuot_apply] using
      congrArg (fun w : ↥(KillU f) => (w : KillX f)) hspec
  have hrel : Relation.EqvGen (attachRel n Y ι f)
      ((Classical.choose (killUQuot_surjective f ⟨cellMap n Y ι f i (x : cellDisk n),
        KillZ_subset_KillU f h⟩) : ↥(KillUpre f)) : Y ⊕ (Σ _ : ι, cellDisk n))
      (Sum.inr ⟨i, (x : cellDisk n)⟩) := by
    refine Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f)) ?_
    show (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
        ((Classical.choose (killUQuot_surjective f ⟨cellMap n Y ι f i (x : cellDisk n),
          KillZ_subset_KillU f h⟩) : ↥(KillUpre f)) : Y ⊕ (Σ _ : ι, cellDisk n)) :
          attachCells n Y ι f)
      = (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
          (Sum.inr ⟨i, (x : cellDisk n)⟩) : attachCells n Y ι f)
    rw [hAval]
    rfl
  have hx0 : ((x : cellDisk n) : CellVec n) ≠ 0 := by
    intro h0
    have h' := x.2.1
    rw [h0, norm_zero] at h'
    norm_num at h'
  have hB : (Sum.inr ⟨i, (x : cellDisk n)⟩ : Y ⊕ (Σ _ : ι, cellDisk n)) ∈
      pushDomain n Y ι f :=
    (mem_pushDomain_iff (f := f) _).mpr (Or.inr ⟨i, (x : cellDisk n), hx0, rfl⟩)
  rw [pushGarbage_eq_of_eqvGen (f := f) 1 hrel (KillUpre_subset_pushDomain f
      (Classical.choose (killUQuot_surjective f ⟨cellMap n Y ι f i (x : cellDisk n),
        KillZ_subset_KillU f h⟩)).2) hB]
  rw [pushGarbage_inr (i := i) (x := (x : cellDisk n)) hx0 1]
  rw [cellPush_one_eq x hx0]
  rw [attachIncl_attachRel n Y ι f i (shellDir x)]

theorem killUPushFun_continuous (f : ι → C(cellSphere n, Y)) :
    Continuous (killUPushFun f) := by
  have hG : Continuous (killUPushRaw f) := by
    refine Topology.IsQuotientMap.continuous_lift_prod_left (killUQuot_isQuotientMap f) ?_
    have hcomp : (fun p : ↥(KillUpre f) × I => killUPushRaw f (killUQuot f p.1, p.2)) =
        fun p : ↥(KillUpre f) × I =>
          (⟨pushGarbage n Y ι f (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) p.2,
            Work.Serre.CellStep.pushGarbage_mem_cellU f (by norm_num) (by norm_num)
              p.1.2 p.2⟩ : ↥(KillU f)) := by
      funext p
      apply Subtype.ext
      show pushGarbage n Y ι f
          ((Classical.choose (killUQuot_surjective f (killUQuot f p.1)) :
            ↥(KillUpre f)) : Y ⊕ (Σ _ : ι, cellDisk n)) p.2
        = pushGarbage n Y ι f (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) p.2
      exact pushGarbage_eq_of_eqvGen (f := f) p.2
        (Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f))
          (show (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
              ((Classical.choose (killUQuot_surjective f (killUQuot f p.1)) :
                ↥(KillUpre f)) : Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f)
            = Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
              (p.1 : Y ⊕ (Σ _ : ι, cellDisk n))
            from congrArg (fun w : ↥(KillU f) => (w : KillX f))
              (Classical.choose_spec (killUQuot_surjective f (killUQuot f p.1)))))
        (KillUpre_subset_pushDomain f
          (Classical.choose (killUQuot_surjective f (killUQuot f p.1))).2)
        (KillUpre_subset_pushDomain f p.1.2)
    rw [hcomp]
    exact Continuous.subtype_mk
      ((continuous_pushGarbage (f := f)).comp (Continuous.prodMap
        (Continuous.subtype_mk continuous_subtype_val
          (fun x : ↥(KillUpre f) => KillUpre_subset_pushDomain f x.2))
        continuous_id))
      (fun p => Work.Serre.CellStep.pushGarbage_mem_cellU f (by norm_num) (by norm_num)
        p.1.2 p.2)
  have h : Continuous (fun v : ↥(KillU f) =>
      ((killUPushRaw f (v, 1) : ↥(KillU f)) : KillX f)) :=
    continuous_subtype_val.comp (hG.comp (continuous_id.prodMk continuous_const))
  exact h.subtype_mk _

/-! ### The assembly -/

theorem serreC0KillRho {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    ∃ (ρ : C(↥(Work.Serre.KillU f), ↥(Work.Serre.KillA f)))
      (e : ↥(Work.Serre.KillZ f) ≃ₜ (Σ i : ι, ↥(Work.Serre.cellShellSet n (1 / 4) (1 / 2)))),
      (∀ a : ↥(Work.Serre.KillA f), ρ ⟨(a : Work.Serre.KillX f), Work.Serre.KillA_subset_KillU f a.2⟩ = a) ∧
      (∀ z : ↥(Work.Serre.KillZ f),
        ρ ⟨(z : Work.Serre.KillX f), Work.Serre.KillZ_subset_KillU f z.2⟩
          = Work.Serre.KillShellToA f (e z)) := by
  let H : (Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2))) ≃ₜ ↥(KillZ f) :=
    (Equiv.ofBijective (killZShellMap f) (killZShellMap_bijective f)).toHomeomorphOfContinuousOpen
      (killZShellMap f).continuous (killZShellMap_isOpenMap f)
  have hHz : ∀ z : ↥(KillZ f), killZShellMap f (H.symm z) = z := by
    intro z
    have h1 : H (H.symm z) = z := H.apply_symm_apply z
    have h2 : H (H.symm z) = killZShellMap f (H.symm z) := rfl
    rw [h2] at h1
    exact h1
  refine ⟨⟨killUPushFun f, killUPushFun_continuous f⟩, H.symm, ?_, ?_⟩
  · intro a
    exact killUPushFun_fix f a (KillA_subset_KillU f a.2)
  · intro z
    have hval : ((killZShellMap f (H.symm z) : ↥(KillZ f)) : KillX f) = (z : KillX f) :=
      congrArg (fun w : ↥(KillZ f) => (w : KillX f)) (hHz z)
    have hshell := killUPushFun_shell f (H.symm z).1 (H.symm z).2 (killZShellMap f (H.symm z)).2
    have hsub : (⟨(z : KillX f), KillZ_subset_KillU f z.2⟩ : ↥(KillU f)) =
        ⟨((killZShellMap f (H.symm z) : ↥(KillZ f)) : KillX f),
          KillZ_subset_KillU f (killZShellMap f (H.symm z)).2⟩ := Subtype.ext hval.symm
    rw [hsub]
    exact hshell

end

end Work.Serre
