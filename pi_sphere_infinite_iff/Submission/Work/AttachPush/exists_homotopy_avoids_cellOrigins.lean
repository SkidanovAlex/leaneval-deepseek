import Mathlib
import Submission.Work.RatHurewicz.AttachPush.Defs
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.RatHurewicz.AttachPush.PushOffAux
import Submission.Work.AttachPush.exists_contDiff_approx_ne_zero
import Submission.Work.AttachPush.isClosed_cellMap_image_closedBall
import Submission.Work.AttachPush.exists_continuous_approx_ne_zero_cube

open scoped Topology unitInterval
open Work.RatHurewicz

namespace Work.AttachPush

/-! ## Auxiliary point-set lemmas -/

/-- The image of the closed `ρ`-ball of the model cell, `ρ < 1`, lies in the interior of the
attached cell. -/
theorem cellMap_image_closedBall_subset_cellInterior (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(cellSphere n, Y)) (i : ι) {ρ : ℝ} (hρ : ρ < 1) :
    cellMap n Y ι f i '' {y : cellDisk n | ‖(y : CellVec n)‖ ≤ ρ}
      ⊆ cellInterior n Y ι f i := by
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, lt_of_le_of_lt hy hρ, rfl⟩

/-- **The chart characterization of the closed `ρ`-ball image**: for a point `z` in the interior of
the `i`-th cell, `z` lies in the image of the closed `ρ`-ball (`ρ < 1`) if and only if its chart
coordinate has norm `≤ ρ`. -/
theorem mem_cellMap_image_closedBall_iff (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (i : ι)
    (S : C(↥(cellInterior n Y ι f i), ↥(cellInner n)))
    (hS : ∀ y, cellMap n Y ι f i ((S y : ↥(cellInner n)) : cellDisk n) = (y : attachCells n Y ι f))
    {ρ : ℝ} (hρ : ρ < 1) {z : attachCells n Y ι f} (hz : z ∈ cellInterior n Y ι f i) :
    z ∈ cellMap n Y ι f i '' {y : cellDisk n | ‖(y : CellVec n)‖ ≤ ρ} ↔
      ‖((S ⟨z, hz⟩ : ↥(cellInner n)) : CellVec n)‖ ≤ ρ := by
  constructor
  · rintro ⟨y, hy, hyz⟩
    have hyc : y ∈ cellInner n := lt_of_le_of_lt hy hρ
    have hSc : ((S ⟨z, hz⟩ : ↥(cellInner n)) : cellDisk n) ∈ cellInner n := (S ⟨z, hz⟩).2
    have hinj := cellMap_injective_cellInner (n := n) (Y := Y) (ι := ι) (f := f) i
    have heq : (⟨((S ⟨z, hz⟩ : ↥(cellInner n)) : cellDisk n), hSc⟩ : ↥(cellInner n)) =
        (⟨y, hyc⟩ : ↥(cellInner n)) := by
      apply hinj
      show cellMap n Y ι f i ((S ⟨z, hz⟩ : ↥(cellInner n)) : cellDisk n) = cellMap n Y ι f i y
      rw [hS ⟨z, hz⟩]
      exact hyz.symm
    have hval : ((S ⟨z, hz⟩ : ↥(cellInner n)) : cellDisk n) = y := congrArg Subtype.val heq
    rwa [hval]
  · intro h
    exact ⟨((S ⟨z, hz⟩ : ↥(cellInner n)) : cellDisk n), h, hS ⟨z, hz⟩⟩

/-- **A Urysohn cutoff between a closed set and an open set containing it.**  There is a continuous
`χ : I^d → ℝ` with values in `[0,1]`, equal to `1` on `A`, vanishing outside `U`, and whose support
closure is still contained in `U`. -/
theorem exists_cutoff_of_isClosed_subset_open {d : ℕ} {A U : Set (ICube d)}
    (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ χ : C(ICube d, ℝ), (∀ x ∈ A, χ x = 1) ∧ (∀ x, χ x ≠ 0 → x ∈ U) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ closure {x | χ x ≠ 0} ⊆ U := by
  obtain ⟨V, hVopen, hAV, hVcl⟩ := normal_exists_closure_subset hA hU hAU
  have hdisj : Disjoint (Vᶜ) A := by
    rw [Set.disjoint_left]
    intro x hx hxA
    exact hx (hAV hxA)
  obtain ⟨χ, hχ0, hχ1, hχr⟩ :=
    exists_continuous_zero_one_of_isClosed hVopen.isClosed_compl hA hdisj
  refine ⟨χ, fun x hx => hχ1 hx, ?_, fun x => hχr x, ?_⟩
  · intro x hx
    by_contra hxU
    exact hx (hχ0 (fun hxV => hxU (hVcl (subset_closure hxV))))
  · have hsub : {x : ICube d | χ x ≠ 0} ⊆ V := by
      intro x hx
      by_contra hxV
      exact hx (hχ0 hxV)
    exact subset_trans (closure_mono hsub) hVcl

/-! ## Two point-set lemmas about the model cell -/

/-- A point of the model cell which is not in the open model cell has norm one. -/
theorem norm_eq_one_of_not_mem_cellInner {n : ℕ} {u : cellDisk n} (h : u ∉ cellInner n) :
    ‖(u : CellVec n)‖ = 1 := by
  have hle : ‖(u : CellVec n)‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp u.2
    simpa [dist_eq_norm] using this
  have hge : 1 ≤ ‖(u : CellVec n)‖ := not_lt.mp h
  exact le_antisymm hle hge

/-- **A boundary point of the model cell maps into the range of `attachIncl`.** -/
theorem cellMap_mem_range_attachIncl_of_norm_eq_one (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(cellSphere n, Y)) (i : ι) {u : cellDisk n}
    (h : ‖(u : CellVec n)‖ = 1) :
    cellMap n Y ι f i u ∈ Set.range (attachIncl n Y ι f) := by
  let z : cellSphere n := ⟨(u : CellVec n),
    by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h⟩
  refine ⟨f i z, ?_⟩
  have h3 : cellSphereToDisk n z = u := Subtype.ext rfl
  calc attachIncl n Y ι f (f i z) = cellMap n Y ι f i (cellSphereToDisk n z) :=
        attachIncl_attachRel n Y ι f i z
    _ = cellMap n Y ι f i u := by rw [h3]

/-! ## Sets with at most one point per cell interior are closed -/

/-- **A set which lies in the union of the cell interiors and meets each cell interior in at most
one point is closed.**  This is the point-set content of "a compact subset of a cell complex meets
only finitely many cells". -/
theorem isClosed_of_subsingleton_on_cellInterior (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(cellSphere n, Y)) (A : Set (attachCells n Y ι f))
    (hAsub : A ⊆ ⋃ i, cellInterior n Y ι f i)
    (hAuniq : ∀ i, (A ∩ cellInterior n Y ι f i).Subsingleton) : IsClosed A := by
  classical
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Y ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Y ι f) :=
    (isQuotientMap_quotient_mk' (X := Y ⊕ (Σ _ : ι, cellDisk n))
      (s := Relation.EqvGen.setoid (attachRel n Y ι f))).isCoinducing
  refine (hq.isClosed_preimage (s := A)).mp ?_
  rw [← isOpen_compl_iff]
  set V : Set (Y ⊕ (Σ _ : ι, cellDisk n)) :=
    {a | (∃ y, a = Sum.inl y) ∨ ∃ (i : ι) (u : cellDisk n),
      a = Sum.inr ⟨i, u⟩ ∧ cellMap n Y ι f i u ∉ A} with hVdef
  have hVeq : (Quotient.mk'' ⁻¹' A : Set (Y ⊕ (Σ _ : ι, cellDisk n)))ᶜ = V := by
    ext a
    rcases a with y | ⟨i, u⟩
    · constructor
      · intro _; exact Or.inl ⟨y, rfl⟩
      · intro _
        simp only [Set.mem_compl_iff, Set.mem_preimage]
        intro hmem
        have h1 : (Quotient.mk'' (Sum.inl y) : attachCells n Y ι f) ∈
            Set.range (attachIncl n Y ι f) := ⟨y, rfl⟩
        rw [range_attachIncl_eq_compl_iUnion_cellInterior] at h1
        exact h1 (hAsub hmem)
    · constructor
      · intro h
        simp only [Set.mem_compl_iff, Set.mem_preimage] at h
        exact Or.inr ⟨i, u, rfl, h⟩
      · rintro (⟨y, hy⟩ | ⟨j, u', h, hA'⟩)
        · exact absurd hy Sum.inr_ne_inl
        · simp only [Set.mem_compl_iff, Set.mem_preimage]
          have h1 : (⟨i, u⟩ : Σ _ : ι, cellDisk n) = ⟨j, u'⟩ := Sum.inr.inj h
          have h2 : i = j := congrArg Sigma.fst h1
          have h3 : u = u' := congrArg Sigma.snd h1
          subst h2; subst h3
          exact hA'
  rw [hVeq]
  have hVopen : IsOpen V := by
    rw [isOpen_sum_iff]
    refine ⟨?_, ?_⟩
    · have huniv : Sum.inl ⁻¹' V = Set.univ := by
        ext y
        exact ⟨fun _ => trivial, fun _ => Or.inl ⟨y, rfl⟩⟩
      rw [huniv]; exact isOpen_univ
    · rw [isOpen_sigma_iff]
      intro i
      have hpiece : Sigma.mk i ⁻¹' (Sum.inr ⁻¹' V) =
          {u : cellDisk n | cellMap n Y ι f i u ∉ A} := by
        ext u
        constructor
        · rintro (⟨y, hy⟩ | ⟨j, u', h, hA'⟩)
          · exact absurd hy Sum.inr_ne_inl
          · have h1 : (⟨i, u⟩ : Σ _ : ι, cellDisk n) = ⟨j, u'⟩ := Sum.inr.inj h
            have h2 : i = j := congrArg Sigma.fst h1
            have h3 : u = u' := congrArg Sigma.snd h1
            subst h2; subst h3
            exact hA'
        · intro h; exact Or.inr ⟨i, u, rfl, h⟩
      rw [hpiece]
      let F : Set (cellDisk n) := {u : cellDisk n | cellMap n Y ι f i u ∈ A}
      have hFball : F ⊆ cellInner n := by
        intro u hu
        by_contra hcon
        have h1 : cellMap n Y ι f i u ∈ Set.range (attachIncl n Y ι f) :=
          cellMap_mem_range_attachIncl_of_norm_eq_one n Y ι f i
            (norm_eq_one_of_not_mem_cellInner hcon)
        rw [range_attachIncl_eq_compl_iUnion_cellInterior] at h1
        exact h1 (hAsub hu)
      have hFuniq : F.Subsingleton := by
        intro u hu u' hu'
        have h1 : cellMap n Y ι f i u ∈ A ∩ cellInterior n Y ι f i := ⟨hu, ⟨u, hFball hu, rfl⟩⟩
        have h2 : cellMap n Y ι f i u' ∈ A ∩ cellInterior n Y ι f i := ⟨hu', ⟨u', hFball hu', rfl⟩⟩
        have h3 := hAuniq i h1 h2
        have h4 : (⟨u, hFball hu⟩ : ↥(cellInner n)) = ⟨u', hFball hu'⟩ :=
          cellMap_injective_cellInner (n := n) (Y := Y) (ι := ι) (f := f) i (by
            show cellMap n Y ι f i ((⟨u, hFball hu⟩ : ↥(cellInner n)) : cellDisk n) =
              cellMap n Y ι f i ((⟨u', hFball hu'⟩ : ↥(cellInner n)) : cellDisk n)
            exact h3)
        exact congrArg Subtype.val h4
      have hFcl : IsClosed F := by
        rcases Set.eq_empty_or_nonempty F with hF | ⟨v, hvF⟩
        · rw [hF]; exact isClosed_empty
        · have hFsingle : F = {v} := by
            refine Set.eq_singleton_iff_unique_mem.mpr ⟨hvF, ?_⟩
            intro w hw
            exact hFuniq hw hvF
          rw [hFsingle]; exact isClosed_singleton
      have hgoal : {u : cellDisk n | cellMap n Y ι f i u ∉ A} = Fᶜ := rfl
      rw [hgoal]
      exact hFcl.isOpen_compl
  exact hVopen

/-! ## A compact set meets only finitely many cell interiors -/

/-- **A compact subset of `attachCells n Y ι f` meets only finitely many cell interiors.** -/
theorem finite_meets_cellInterior (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {K : Set (attachCells n Y ι f)} (hK : IsCompact K) :
    {i : ι | (K ∩ cellInterior n Y ι f i).Nonempty}.Finite := by
  classical
  by_contra hfin
  set J : Set ι := {i | (K ∩ cellInterior n Y ι f i).Nonempty} with hJdef
  have hJinf : J.Infinite := hfin
  choose pt hpt using fun i : J => i.2
  set A : Set (attachCells n Y ι f) := Set.range pt with hAdef
  have hptinj : Function.Injective pt := by
    intro i j hij
    refine Subtype.ext ?_
    by_contra hne
    have h1 : pt i ∈ cellInterior n Y ι f i.1 := (hpt i).2
    have h2 : pt j ∈ cellInterior n Y ι f j.1 := (hpt j).2
    rw [hij] at h1
    exact Set.disjoint_left.mp (disjoint_cellInterior (f := f) i.1 j.1 hne) h1 h2
  have hAsub : A ⊆ ⋃ i, cellInterior n Y ι f i := by
    rintro x ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i.1, (hpt i).2⟩
  have hAuniq : ∀ i, (A ∩ cellInterior n Y ι f i).Subsingleton := by
    rintro j x ⟨⟨i, rfl⟩, hx⟩ y ⟨⟨i', rfl⟩, hy⟩
    have hi : i.1 = j := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_cellInterior (f := f) i.1 j hne) (hpt i).2 hx
    have hi' : i'.1 = j := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_cellInterior (f := f) i'.1 j hne) (hpt i').2 hy
    have hii : i = i' := Subtype.ext (by rw [hi, hi'])
    rw [hii]
  have hAcl : IsClosed A := isClosed_of_subsingleton_on_cellInterior n Y ι f A hAsub hAuniq
  have hAK : A ⊆ K := by rintro x ⟨i, rfl⟩; exact (hpt i).1
  have hAcpt : IsCompact A := hK.of_isClosed_subset hAcl hAK
  have hdiffcl : ∀ a : A, IsClosed (A \ {(a : attachCells n Y ι f)}) := by
    intro a
    refine isClosed_of_subsingleton_on_cellInterior n Y ι f _ ?_ ?_
    · intro x hx; exact hAsub hx.1
    · intro i x hx y hy
      exact hAuniq i ⟨hx.1.1, hx.2⟩ ⟨hy.1.1, hy.2⟩
  have hcover : A ⊆ ⋃ a : A, ((A \ {(a : attachCells n Y ι f)})ᶜ :
      Set (attachCells n Y ι f)) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simp
  obtain ⟨t, ht⟩ := hAcpt.elim_finite_subcover
    (fun a : A => (A \ {(a : attachCells n Y ι f)})ᶜ)
    (fun a => (hdiffcl a).isOpen_compl) hcover
  have hAfin : A.Finite := by
    refine Set.Finite.subset (t.finite_toSet.image Subtype.val) ?_
    intro x hx
    obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hxa' : x ∉ A \ {(a : attachCells n Y ι f)} := hxa
    have hval : x = (a : attachCells n Y ι f) := by
      by_contra hne
      exact hxa' ⟨hx, hne⟩
    rw [hval]
    rw [Set.mem_image]
    exact ⟨a, Finset.mem_coe.mpr hat, rfl⟩
  have hAinf : A.Infinite := by
    rw [hAdef]
    exact (Set.infinite_range_iff hptinj).mpr hJinf.to_subtype
  exact hAinf hAfin



/-- The characteristic map of the `i`-th cell takes the centre of the model disc to the centre of the
cell, and no other point of the *open* model disc to that cell centre. -/
theorem cellMap_eq_cellOrigin_iff (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (i : ι) {u : cellDisk n} (hu : u ∈ cellInner n) :
    cellMap n Y ι f i u = cellOrigin n Y ι f i ↔ u = cellDiskCentre n := by
  constructor
  · intro h
    have h1 : (⟨u, hu⟩ : ↥(cellInner n)) =
        ⟨cellDiskCentre n, by simp [cellInner, cellDiskCentre]⟩ := by
      apply cellMap_injective_cellInner (n := n) (Y := Y) (ι := ι) (f := f) i
      show cellMap n Y ι f i u = cellMap n Y ι f i (cellDiskCentre n)
      rw [h]
      rfl
    simpa using congrArg Subtype.val h1
  · rintro rfl
    rfl

/-- **The general position step of the push-off**: a map of the `d`-cube into `attachCells n Y ι f`,
`d ≤ n+1`, whose boundary already lies in the range of `attachIncl`, is homotopic relative to its
boundary to a map avoiding every cell centre `cellOrigin i`.

The construction is cellwise: on the part of the cube mapping into the interior of the `i`-th cell
the map lifts to the model disc; a cutoff `χ i` (equal to `1` where the lift is close to the centre,
supported away from the boundary of the cell) and a continuous map `P i`, `1/8`-close to the lift
on the support of `χ i` and nowhere zero where `χ i = 1`, given by the Sard-based approximation
`exists_continuous_approx_ne_zero_cube` (with `d < n+2`), produce an interpolation
`w = lift + χ i • (P i - lift)` that is never zero. -/
theorem exists_homotopy_avoids_cellOrigins (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {d : ℕ} (hd : d ≤ n + 1)
    (g : C(Work.RatHurewicz.ICube d, Work.RatHurewicz.attachCells n Y ι f))
    (hg : ∀ x, x ∈ Cube.boundary (Fin d) → g x ∈
      Set.range (Work.RatHurewicz.attachIncl n Y ι f)) :
    ∃ (g₁ : C(Work.RatHurewicz.ICube d, Work.RatHurewicz.attachCells n Y ι f))
      (H : C(Work.RatHurewicz.ICube d × unitInterval,
        Work.RatHurewicz.attachCells n Y ι f)),
      (∀ x, H (x, 0) = g x) ∧
      (∀ x, x ∈ Cube.boundary (Fin d) → ∀ t : unitInterval, H (x, t) = g x) ∧
      (∀ x, H (x, 1) = g₁ x) ∧
      (∀ (i : ι) (x : Work.RatHurewicz.ICube d),
        g₁ x ≠ Work.RatHurewicz.cellOrigin n Y ι f i) := by
  classical
  have hdk : d < n + 2 := by omega
  have hsec : ∀ i : ι, ∃ S : C(↥(Work.RatHurewicz.cellInterior n Y ι f i),
      ↥(Work.RatHurewicz.cellInner n)),
      ∀ y, Work.RatHurewicz.cellMap n Y ι f i
        ((S y : ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n) =
        (y : Work.RatHurewicz.attachCells n Y ι f) :=
    fun i => Work.RatHurewicz.cellInterior_section (n := n) (Y := Y) (ι := ι) (f := f) i
  choose S hSspec using hsec
  let W : ι → Set (Work.RatHurewicz.ICube d) := fun i =>
    g ⁻¹' (Work.RatHurewicz.cellInterior n Y ι f i)
  have hWopen : ∀ i, IsOpen (W i) := fun i =>
    (Work.RatHurewicz.isOpen_cellInterior (n := n) (Y := Y) (ι := ι) (f := f) i).preimage
      g.continuous
  let liftV : ι → Work.RatHurewicz.ICube d → Work.RatHurewicz.CellVec n := fun i x =>
    if hx : x ∈ W i then
      ((S i ⟨g x, hx⟩ : ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.CellVec n) else 0
  have hliftV_zero : ∀ (i : ι) (x : Work.RatHurewicz.ICube d), x ∉ W i → liftV i x = 0 := by
    intro i x hx
    simp only [liftV]
    exact dif_neg hx
  have hliftV_val : ∀ (i : ι) (x : Work.RatHurewicz.ICube d) (hx : x ∈ W i), liftV i x =
      ((S i ⟨g x, hx⟩ : ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.CellVec n) := by
    intro i x hx
    simp only [liftV]
    exact dif_pos hx
  have hliftV_norm : ∀ (i : ι) (x : Work.RatHurewicz.ICube d),
      ‖liftV i x‖ ≤ 1 := by
    intro i x
    by_cases hx : x ∈ W i
    · rw [hliftV_val i x hx]
      exact le_of_lt (S i ⟨g x, hx⟩).2
    · rw [hliftV_zero i x hx, norm_zero]
      norm_num
  have hdata : ∀ i : ι, ∃ (χ : C(Work.RatHurewicz.ICube d, ℝ))
      (P : Work.RatHurewicz.ICube d → Work.RatHurewicz.CellVec n),
      (closure {x : Work.RatHurewicz.ICube d | χ x ≠ 0} ⊆ W i) ∧
      (∀ x, g x ∈ Work.RatHurewicz.cellMap n Y ι f i ''
        {y : Work.RatHurewicz.cellDisk n | ‖(y : Work.RatHurewicz.CellVec n)‖ ≤ 1/4} →
        χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      Continuous P ∧ (∀ x, ‖P x‖ ≤ 1) ∧
      (∀ x, χ x ≠ 0 → ‖P x - liftV i x‖ < 1/8) ∧
      (∀ x, χ x = 1 → P x ≠ 0) := by
    intro i
    set A : Set (Work.RatHurewicz.ICube d) := g ⁻¹'
      (Work.RatHurewicz.cellMap n Y ι f i ''
        {y : Work.RatHurewicz.cellDisk n | ‖(y : Work.RatHurewicz.CellVec n)‖ ≤ 1/4}) with hAdef
    have hAcl : IsClosed A := (Work.AttachPush.isClosed_cellMap_image_closedBall n Y ι f i
      (by norm_num)).preimage g.continuous
    have hAU : A ⊆ W i := fun x hx =>
      cellMap_image_closedBall_subset_cellInterior n Y ι f i (by norm_num) hx
    obtain ⟨χ, hχ1, hχmem, hχr, hχsupp⟩ :=
      exists_cutoff_of_isClosed_subset_open hAcl (hWopen i) hAU
    have hK₁cl : IsClosed {x : Work.RatHurewicz.ICube d | χ x = 1} :=
      isClosed_eq χ.continuous continuous_const
    have hK₂cl : IsClosed (closure {x : Work.RatHurewicz.ICube d | χ x ≠ 0}) := isClosed_closure
    have hK₁K₂ : {x : Work.RatHurewicz.ICube d | χ x = 1} ⊆
        closure {x : Work.RatHurewicz.ICube d | χ x ≠ 0} := by
      intro x hx
      exact subset_closure (by rw [Set.mem_ofPred_eq]; rw [hx]; norm_num)
    let ψ : C(↥(closure {x : Work.RatHurewicz.ICube d | χ x ≠ 0}),
        Work.RatHurewicz.CellVec n) :=
      { toFun := fun x =>
          ((S i ⟨g x.1, hχsupp x.2⟩ : ↥(Work.RatHurewicz.cellInner n)) :
            Work.RatHurewicz.CellVec n)
        continuous_toFun := by
          refine continuous_subtype_val.comp (continuous_subtype_val.comp
            ((S i).continuous.comp ?_))
          exact Continuous.subtype_mk (g.continuous.comp continuous_subtype_val)
            (fun x => hχsupp x.2) }
    have hψ1 : ∀ x : ↥(closure {x : Work.RatHurewicz.ICube d | χ x ≠ 0}), ‖ψ x‖ ≤ 1 := by
      intro x
      exact le_of_lt (S i ⟨g x.1, hχsupp x.2⟩).2
    obtain ⟨P, hPcont, hPnorm, hPclose, hPne⟩ :=
      exists_continuous_approx_ne_zero_cube hdk hK₁cl.isCompact hK₂cl.isCompact hK₁K₂ ψ hψ1
        (ε := 1/8) (by norm_num)
    refine ⟨χ, P, hχsupp, fun x hx => hχ1 x hx, hχr, hPcont, hPnorm, ?_, ?_⟩
    · intro x hx
      have hxK₂ : x ∈ closure {x : Work.RatHurewicz.ICube d | χ x ≠ 0} :=
        subset_closure (by simpa using hx)
      have h1 := hPclose ⟨x, hxK₂⟩
      have h2 : liftV i x = ψ ⟨x, hxK₂⟩ := by
        rw [hliftV_val i x (hχsupp hxK₂)]
        rfl
      rw [← h2] at h1
      exact h1
    · intro x hx
      exact hPne ⟨x, hx⟩
  choose χ P hχsupp hχA hχr hPcont hPnorm hPclose hPne using hdata
  let pick (p : Work.RatHurewicz.ICube d × unitInterval)
      (h : ∃ i, χ i p.1 ≠ 0) : ι := Classical.choose h
  have hpick : ∀ (p : Work.RatHurewicz.ICube d × unitInterval) (h : ∃ i, χ i p.1 ≠ 0),
      χ (pick p h) p.1 ≠ 0 := fun p h => Classical.choose_spec h
  have huniq : ∀ (i j : ι) (x : Work.RatHurewicz.ICube d), χ i x ≠ 0 → χ j x ≠ 0 → i = j := by
    intro i j x hi hj
    by_contra hij
    have h1 : x ∈ W i := hχsupp i (subset_closure (by simpa using hi))
    have h2 : x ∈ W j := hχsupp j (subset_closure (by simpa using hj))
    exact Set.disjoint_left.mp (Work.RatHurewicz.disjoint_cellInterior (f := f) i j hij) h1 h2
  let wfun (i : ι) (p : Work.RatHurewicz.ICube d × unitInterval) :
      Work.RatHurewicz.CellVec n :=
    liftV i p.1 + ((χ i p.1 * (p.2 : ℝ))) • (P i p.1 - liftV i p.1)
  have hwfun_norm : ∀ (i : ι) (p : Work.RatHurewicz.ICube d × unitInterval),
      ‖wfun i p‖ ≤ 1 := by
    intro i p
    set θ : ℝ := χ i p.1 * (p.2 : ℝ) with hθdef
    have hθ0 : 0 ≤ θ := mul_nonneg (hχr i p.1).1 (Set.mem_Icc.mp p.2.2).1
    have hθ1 : θ ≤ 1 := by
      have h1 : χ i p.1 ≤ 1 := (hχr i p.1).2
      have h2 : (p.2 : ℝ) ≤ 1 := (Set.mem_Icc.mp p.2.2).2
      have h3 : 0 ≤ χ i p.1 := (hχr i p.1).1
      have h4 : 0 ≤ (p.2 : ℝ) := (Set.mem_Icc.mp p.2.2).1
      nlinarith
    have hw : wfun i p = (1 - θ) • liftV i p.1 + θ • P i p.1 := by
      simp only [wfun, hθdef]
      rw [smul_sub]
      module
    rw [hw]
    calc ‖(1 - θ) • liftV i p.1 + θ • P i p.1‖
        ≤ ‖(1 - θ) • liftV i p.1‖ + ‖θ • P i p.1‖ := norm_add_le _ _
      _ = (1 - θ) * ‖liftV i p.1‖ + θ * ‖P i p.1‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
      _ ≤ (1 - θ) * 1 + θ * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hliftV_norm i p.1) (by linarith))
            (mul_le_mul_of_nonneg_left (hPnorm i p.1) hθ0)
      _ = 1 := by ring
  have hwfun_mem : ∀ (i : ι) (p : Work.RatHurewicz.ICube d × unitInterval),
      wfun i p ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro i p
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hwfun_norm i p
  have hliftV_mem : ∀ (i : ι) (x : Work.RatHurewicz.ICube d),
      liftV i x ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro i x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hliftV_norm i x
  let Hfun : Work.RatHurewicz.ICube d × unitInterval →
      Work.RatHurewicz.attachCells n Y ι f := fun p =>
    if h : ∃ i, χ i p.1 ≠ 0 then
      Work.RatHurewicz.cellMap n Y ι f (pick p h)
        ⟨wfun (pick p h) p, hwfun_mem (pick p h) p⟩
    else g p.1
  have hliftOn : ∀ i : ι, ContinuousOn (fun x : Work.RatHurewicz.ICube d => liftV i x) (W i) := by
    intro i
    have h1 : Continuous fun x : ↥(W i) => liftV i x.1 := by
      have heq : (fun x : ↥(W i) => liftV i x.1) = fun x : ↥(W i) =>
          ((S i ⟨g x.1, x.2⟩ : ↥(Work.RatHurewicz.cellInner n)) :
            Work.RatHurewicz.CellVec n) := by
        funext x
        exact hliftV_val i x.1 x.2
      rw [heq]
      refine continuous_subtype_val.comp (continuous_subtype_val.comp ((S i).continuous.comp ?_))
      exact Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) (fun x => x.2)
    rw [continuousOn_iff_continuous_domRestrict]
    exact h1
  have hpiece_cont : ∀ i : ι, ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval =>
      Work.RatHurewicz.cellMap n Y ι f i ⟨wfun i p, hwfun_mem i p⟩)
      (W i ×ˢ (Set.univ : Set unitInterval)) := by
    intro i
    have hlift' : ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval => liftV i p.1)
        (W i ×ˢ (Set.univ : Set unitInterval)) :=
      (hliftOn i).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have hP' : ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval => P i p.1)
        (W i ×ˢ (Set.univ : Set unitInterval)) :=
      ((hPcont i).comp_continuousOn continuous_fst.continuousOn).mono (Set.subset_univ _)
    have hχ' : ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval => (χ i p.1 : ℝ))
        (W i ×ˢ (Set.univ : Set unitInterval)) :=
      ((χ i).continuous.comp_continuousOn continuous_fst.continuousOn).mono (Set.subset_univ _)
    have ht' : ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval => (p.2 : ℝ))
        (W i ×ˢ (Set.univ : Set unitInterval)) :=
      (continuous_subtype_val.comp continuous_snd).continuousOn
    have hw : ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval => wfun i p)
        (W i ×ˢ (Set.univ : Set unitInterval)) := by
      show ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval =>
        liftV i p.1 + ((χ i p.1 * (p.2 : ℝ))) • (P i p.1 - liftV i p.1))
        (W i ×ˢ (Set.univ : Set unitInterval))
      exact hlift'.add ((hχ'.mul ht').smul (hP'.sub hlift'))
    have hsub : ContinuousOn (fun p : Work.RatHurewicz.ICube d × unitInterval =>
        (⟨wfun i p, hwfun_mem i p⟩ : Work.RatHurewicz.cellDisk n))
        (W i ×ˢ (Set.univ : Set unitInterval)) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuousOn_iff_continuous_domRestrict.mp hw).subtype_mk
        (fun q => hwfun_mem i q.1)
    exact (Work.RatHurewicz.cellMap n Y ι f i).continuous.comp_continuousOn hsub
  have hcont : Continuous Hfun := by
    rw [continuous_iff_continuousAt]
    intro p₀
    by_cases hW : p₀.1 ∈ ⋃ i, W i
    · obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hW
      have hnb : (W i₀ ×ˢ (Set.univ : Set unitInterval)) ∈ 𝓝 p₀ :=
        ((hWopen i₀).prod isOpen_univ).mem_nhds ⟨hi₀, trivial⟩
      have hcont_piece : ContinuousAt (fun p : Work.RatHurewicz.ICube d × unitInterval =>
          Work.RatHurewicz.cellMap n Y ι f i₀ ⟨wfun i₀ p, hwfun_mem i₀ p⟩) p₀ :=
        (hpiece_cont i₀).continuousAt hnb
      refine hcont_piece.congr ?_
      filter_upwards [hnb] with p hp
      by_cases h : ∃ i, χ i p.1 ≠ 0
      · have hpick : pick p h = i₀ := by
          by_contra hne
          have h1 : p.1 ∈ W (pick p h) :=
            hχsupp (pick p h) (subset_closure (by simpa using hpick p h))
          exact Set.disjoint_left.mp
            (Work.RatHurewicz.disjoint_cellInterior (f := f) (pick p h) i₀ hne) h1 hp.1
        have hval : Hfun p = Work.RatHurewicz.cellMap n Y ι f (pick p h)
            ⟨wfun (pick p h) p, hwfun_mem (pick p h) p⟩ := dif_pos h
        have hsub : (⟨wfun (pick p h) p, hwfun_mem (pick p h) p⟩ : Work.RatHurewicz.cellDisk n) =
            (⟨wfun i₀ p, hwfun_mem i₀ p⟩ : Work.RatHurewicz.cellDisk n) := by
          apply Subtype.ext
          rw [hpick]
        rw [hval, hsub, hpick]
      · have hχ0 : χ i₀ p.1 = 0 := by
          by_contra hne
          exact h ⟨i₀, hne⟩
        have hpiece : Work.RatHurewicz.cellMap n Y ι f i₀
            ⟨wfun i₀ p, hwfun_mem i₀ p⟩ = g p.1 := by
          have hw : wfun i₀ p = liftV i₀ p.1 := by
            simp only [wfun, hχ0, zero_mul, zero_smul, add_zero]
          have h3 : (⟨wfun i₀ p, hwfun_mem i₀ p⟩ : Work.RatHurewicz.cellDisk n) =
              (⟨liftV i₀ p.1, hliftV_mem i₀ p.1⟩ : Work.RatHurewicz.cellDisk n) :=
            Subtype.ext hw
          have h4 : (⟨liftV i₀ p.1, hliftV_mem i₀ p.1⟩ : Work.RatHurewicz.cellDisk n) =
              ((S i₀ ⟨g p.1, hp.1⟩ : ↥(Work.RatHurewicz.cellInner n)) :
                Work.RatHurewicz.cellDisk n) :=
            Subtype.ext (hliftV_val i₀ p.1 hp.1)
          rw [h3, h4]
          exact hSspec i₀ ⟨g p.1, hp.1⟩
        have hval : Hfun p = g p.1 := dif_neg h
        rw [hval]
        exact hpiece
    · set J : Set ι := {i : ι |
        (Set.range g ∩ Work.RatHurewicz.cellInterior n Y ι f i).Nonempty} with hJdef
      have hJfin : J.Finite := finite_meets_cellInterior n Y ι f (isCompact_range g.continuous)
      have hZeq : (⋃ i : ι, closure {x : Work.RatHurewicz.ICube d | χ i x ≠ 0})
          = ⋃ i ∈ hJfin.toFinset, closure {x : Work.RatHurewicz.ICube d | χ i x ≠ 0} := by
        apply le_antisymm
        · intro x hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          have hiJ : i ∈ J := by
            by_contra hiJ
            have hWi : W i = ∅ := by
              ext y
              constructor
              · intro hy
                exact absurd ⟨g y, ⟨⟨y, rfl⟩, hy⟩⟩ hiJ
              · intro hy
                exact absurd hy (by simp)
            have hxempty : x ∈ (∅ : Set (Work.RatHurewicz.ICube d)) := by
              rw [← hWi]
              exact hχsupp i hi
            exact hxempty
          exact Set.mem_iUnion₂.mpr ⟨i, hJfin.mem_toFinset.mpr hiJ, hi⟩
        · intro x hx
          obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hx
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
      have hZclosed : IsClosed (⋃ i : ι, closure {x : Work.RatHurewicz.ICube d | χ i x ≠ 0}) := by
        rw [hZeq]
        exact isClosed_biUnion_finset (s := hJfin.toFinset) (fun i _ => isClosed_closure)
      have hp₀Z : p₀.1 ∉ ⋃ i : ι, closure {x : Work.RatHurewicz.ICube d | χ i x ≠ 0} := by
        intro hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
        exact hW (Set.mem_iUnion.mpr ⟨i, hχsupp i hi⟩)
      have hnb : (((⋃ i : ι, closure {x : Work.RatHurewicz.ICube d | χ i x ≠ 0})ᶜ ×ˢ
          (Set.univ : Set unitInterval))) ∈ 𝓝 p₀ :=
        (hZclosed.isOpen_compl.prod isOpen_univ).mem_nhds ⟨hp₀Z, trivial⟩
      have hcont_g : ContinuousAt (fun p : Work.RatHurewicz.ICube d × unitInterval => g p.1)
          p₀ := (g.continuous.comp continuous_fst).continuousAt
      refine hcont_g.congr ?_
      filter_upwards [hnb] with p hp
      have hχ0 : ∀ i : ι, χ i p.1 = 0 := by
        intro i
        by_contra hne
        exact hp.1 (Set.mem_iUnion.mpr ⟨i, subset_closure (by simpa using hne)⟩)
      have hval : Hfun p = g p.1 := dif_neg (by
        rintro ⟨i, hi⟩
        exact hi (hχ0 i))
      exact hval.symm
  refine ⟨⟨fun x => Hfun (x, 1), ?_⟩, ⟨Hfun, hcont⟩, ?_, ?_, ?_, ?_⟩
  · exact hcont.comp (continuous_id.prodMk continuous_const)
  · intro x
    show Hfun (x, (0 : unitInterval)) = g x
    by_cases h : ∃ i, χ i x ≠ 0
    · have hxW : x ∈ W (pick (x, 0) h) :=
        hχsupp (pick (x, 0) h) (subset_closure (by simpa using hpick (x, 0) h))
      have hcell : Work.RatHurewicz.cellMap n Y ι f (pick (x, 0) h)
          ⟨wfun (pick (x, 0) h) (x, 0), hwfun_mem (pick (x, 0) h) (x, 0)⟩ = g x := by
        have hw : wfun (pick (x, 0) h) (x, 0) = liftV (pick (x, 0) h) x := by
          simp only [wfun]
          norm_num
        have h3 : (⟨wfun (pick (x, 0) h) (x, 0), hwfun_mem (pick (x, 0) h) (x, 0)⟩ :
              Work.RatHurewicz.cellDisk n) =
            (⟨liftV (pick (x, 0) h) x, hliftV_mem (pick (x, 0) h) x⟩ :
              Work.RatHurewicz.cellDisk n) := Subtype.ext hw
        have h4 : (⟨liftV (pick (x, 0) h) x, hliftV_mem (pick (x, 0) h) x⟩ :
              Work.RatHurewicz.cellDisk n) =
            ((S (pick (x, 0) h) ⟨g x, hxW⟩ : ↥(Work.RatHurewicz.cellInner n)) :
              Work.RatHurewicz.cellDisk n) :=
          Subtype.ext (hliftV_val (pick (x, 0) h) x hxW)
        rw [h3, h4]
        exact hSspec (pick (x, 0) h) ⟨g x, hxW⟩
      have hval : Hfun (x, (0 : unitInterval)) = Work.RatHurewicz.cellMap n Y ι f
          (pick (x, 0) h) ⟨wfun (pick (x, 0) h) (x, 0), hwfun_mem (pick (x, 0) h) (x, 0)⟩ :=
        dif_pos h
      rw [hval]
      exact hcell
    · have hval : Hfun (x, (0 : unitInterval)) = g x := dif_neg h
      exact hval
  · intro x hx t
    show Hfun (x, t) = g x
    have hxW : ∀ i : ι, x ∉ W i := by
      intro i hxWi
      have h1 : g x ∈ (⋃ i, Work.RatHurewicz.cellInterior n Y ι f i)ᶜ := by
        rw [← Work.RatHurewicz.range_attachIncl_eq_compl_iUnion_cellInterior]
        exact hg x hx
      exact h1 (Set.mem_iUnion.mpr ⟨i, hxWi⟩)
    have hχ0 : ∀ i : ι, χ i x = 0 := by
      intro i
      by_contra hne
      exact hxW i (hχsupp i (subset_closure (by simpa using hne)))
    have hval : Hfun (x, t) = g x := dif_neg (by
      rintro ⟨i, hi⟩
      exact hi (hχ0 i))
    exact hval
  · intro x
    rfl
  · intro i x
    show Hfun (x, (1 : unitInterval)) ≠ Work.RatHurewicz.cellOrigin n Y ι f i
    by_cases h : ∃ j, χ j x ≠ 0
    · have hval : Hfun (x, (1 : unitInterval)) = Work.RatHurewicz.cellMap n Y ι f
          (pick (x, 1) h) ⟨wfun (pick (x, 1) h) (x, 1), hwfun_mem (pick (x, 1) h) (x, 1)⟩ :=
        dif_pos h
      rw [hval]
      refine Work.RatHurewicz.cellMap_ne_cellOrigin (n := n) (Y := Y) (ι := ι) (f := f) ?_ i
      by_cases hχ1 : χ (pick (x, 1) h) x = 1
      · have hwnz : wfun (pick (x, 1) h) (x, 1) ≠ 0 := by
          have hw : wfun (pick (x, 1) h) (x, 1) = P (pick (x, 1) h) x := by
            simp only [wfun]
            rw [hχ1]
            norm_num
          rw [hw]
          exact hPne (pick (x, 1) h) x hχ1
        simpa using hwnz
      · have hxW : x ∈ W (pick (x, 1) h) :=
          hχsupp (pick (x, 1) h) (subset_closure (by simpa using hpick (x, 1) h))
        have hlift : 1/4 < ‖liftV (pick (x, 1) h) x‖ := by
          by_contra hle
          push_neg at hle
          have h1 : liftV (pick (x, 1) h) x =
              ((S (pick (x, 1) h) ⟨g x, hxW⟩ : ↥(Work.RatHurewicz.cellInner n)) :
                Work.RatHurewicz.CellVec n) := hliftV_val _ x hxW
          rw [h1] at hle
          have h2 : g x ∈ Work.RatHurewicz.cellMap n Y ι f (pick (x, 1) h) ''
              {y : Work.RatHurewicz.cellDisk n | ‖(y : Work.RatHurewicz.CellVec n)‖ ≤ 1/4} :=
            (mem_cellMap_image_closedBall_iff n Y ι f (pick (x, 1) h) (S (pick (x, 1) h))
              (hSspec (pick (x, 1) h)) (by norm_num) hxW).mpr hle
          exact hχ1 (hχA (pick (x, 1) h) x h2)
        have hclose := hPclose (pick (x, 1) h) x (hpick (x, 1) h)
        have hnorm : (1/8 : ℝ) < ‖wfun (pick (x, 1) h) (x, 1)‖ := by
          have hw : wfun (pick (x, 1) h) (x, 1) = liftV (pick (x, 1) h) x +
              (χ (pick (x, 1) h) x) • (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x) := by
            simp only [wfun]
            norm_num
          rw [hw]
          have h2 : ‖(χ (pick (x, 1) h) x) •
              (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x)‖ < 1/8 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχr (pick (x, 1) h) x).1]
            calc χ (pick (x, 1) h) x * ‖P (pick (x, 1) h) x - liftV (pick (x, 1) h) x‖
                ≤ 1 * ‖P (pick (x, 1) h) x - liftV (pick (x, 1) h) x‖ :=
                  mul_le_mul_of_nonneg_right (hχr (pick (x, 1) h) x).2 (norm_nonneg _)
              _ = ‖P (pick (x, 1) h) x - liftV (pick (x, 1) h) x‖ := one_mul _
              _ < 1/8 := hclose
          have h3 : ‖liftV (pick (x, 1) h) x + (χ (pick (x, 1) h) x) •
              (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x)‖ ≥
              ‖liftV (pick (x, 1) h) x‖ -
              ‖(χ (pick (x, 1) h) x) • (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x)‖ := by
            have h4 := norm_sub_le (liftV (pick (x, 1) h) x + (χ (pick (x, 1) h) x) •
              (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x))
              ((χ (pick (x, 1) h) x) • (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x))
            have h5 : liftV (pick (x, 1) h) x + (χ (pick (x, 1) h) x) •
                (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x) -
                (χ (pick (x, 1) h) x) • (P (pick (x, 1) h) x - liftV (pick (x, 1) h) x) =
                liftV (pick (x, 1) h) x := by abel
            rw [h5] at h4
            linarith
          linarith
        intro hzero
        have hz : wfun (pick (x, 1) h) (x, 1) = 0 := hzero
        rw [hz, norm_zero] at hnorm
        norm_num at hnorm
    · have hval : Hfun (x, (1 : unitInterval)) = g x := dif_neg h
      rw [hval]
      intro hcon
      have hxW : x ∈ W i := by
        show g x ∈ Work.RatHurewicz.cellInterior n Y ι f i
        rw [hcon]
        exact Work.RatHurewicz.cellOrigin_mem_cellInterior (n := n) (Y := Y) (ι := ι) (f := f) i
      have hlift0 : liftV i x = 0 := by
        have hu : ((S i ⟨g x, hxW⟩ : ↥(Work.RatHurewicz.cellInner n)) :
            Work.RatHurewicz.cellDisk n) ∈ Work.RatHurewicz.cellInner n :=
          (S i ⟨g x, hxW⟩).2
        have hcell_eq : Work.RatHurewicz.cellMap n Y ι f i
            ((S i ⟨g x, hxW⟩ : ↥(Work.RatHurewicz.cellInner n)) :
              Work.RatHurewicz.cellDisk n) = Work.RatHurewicz.cellOrigin n Y ι f i := by
          rw [hSspec i ⟨g x, hxW⟩]
          simpa using hcon
        have h1 := (cellMap_eq_cellOrigin_iff (n := n) (Y := Y) (ι := ι) (f := f) i hu).mp hcell_eq
        rw [hliftV_val i x hxW, h1, Work.RatHurewicz.cellDiskCentre_coe]
      have h1 : g x ∈ Work.RatHurewicz.cellMap n Y ι f i ''
          {y : Work.RatHurewicz.cellDisk n | ‖(y : Work.RatHurewicz.CellVec n)‖ ≤ 1/4} :=
        (mem_cellMap_image_closedBall_iff n Y ι f i (S i) (hSspec i) (by norm_num) hxW).mpr (by
          rw [← hliftV_val i x hxW, hlift0, norm_zero]
          norm_num)
      have h2 : χ i x = 1 := hχA i x h1
      exact h ⟨i, by rw [h2]; norm_num⟩


end Work.AttachPush
