import Mathlib
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.ThomBordism.excludedMV
import Submission.Work.ThomBordism.convexLocalIso
import Submission.Work.Cohomology.Endgame.shiftCap
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.homology_vanishing_relative_compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary homology lemmas for `Work.ThomBordism.localGeneration`

* `RelHmap_self`, `RelHmap_congr_h`: the restriction maps depend only on the pair of sets.
* `RelH_empty_isZero`: `H_n(M, M) = 0`.
* `unionZero`: a class on a finite union of coordinate balls which dies at one point of each ball
  is zero (Hatcher 3.27(a), uniqueness, finite-union case).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

variable {n : ℕ}

/-- The restriction attached to an inclusion `A ⊆ A` is the identity. -/
theorem RelHmap_self (M : TopCat) (n : ℕ) {A : Set M} (h : A ⊆ A) :
    RelHmap M n h = LinearMap.id := by
  have h₁ : Work.Cohomology.relCokerMap M Aᶜ Aᶜ (Set.compl_subset_compl.mpr h) = 𝟙 _ := by
    apply (cancel_epi (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ))).mp
    rw [Work.Cohomology.relCokerMap_comp_π, Category.comp_id]
  simp only [RelHmap, h₁, HomologicalComplex.homologyMap_id, ModuleCat.hom_id]

/-- The restriction map depends only on the pair of sets, not on the proof of the inclusion. -/
theorem RelHmap_congr_h (M : TopCat) (n : ℕ) {A B : Set M} (h h' : A ⊆ B) :
    RelHmap M n h = RelHmap M n h' := by
  simp only [RelHmap]

/-- `H_n(M, M) = 0`. -/
theorem RelH_empty_isZero (M : TopCat) (n : ℕ) : IsZero (RelH M n (∅ : Set M)) := by
  have h : (Work.Cohomology.relChains M (∅ : Set M)ᶜ).homology n
      = (Work.Cohomology.relChains M (Set.univ : Set M)).homology n :=
    congrArg (fun S : Set M => (Work.Cohomology.relChains M S).homology n) Set.compl_empty
  exact IsZero.of_iso (Work.Cohomology.isZero_relChains_univ M n) (eqToIso h)

/-- Composition of restriction maps, stated with the target inclusion given explicitly (so that
proofs of inclusions need not match syntactically). -/
theorem RelHmap_comp' (M : TopCat) (n : ℕ) {A B C : Set M} (h₁ : A ⊆ B) (h₂ : B ⊆ C)
    (h₃ : A ⊆ C) : (RelHmap M n h₁).comp (RelHmap M n h₂) = RelHmap M n h₃ := by
  rw [RelHmap_comp M n h₁ h₂, RelHmap_congr_h M n (h₁.trans h₂) h₃]

/-- Restriction of a restriction: for `h : A ⊆ B` and `x ∈ A`, restricting a class on `B` to the
point `x` factors through `A`. -/
theorem RelHmap_point_fac (M : TopCat) (n : ℕ) {A B : Set M} (h : A ⊆ B) {x : M} (hxA : x ∈ A) :
    RelHmap M n (Set.singleton_subset_iff.mpr (h hxA))
      = (RelHmap M n (Set.singleton_subset_iff.mpr hxA)).comp (RelHmap M n h) :=
  (RelHmap_comp' M n (Set.singleton_subset_iff.mpr hxA) h
    (Set.singleton_subset_iff.mpr (h hxA))).symm

/-- **Uniqueness for a finite union of coordinate balls** (Hatcher 3.27(a), finite-union case):
a class of `H_n(M, M∖⋃ K_i)` which dies at one point `x i ∈ K i` of each ball is zero. -/
theorem unionZero (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {ι : Type} (s : Finset ι) (K : ι → Set M) (x : ι → M)
    (hK : ∀ i ∈ s, IsCoordBall n M (K i)) (hx : ∀ i ∈ s, x i ∈ K i)
    (u : RelH M n (⋃ i ∈ s, K i))
    (hu : ∀ i (hi : i ∈ s),
      RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr ⟨i, hi, hx i hi⟩)) u = 0) :
    u = 0 := by
  classical
  have key : ∀ t : Finset ι, (∀ i ∈ t, IsCoordBall n M (K i)) → (hxs : ∀ i ∈ t, x i ∈ K i) →
      ∀ u : RelH M n (⋃ i ∈ t, K i),
        (∀ i (hi : i ∈ t),
          RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr ⟨i, hi, hxs i hi⟩)) u = 0) →
        u = 0 := by
    intro t
    refine Finset.induction_on t ?base ?step
    · intro _ _ u _
      have heq : (⋃ i ∈ (∅ : Finset ι), K i) = (∅ : Set M) := by simp
      have hI : IsZero (RelH M n (⋃ i ∈ (∅ : Finset ι), K i)) :=
        IsZero.of_iso (RelH_empty_isZero M n)
          (eqToIso (congrArg (fun S : Set M =>
            (Work.Cohomology.relChains M Sᶜ).homology n) heq))
      exact (ModuleCat.subsingleton_of_isZero hI).elim u 0
    · intro a t ha ih hKt hxt u hu
      have hKa : IsCoordBall n M (K a) := hKt a (Finset.mem_insert_self a t)
      have hxa : x a ∈ K a := hxt a (Finset.mem_insert_self a t)
      have hKt' : ∀ i ∈ t, IsCoordBall n M (K i) := fun i hi => hKt i (Finset.mem_insert_of_mem hi)
      have hxt' : ∀ i ∈ t, x i ∈ K i := fun i hi => hxt i (Finset.mem_insert_of_mem hi)
      have hWU : (K a ∪ ⋃ i ∈ t, K i) ⊆ (⋃ i ∈ insert a t, K i) := by
        intro y hy
        rcases hy with hy | hy
        · exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a t, hy⟩
        · obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
          exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hyi⟩
      have hUW : (⋃ i ∈ insert a t, K i) ⊆ (K a ∪ ⋃ i ∈ t, K i) := by
        intro y hy
        obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl hyi
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hyi⟩)
      have hKaw : K a ⊆ (K a ∪ ⋃ i ∈ t, K i) := Set.subset_union_left
      have hLw : (⋃ i ∈ t, K i) ⊆ (K a ∪ ⋃ i ∈ t, K i) := Set.subset_union_right
      have hKaU : K a ⊆ (⋃ i ∈ insert a t, K i) := hKaw.trans hWU
      have hLU : (⋃ i ∈ t, K i) ⊆ (⋃ i ∈ insert a t, K i) := hLw.trans hWU
      have hKacpt : IsCompact (K a) := hKa.isCompact
      have hLcpt : IsCompact (⋃ i ∈ t, K i) :=
        Finset.isCompact_biUnion t (fun i hi => (hKt' i hi).isCompact)
      have hzero : IsZero ((Work.Cohomology.relChains M (K a ∩ ⋃ i ∈ t, K i)ᶜ).homology (n+1)) :=
        Work.Cohomology.relChains_vanishing_of_compact hn (M := M) (K a ∩ ⋃ i ∈ t, K i)
          (hKacpt.inter hLcpt) (n+1) (by omega)
      have hMV := (Work.ThomBordism.excludedMV n M (K a) (⋃ i ∈ t, K i)
        hKa.isClosed hLcpt.isClosed hzero).1
      -- the ball `K a` is killed
      have h₁ : RelHmap M n hKaw (RelHmap M n hWU u) = 0 := by
        have hstep : RelHmap M n hKaw (RelHmap M n hWU u) = RelHmap M n hKaU u :=
          LinearMap.congr_fun (RelHmap_comp' M n hKaw hWU hKaU) u
        have hker : RelHmap M n (Set.singleton_subset_iff.mpr hxa) (RelHmap M n hKaU u) = 0 := by
          rw [← LinearMap.comp_apply, ← RelHmap_point_fac M n hKaU hxa]
          rw [show Set.singleton_subset_iff.mpr (hKaU hxa)
              = Set.singleton_subset_iff.mpr
                (Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a t, hxa⟩)
              from Subsingleton.elim _ _]
          exact hu a (Finset.mem_insert_self a t)
        haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M (K a)ᶜ
            ({x a} : Set M)ᶜ (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxa))) n) :=
          hKa.isIso_restrict hn hxa
        have hinj : Function.Injective (RelHmap M n (Set.singleton_subset_iff.mpr hxa)) :=
          (ModuleCat.mono_iff_injective _).mp inferInstance
        have hzero2 : RelHmap M n hKaU u = 0 := hinj (by rw [hker, map_zero])
        rw [hstep, hzero2]
      -- the rest of the union is killed by the induction hypothesis
      have h₂ : RelHmap M n hLw (RelHmap M n hWU u) = 0 := by
        have hstep : RelHmap M n hLw (RelHmap M n hWU u) = RelHmap M n hLU u :=
          LinearMap.congr_fun (RelHmap_comp' M n hLw hWU hLU) u
        rw [hstep]
        refine ih hKt' hxt' (RelHmap M n hLU u) ?_
        intro i hi
        rw [← LinearMap.comp_apply, ← RelHmap_point_fac M n hLU
          (Set.mem_iUnion₂.mpr ⟨i, hi, hxt' i hi⟩)]
        rw [show Set.singleton_subset_iff.mpr (hLU (Set.mem_iUnion₂.mpr ⟨i, hi, hxt' i hi⟩))
            = Set.singleton_subset_iff.mpr
              (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hxt' i hi⟩)
            from Subsingleton.elim _ _]
        exact hu i (Finset.mem_insert_of_mem hi)
      have huW0 : RelHmap M n hWU u = 0 := hMV (RelHmap M n hWU u) h₁ h₂
      have hback : RelHmap M n hUW (RelHmap M n hWU u) = u := by
        rw [← LinearMap.comp_apply, RelHmap_comp' M n hUW hWU (hUW.trans hWU),
          RelHmap_self M n (hUW.trans hWU), LinearMap.id_apply]
      rw [← hback, huW0, map_zero]
  exact key s hK hx u hu

/-- **Chain lifting for the relative complex of the pair `(M, M∖A)`.**

Every class `β ∈ H_n(M, M∖A)` is represented by a chain `x ∈ C_n(M)` whose boundary lies in
`C_{n-1}(M∖A)`; the class of that chain is `β`. -/
theorem relChain_lift (n : ℕ) (hn : 1 ≤ n) (M : TopCat) (A : Set M) (β : RelH M n A) :
    ∃ (x : (Work.Cohomology.singularChains ℤ M).X n)
      (hx : (Work.Cohomology.singularChains ℤ M).d n (n-1) x
        ∈ LinearMap.range ((Work.Cohomology.inclChains M Aᶜ).f (n-1)).hom)
      (hcyc : (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)).d n (n-1)
        ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f n x) = 0),
      (HomologicalComplex.homologyπ
        (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)) n)
        (Work.Cohomology.cycleOf n _ hcyc) = β := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (CategoryTheory.Limits.cokernel
        (Work.Cohomology.inclChains M Aᶜ)).cycles n,
      (HomologicalComplex.homologyπ
        (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)) n) ζ = β :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance β
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective _).mp
    (Work.Cohomology.epi_cokernel_π_f (Work.Cohomology.inclChains M Aᶜ) n)
    ((HomologicalComplex.iCycles (CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChains M Aᶜ)) n) ζ)
  have hcomm : (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f n
        ≫ (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)).d n (n-1)
      = (Work.Cohomology.singularChains ℤ M).d n (n-1)
        ≫ (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f (n-1) :=
    HomologicalComplex.Hom.comm _ n (n-1)
  have h0 : (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f (n-1)
      ((Work.Cohomology.singularChains ℤ M).d n (n-1) x) = 0 := by
    rw [← CategoryTheory.ConcreteCategory.comp_apply]
    rw [← hcomm]
    rw [CategoryTheory.ConcreteCategory.comp_apply]
    rw [hx]
    exact CategoryTheory.ConcreteCategory.congr_hom
      (HomologicalComplex.iCycles_d (CategoryTheory.Limits.cokernel
        (Work.Cohomology.inclChains M Aᶜ)) n (n-1)) ζ
  have hx' : (Work.Cohomology.singularChains ℤ M).d n (n-1) x
      ∈ LinearMap.range ((Work.Cohomology.inclChains M Aᶜ).f (n-1)).hom :=
    (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains M Aᶜ) (n-1) _).mp h0
  have hcyc : (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)).d n (n-1)
      ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f n x) = 0 := by
    rw [← CategoryTheory.ConcreteCategory.comp_apply, hcomm,
      CategoryTheory.ConcreteCategory.comp_apply, h0]
  refine ⟨x, hx', hcyc, ?_⟩
  have key : Work.Cohomology.cycleOf n
      ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f n x) hcyc = ζ := by
    apply (ModuleCat.mono_iff_injective
      ((HomologicalComplex.iCycles (CategoryTheory.Limits.cokernel
        (Work.Cohomology.inclChains M Aᶜ)) n))).mp inferInstance
    rw [Work.Cohomology.iCycles_cycleOf, hx]
  rw [key, hζ]

/-- **A coordinate ball around a point, inside a given open set.** -/
theorem exists_coordBall_subset {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {U : Set M} (hU : IsOpen U) {a : M} (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) r ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
          Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (r/2) ∩
        (chartAt (EuclideanSpace ℝ (Fin n)) a).source ⊆ U := by
  set e := chartAt (EuclideanSpace ℝ (Fin n)) a with he
  have himg : IsOpen (e '' (e.source ∩ U)) := e.isOpen_image_source_inter hU
  have hea : e a ∈ e '' (e.source ∩ U) := ⟨a, ⟨mem_chart_source _ a, ha⟩, rfl⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp himg (e a) hea
  obtain ⟨ρ', hρ', hρ'sub⟩ :=
    Metric.isOpen_iff.mp e.open_target (e a) (e.map_source (mem_chart_source _ a))
  refine ⟨min ρ ρ', lt_min hρ hρ', ?_, ?_⟩
  · intro y hy
    exact hρ'sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro y hy
    obtain ⟨hyb, hys⟩ := hy
    have hb : e y ∈ Metric.ball (e a) ρ := by
      rw [Metric.mem_ball]
      have h1 : dist (e y) (e a) ≤ min ρ ρ' / 2 := Metric.mem_closedBall.mp hyb
      have h2 : min ρ ρ' / 2 < ρ := by linarith [min_le_left ρ ρ', hρ]
      linarith
    obtain ⟨x, hx, hxe⟩ := hρsub hb
    have hxya : x = y := by
      calc x = e.symm (e x) := (e.left_inv hx.1).symm
        _ = e.symm (e y) := by rw [hxe]
        _ = y := e.left_inv hys
    rw [← hxya]
    exact hx.2

/-- **A finite cover of a compact set by coordinate balls centred in it, avoiding a disjoint
compact set.** -/
theorem exists_ball_cover_avoiding (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {A S : Set M} (hA : IsCompact A)
    (hAS : Disjoint A S) (hSc : IsClosed S) :
    ∃ t : Finset (Set M × M),
      (∀ p ∈ t, IsCoordBall n M p.1) ∧ (∀ p ∈ t, p.2 ∈ p.1) ∧ (∀ p ∈ t, p.2 ∈ A) ∧
      A ⊆ ⋃ p ∈ t, p.1 ∧ Disjoint S (⋃ p ∈ t, p.1) := by
  classical
  have key : ∀ a : M, a ∈ A → ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) r ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
          Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (r/2) ∩
        (chartAt (EuclideanSpace ℝ (Fin n)) a).source ⊆ Sᶜ := by
    intro a ha
    exact exists_coordBall_subset (n := n) (M := M) hSc.isOpen_compl (Set.disjoint_left.mp hAS ha)
  choose! r hr hrt hsub using key
  let L : M → Set M := fun a => (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (r a/2) ∩
    (chartAt (EuclideanSpace ℝ (Fin n)) a).source
  have hL : ∀ a ∈ A, IsCoordBall n M (L a) := by
    intro a ha
    exact ⟨a, r a, hr a ha, hrt a ha, rfl⟩
  have hLmem : ∀ a ∈ A, a ∈ L a := by
    intro a ha
    refine ⟨?_, mem_chart_source _ a⟩
    show (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (r a / 2)
    rw [Metric.mem_closedBall, dist_self]
    linarith [hr a ha]
  have hLsub : ∀ a ∈ A, L a ⊆ Sᶜ := fun a ha => hsub a ha
  -- the open pieces
  let U : M → Set M := fun a => (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (r a/2) ∩
    (chartAt (EuclideanSpace ℝ (Fin n)) a).source
  have hUopen : ∀ a, IsOpen (U a) := by
    intro a
    have h := (chartAt (EuclideanSpace ℝ (Fin n)) a).isOpen_inter_preimage
      (s := Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (r a/2)) Metric.isOpen_ball
    simpa only [U, Set.inter_comm] using h
  have hUmem : ∀ a ∈ A, a ∈ U a := by
    intro a ha
    refine ⟨?_, mem_chart_source _ a⟩
    show (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (r a / 2)
    rw [Metric.mem_ball, dist_self]
    linarith [hr a ha]
  have hUL : ∀ a, U a ⊆ L a := by
    intro a y hy
    exact ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩
  have hmemi : ∀ a ∈ A, a ∈ interior (L a) :=
    fun a ha => interior_maximal (hUL a) (hUopen a) (hUmem a ha)
  have hcov : A ⊆ ⋃ a, (if a ∈ A then interior (L a) else (∅ : Set M)) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨y, by rw [if_pos hy]; exact hmemi y hy⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover
    (fun a => if a ∈ A then interior (L a) else (∅ : Set M))
    (fun a => by split <;> simp [isOpen_interior]) hcov
  refine ⟨(t.filter (fun a => a ∈ A)).image (fun a => (L a, a)), ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hL a (Finset.mem_filter.mp ha).2
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hLmem a (Finset.mem_filter.mp ha).2
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp ha).2
  · intro y hy
    obtain ⟨a, hat, hya⟩ := Set.mem_iUnion₂.mp (ht hy)
    have haA : a ∈ A := by
      by_contra hc
      rw [if_neg hc] at hya
      exact hya
    refine Set.mem_iUnion₂.mpr ⟨(L a, a), Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨hat, haA⟩, rfl⟩, ?_⟩
    rw [if_pos haA] at hya
    exact interior_subset hya
  · rw [Set.disjoint_left]
    intro y hy hyU
    obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hyU
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hLsub a (Finset.mem_filter.mp ha).2 hyp hy

set_option backward.isDefEq.respectTransparency true in
/-- **Naturality of the class of a relative chain under restriction.** -/
theorem chainClass_restrict (n : ℕ) (hn : 1 ≤ n) (M : TopCat) {A B : Set M} (hAB : A ⊆ B)
    (x : (Work.Cohomology.singularChains ℤ M).X n)
    (hcycB : (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Bᶜ)).d n (n-1)
      ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Bᶜ)).f n x) = 0) :
    RelHmap M n hAB ((HomologicalComplex.homologyπ
        (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Bᶜ)) n)
        (Work.Cohomology.cycleOf n _ hcycB))
      = (HomologicalComplex.homologyπ
          (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)) n)
        (HomologicalComplex.cyclesMap (Work.Cohomology.relCokerMap M Bᶜ Aᶜ
          (Set.compl_subset_compl.mpr hAB)) n (Work.Cohomology.cycleOf n _ hcycB)) := by
  have hnat := CategoryTheory.ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (Work.Cohomology.relCokerMap M Bᶜ Aᶜ
      (Set.compl_subset_compl.mpr hAB)) n) (Work.Cohomology.cycleOf n _ hcycB)
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at hnat
  exact hnat

/-- **The class of a relative chain is compatible with restriction**: the cycle of an `(M, M∖B)`
relative chain restricts to the cycle of the same chain for `(M, M∖A)`. -/
theorem cyclesMap_cycleOf (n : ℕ) (hn : 1 ≤ n) (M : TopCat) {A B : Set M} (hAB : A ⊆ B)
    (x : (Work.Cohomology.singularChains ℤ M).X n)
    (hcycB : (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Bᶜ)).d n (n-1)
      ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Bᶜ)).f n x) = 0)
    (hcycA : (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)).d n (n-1)
      ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f n x) = 0) :
    HomologicalComplex.cyclesMap (Work.Cohomology.relCokerMap M Bᶜ Aᶜ
        (Set.compl_subset_compl.mpr hAB)) n
      (Work.Cohomology.cycleOf n ((CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains M Bᶜ)).f n x) hcycB)
      = Work.Cohomology.cycleOf n ((CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains M Aᶜ)).f n x) hcycA := by
  apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles
    (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M Aᶜ)) n)).mp inferInstance
  have hcm := CategoryTheory.ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (Work.Cohomology.relCokerMap M Bᶜ Aᶜ
      (Set.compl_subset_compl.mpr hAB)) n)
    (Work.Cohomology.cycleOf n ((CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains M Bᶜ)).f n x) hcycB)
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcm
  rw [hcm, Work.Cohomology.iCycles_cycleOf, Work.Cohomology.iCycles_cycleOf]
  have hcomp : (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Bᶜ)).f n
      ≫ (Work.Cohomology.relCokerMap M Bᶜ Aᶜ (Set.compl_subset_compl.mpr hAB)).f n
      = (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M Aᶜ)).f n := by
    rw [← HomologicalComplex.comp_f, Work.Cohomology.relCokerMap_comp_π]
  exact CategoryTheory.ConcreteCategory.congr_hom hcomp x

open scoped Simplicial in
/-- **The lift of a relative class to a fine union of coordinate balls.**

For a compact set `A` and `β ∈ H_n(M, M∖A)` there is a finite family of coordinate balls centred at
points of `A`, covering `A`, such that `β` is the restriction of a class on their union. -/
theorem existsLift (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {A : Set M} (hA : IsCompact A) (β : RelH M n A) :
    ∃ (t : Finset (Set M × M)) (hL : ∀ p ∈ t, IsCoordBall n M p.1) (hx : ∀ p ∈ t, p.2 ∈ p.1)
      (hxA : ∀ p ∈ t, p.2 ∈ A) (hcov : A ⊆ ⋃ p ∈ t, p.1),
      ∃ γ : RelH M n (⋃ p ∈ t, p.1), RelHmap M n hcov γ = β := by
  classical
  obtain ⟨x₀, hbdry, hcycA, hclA⟩ := relChain_lift n hn M A β
  obtain ⟨y, hy⟩ := hbdry
  obtain ⟨S, hSA, hScpt, hSr⟩ := Work.Cohomology.exists_compact_support_image (Aᶜ) (n-1) y
  have hSbdry : (Work.Cohomology.singularChains ℤ M).d n (n-1) x₀
      ∈ LinearMap.range ((Work.Cohomology.inclChains M S).f (n-1)).hom := by
    rw [← hy]
    exact hSr
  have hSc : IsClosed S := hScpt.isClosed
  have hAS : Disjoint A S := Set.disjoint_left.mpr (fun a ha hS => hSA hS ha)
  obtain ⟨t, hLt, hxt, hxAt, hcovA, hdisj⟩ := exists_ball_cover_avoiding n hn M hA hAS hSc
  have hSK : S ⊆ (⋃ p ∈ t, p.1)ᶜ := Set.disjoint_left.mp hdisj
  have hbdry' : (Work.Cohomology.singularChains ℤ M).d n (n-1) x₀
      ∈ LinearMap.range ((Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ).f (n-1)).hom :=
    Work.Cohomology.mem_range_inclChains_of_subset hSK hSbdry
  have h0K : (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ)).f (n-1)
      ((Work.Cohomology.singularChains ℤ M).d n (n-1) x₀) = 0 := by
    obtain ⟨z, hz⟩ := hbdry'
    rw [← hz]
    exact Work.Cohomology.cokernel_π_f_apply_eq_zero (n-1) z
  have hcomm : (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ)).f n
        ≫ (CategoryTheory.Limits.cokernel
            (Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ)).d n (n-1)
      = (Work.Cohomology.singularChains ℤ M).d n (n-1)
        ≫ (CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ)).f (n-1) :=
    HomologicalComplex.Hom.comm _ n (n-1)
  have hcycK : (CategoryTheory.Limits.cokernel
        (Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ)).d n (n-1)
      ((CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ)).f n x₀) = 0 := by
    rw [← CategoryTheory.ConcreteCategory.comp_apply, hcomm,
      CategoryTheory.ConcreteCategory.comp_apply, h0K]
  refine ⟨t, hLt, hxt, hxAt, hcovA, (HomologicalComplex.homologyπ
    (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains M (⋃ p ∈ t, p.1)ᶜ)) n)
    (Work.Cohomology.cycleOf n _ hcycK), ?_⟩
  rw [chainClass_restrict n hn M hcovA x₀ hcycK,
    cyclesMap_cycleOf n hn M hcovA x₀ hcycK hcycA, hclA]

/-- **Uniqueness of a relative class detected at all points of a compact set.** -/
theorem compactZero (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {A : Set M} (hA : IsCompact A) (β : RelH M n A)
    (hβ : ∀ (x : M) (hx : x ∈ A), RelHmap M n (Set.singleton_subset_iff.mpr hx) β = 0) :
    β = 0 := by
  classical
  obtain ⟨t, hL, hx, hxA, hcov, γ, hγ⟩ := existsLift n hn M hA β
  have hγzero : ∀ (p : Set M × M) (hp : p ∈ t), RelHmap M n (Set.singleton_subset_iff.mpr
      (Set.mem_iUnion₂.mpr ⟨p, hp, hx p hp⟩)) γ = 0 := by
    intro p hp
    have h1 : RelHmap M n (Set.singleton_subset_iff.mpr (hcov (hxA p hp))) γ
        = RelHmap M n (Set.singleton_subset_iff.mpr (hxA p hp)) (RelHmap M n hcov γ) := by
      rw [← LinearMap.comp_apply, ← RelHmap_point_fac M n hcov (hxA p hp)]
    rw [show (Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr ⟨p, hp, hx p hp⟩))
        = Set.singleton_subset_iff.mpr (hcov (hxA p hp)) from
        Subsingleton.elim (Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr ⟨p, hp, hx p hp⟩))
          (Set.singleton_subset_iff.mpr (hcov (hxA p hp))),
      h1, hγ]
    exact hβ (p.2) (hxA p hp)
  have hγ0 : γ = 0 :=
    unionZero n hn M t (fun p : Set M × M => p.1) (fun p : Set M × M => p.2)
      (fun p hp => hL p hp) (fun p hp => hx p hp) γ hγzero
  rw [← hγ, hγ0, map_zero]


end

end Work.ThomBordism
