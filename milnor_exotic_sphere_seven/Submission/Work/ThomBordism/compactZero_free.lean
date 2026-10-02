import Mathlib
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.ThomBordism.localGenAux
import Submission.Work.Orient.Port.Hatcher
import Submission.Work.ThomBordism.isCoordBall_restrict_iso_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.compactZero_free`

Hatcher's Lemma 3.27(a) uniqueness for a compact set, with the spurious `[CompactSpace M]`
hypothesis of `Work.ThomBordism.compactZero` removed.

The two ingredients of `compactZero` are adapted here as well:

* `unionZero_free` — the finite-union case; the only place compactness of `M` was used inside
  `unionZero` was the local restriction isomorphism `IsCoordBall.isIso_restrict`, which is
  re-proved without compactness in `Work.ThomBordism.isCoordBall_restrict_iso_free`.
* `existsLift_free` — the lift of a relative class to a fine union of coordinate balls; its proof
  never used the compactness of `M` (only the compactness of `A`, which is a hypothesis).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

variable {n : ℕ}

/-- **Uniqueness for a finite union of coordinate balls** (Hatcher 3.27(a), finite-union case):
a class of `H_n(M, M∖⋃ K_i)` which dies at one point `x i ∈ K i` of each ball is zero. -/
theorem unionZero_free (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [T2Space M]
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
          isCoordBall_restrict_iso_free (n := n) (M := M) hn hKa hxa
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

open scoped Simplicial in
/-- **The lift of a relative class to a fine union of coordinate balls.**

For a compact set `A` and `β ∈ H_n(M, M∖A)` there is a finite family of coordinate balls centred at
points of `A`, covering `A`, such that `β` is the restriction of a class on their union. -/
theorem existsLift_free (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [T2Space M]
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
theorem compactZero_noCompact (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {A : Set M} (hA : IsCompact A) (β : RelH M n A)
    (hβ : ∀ (x : M) (hx : x ∈ A), RelHmap M n (Set.singleton_subset_iff.mpr hx) β = 0) :
    β = 0 := by
  classical
  obtain ⟨t, hL, hx, hxA, hcov, γ, hγ⟩ := existsLift_free n hn M hA β
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
    unionZero_free n hn M t (fun p : Set M × M => p.1) (fun p : Set M × M => p.2)
      (fun p hp => hL p hp) (fun p hp => hx p hp) γ hγzero
  rw [← hγ, hγ0, map_zero]


/-- **Hatcher 3.27(a), uniqueness for a compact set, without compactness of the ambient space.** -/
theorem compactZero_free {n : ℕ} (hn : 1 ≤ n) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {A : Set M} (hA : IsCompact A)
    (β : Work.ThomBordism.RelH M n A)
    (hβ : ∀ (x : M) (hx : x ∈ A), Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hx) β = 0) :
    β = 0 :=
  compactZero_noCompact n hn M hA β hβ

end

end Work.ThomBordism
