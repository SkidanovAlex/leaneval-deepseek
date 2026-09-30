import Mathlib
import Submission.Work.Cohomology.relChains_compl_union_free
import Submission.Work.Cohomology.pd_plumbing

/-!
# The two-set Mayer--Vietoris map on relative homology

For open `S, T ⊆ M` with `S ∪ T = M`, the natural map

`C_*(M, S ∩ T) ⟶ C_*(M, S) ⊕ C_*(M, T)`

given by the two enlargement maps is a quasi-isomorphism in every positive degree: this is the
first map of the Mayer--Vietoris sequence of the two-set cover `{S, T}`.

The proof isolates the two general inputs:

* `cokernelBiprodMapIsoChar` (a general abelian-category fact): the cokernel of a biproduct of
  maps is the biproduct of the cokernels, with its projection given explicitly.
* `isIso_homologyMap_cokernel_map`: for a morphism of short exact complexes with monomorphic
  components, the first map of the cokernel short exact sequence is an isomorphism on homology in
  degree `k` whenever the third cokernel is acyclic in degrees `k` and `k+1`.

The identification of the explicit map with the Mayer--Vietoris map is then a diagram chase.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Work.Cohomology

noncomputable section

/-! ## General abelian-category helpers -/

/-- The explicit isomorphism `coker (f ⊞ g) ≅ coker f ⊞ coker g`, together with the
characterisation of its inverse on the projections. -/
theorem cokernelBiprodMapIsoChar {C : Type*} [Category C] [Abelian C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') :
    ∃ (e : cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g),
      cokernel.π (biprod.map f g) ≫ e.hom = biprod.map (cokernel.π f) (cokernel.π g) := by
  let ψ := biprod.map f g
  let φ := biprod.map (cokernel.π f) (cokernel.π g)
  have hw : ψ ≫ φ = 0 := by
    dsimp only [ψ, φ]
    apply biprod.hom_ext' <;> simp
  have hcolim : IsColimit (CokernelCofork.ofπ φ hw) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro W k hk
    refine ⟨biprod.desc
      (cokernel.desc f (biprod.inl ≫ k) ?_)
      (cokernel.desc g (biprod.inr ≫ k) ?_), ?_⟩
    · rw [← Category.assoc, ← biprod.inl_map, Category.assoc, hk, comp_zero]
    · rw [← Category.assoc, ← biprod.inr_map, Category.assoc, hk, comp_zero]
    · apply biprod.hom_ext' <;> simp [φ]
  refine ⟨IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel ψ) hcolim, ?_⟩
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel ψ) hcolim
    WalkingParallelPair.one
  simpa [ψ, φ] using h

/-- The snake lemma, in the form in which the *explicit* first map of the cokernel short exact
sequence is an isomorphism on homology.

If `v : S₁ ⟶ S₂` is a morphism of short exact sequences whose three components are
monomorphisms, and the third cokernel `cokernel v.τ₃` is acyclic in degrees `k` and `k+1`, then
the map `cokernel v.τ₁ ⟶ cokernel v.τ₂` induced by `v` is an isomorphism in homology degree `k`.
-/
private theorem isIso_homologyMap_cokernel_map
    {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (v : S₁ ⟶ S₂)
    (hv₁ : Mono v.τ₁) (hv₂ : Mono v.τ₂) (hv₃ : Mono v.τ₃) (k : ℕ)
    (ha₁ : IsZero ((cokernel v.τ₃).homology (k+1)))
    (ha₂ : IsZero ((cokernel v.τ₃).homology k)) :
    IsIso (HomologicalComplex.homologyMap (cokernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂) k) := by
  let f : cokernel v.τ₁ ⟶ cokernel v.τ₂ := cokernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂
  let g : cokernel v.τ₂ ⟶ cokernel v.τ₃ := cokernel.map v.τ₂ v.τ₃ S₁.g S₂.g v.comm₂₃
  have hπf : cokernel.π v.τ₁ ≫ f = S₂.f ≫ cokernel.π v.τ₂ := by
    simp only [f, cokernel.map, cokernel.π_desc]
  have hπg : cokernel.π v.τ₂ ≫ g = S₂.g ≫ cokernel.π v.τ₃ := by
    simp only [g, cokernel.map, cokernel.π_desc]
  have hfg : f ≫ g = 0 := by
    rw [← cancel_epi (cokernel.π v.τ₁), comp_zero, ← Category.assoc, hπf, Category.assoc, hπg,
      ← Category.assoc, S₂.zero, zero_comp]
  let C₀ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := ShortComplex.mk f g hfg
  let φ : S₂ ⟶ C₀ :=
    ShortComplex.homMk (cokernel.π v.τ₁) (cokernel.π v.τ₂) (cokernel.π v.τ₃) hπf hπg
  have w₁₃ : v ≫ φ = 0 := by
    ext <;> simp [ShortComplex.comp_τ₁, φ, cokernel.condition]
  let sn : ShortComplex.SnakeInput (ChainComplex (ModuleCat ℤ) ℕ) :=
    { L₀ := ShortComplex.mk (0 : (0 : ChainComplex (ModuleCat ℤ) ℕ) ⟶ 0) 0 (by simp)
      L₁ := S₁
      L₂ := S₂
      L₃ := C₀
      v₀₁ := 0
      v₁₂ := v
      v₂₃ := φ
      w₀₂ := by simp
      w₁₃ := w₁₃
      h₀ := by
        apply ShortComplex.isLimitOfIsLimitπ
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₁)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₂)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernel.isLimitConeZeroCone v.τ₃)
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₁)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₂)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel v.τ₃)
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have hex : C₀.Exact := sn.L₃_exact
  have hg : Epi sn.L₂.g := h₂.epi_g
  have hepi : Epi g := sn.epi_L₃_g
  have hδ : sn.δ = 0 := IsZero.eq_zero_of_src (X := sn.L₀.X₃)
    (isZero_zero (ChainComplex (ModuleCat ℤ) ℕ)) sn.δ
  have hmono : Mono f := ShortComplex.Exact.mono_g sn.L₂'_exact hδ
  exact isIso_homologyMap_of_acyclic (ShortComplex.ShortExact.mk' hex hmono hepi) k ha₁ ha₂

section

variable {M : TopCat}

/-- The diagonal `C_*(M) ⟶ C_*(M) ⊞ C_*(M)` followed by `p ⊞ q` is `p ⊞ q` on the diagonal. -/
private lemma complDiag_map_eq_lift {A B : Set M}
    (p : singularChains ℤ M ⟶ cokernel (inclChains M A))
    (q : singularChains ℤ M ⟶ cokernel (inclChains M B)) :
    complDiag M ≫ biprod.map p q = biprod.lift p q := by
  apply biprod.hom_ext <;> simp [complDiag]

/-- Precomposition commutes with `biprod.lift`. -/
private lemma comp_biprod_lift {C : Type*} [Category C] [HasZeroMorphisms C]
    {X W Y Z : C} [HasBinaryBiproduct Y Z]
    (c : X ⟶ W) (a : W ⟶ Y) (b : W ⟶ Z) :
    c ≫ biprod.lift a b = biprod.lift (c ≫ a) (c ≫ b) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

end

/-! ## The main statement -/

theorem lk_twoSet_homologyMap_isIso {N : ℕ} (hN : 1 ≤ N) {M : TopCat} (S T : Set M)
    (hS : IsOpen S) (hT : IsOpen T) (hcov : S ∪ T = Set.univ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.biprod.lift
        (Work.Cohomology.relCokerMap M (S ∩ T) S Set.inter_subset_left)
        (Work.Cohomology.relCokerMap M (S ∩ T) T Set.inter_subset_right)) N) := by
  haveI : Mono (inclChains M S) := mono_chainMap_subtypeIncl M S
  haveI : Mono (inclChains M T) := mono_chainMap_subtypeIncl M T
  haveI hmono1 : Mono ((mvToTrivial S T).τ₁) := mono_chainMap_subtypeIncl M (S ∩ T)
  haveI hmono2 : Mono ((mvToTrivial S T).τ₂) := biprod.map_mono _ _
  haveI hmono3 : Mono (smallToSing S T) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr (smallToSing_f_injective S T n)
  have hacyc : ∀ k, 1 ≤ k → IsZero ((cokernel (smallToSing S T)).homology k) :=
    isZero_homology_coker_of_isIso (smallToSing S T)
      (fun n => smallChains_homology_iso S T hS hT hcov n)
  let fC : cokernel (inclChains M (S ∩ T)) ⟶
      cokernel (biprod.map (inclChains M S) (inclChains M T)) :=
    cokernel.map (inclChains M (S ∩ T)) (biprod.map (inclChains M S) (inclChains M T))
      (mvLeft S T) (complDiag M) (mvToTrivial_comm₁₂ S T)
  haveI hiso : IsIso (HomologicalComplex.homologyMap fC N) :=
    isIso_homologyMap_cokernel_map (mvShort_shortExact S T) (trivialShort_shortExact M)
      (mvToTrivial S T) hmono1 hmono2 hmono3 N (hacyc (N+1) (by omega)) (hacyc N hN)
  have hπfC : cokernel.π (inclChains M (S ∩ T)) ≫ fC
      = complDiag M ≫ cokernel.π (biprod.map (inclChains M S) (inclChains M T)) := by
    simp only [fC, cokernel.map, cokernel.π_desc]
  obtain ⟨e, he⟩ := cokernelBiprodMapIsoChar (inclChains M S) (inclChains M T)
  have hJ : biprod.lift (relCokerMap M (S ∩ T) S Set.inter_subset_left)
        (relCokerMap M (S ∩ T) T Set.inter_subset_right) = fC ≫ e.hom := by
    apply (cancel_epi (cokernel.π (inclChains M (S ∩ T)))).mp
    have hL : cokernel.π (inclChains M (S ∩ T)) ≫ biprod.lift
          (relCokerMap M (S ∩ T) S Set.inter_subset_left)
          (relCokerMap M (S ∩ T) T Set.inter_subset_right)
        = biprod.lift (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T)) := by
      simp only [comp_biprod_lift, relCokerMap_comp_π]
    have hR : cokernel.π (inclChains M (S ∩ T)) ≫ (fC ≫ e.hom)
        = biprod.lift (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T)) := by
      rw [← Category.assoc, hπfC, Category.assoc, he, complDiag_map_eq_lift]
    rw [hL, hR]
  have hgoal : HomologicalComplex.homologyMap
        (biprod.lift (relCokerMap M (S ∩ T) S Set.inter_subset_left)
          (relCokerMap M (S ∩ T) T Set.inter_subset_right)) N
      = HomologicalComplex.homologyMap fC N ≫ HomologicalComplex.homologyMap e.hom N := by
    rw [← HomologicalComplex.homologyMap_comp, ← hJ]
  haveI hisoe : IsIso (HomologicalComplex.homologyMap e.hom N) :=
    (HomologicalComplex.homologyMapIso e N).isIso_hom
  rw [hgoal]
  exact inferInstance

end

end Work.Cohomology
