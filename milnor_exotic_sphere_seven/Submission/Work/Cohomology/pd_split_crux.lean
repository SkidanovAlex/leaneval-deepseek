import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_relsub_aux
import Submission.Work.Cohomology.pd_hatcher_cycles_inter
import Submission.Work.Cohomology.pd_goodD_rep
import Submission.Work.Cohomology.pdABdelta_natural
import Submission.Work.Cohomology.pdABInclRel_comp_pdABEnlarge
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pd_localFundClass_of_cycle
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.pd_crux_weak
import Submission.Work.Cohomology.pd_mvdelta_apply
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.chainRetract_mem_range_inclChains
import Submission.Work.Cohomology.mv_boundary_d_of_small_cycle
import Submission.Work.Cohomology.pdHom_iUnion_kill
import Submission.Work.Cohomology.pd_union_extend
import Submission.Work.Cohomology.pd_hatcher_inter_wk2
import Submission.Work.Cohomology.pd_inter_rep
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.pd_evalEnlarge_zero
import Submission.Work.Cohomology.pd_split_crux_rest

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Bridges between `cochainDiff` and the differential of the singular cochain complex -/

/-- The differential of the singular cochain complex is the `cochainDiff`. -/
theorem pd_singularD_eq_cochainDiff (X : TopCat) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (ConcreteCategory.hom ((singularCochainComplex ℤ X).d n (n+1))) φ
      = cochainDiff ℤ (TopCat.toSSet.obj X) φ := by
  simp only [singularCochainComplex_eq, SSetCochainComplex_d]
  exact cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) n φ

/-- **Vanishing of a cohomology class, cochain version.**  For a cochain complex `C` of
`ℤ`-modules and a cycle `z ∈ C.cycles (k+1)`, the class of `z` is zero if and only if `z` is a
coboundary: `z = d w` for some `(k)`-cochain `w`. -/
theorem pd_cochain_homologyπ_eq_zero_iff_d {C : CochainComplex (ModuleCat ℤ) ℕ}
    [∀ i, C.HasHomology i] (k : ℕ) (z : C.cycles (k+1)) :
    C.homologyπ (k+1) z = 0 ↔ ∃ w : C.X k, C.d k (k+1) w = C.iCycles (k+1) z := by
  have hrel : (ComplexShape.up ℕ).Rel k (k+1) := ComplexShape.up_mk k (k+1) rfl
  have hprev : (ComplexShape.up ℕ).prev (k+1) = k := ComplexShape.prev_eq' _ hrel
  have key := pdHom_homologyπ_eq_zero_iff_sc (S := C.sc (k+1)) (z := z)
  have hR : (∃ w : (C.sc (k+1)).X₁, (C.sc (k+1)).f.hom w = (C.sc (k+1)).iCycles z)
      ↔ ∃ w : C.X k, C.d k (k+1) w = C.iCycles (k+1) z := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨(C.XIsoOfEq hprev.symm).inv w, ?_⟩
      rw [← ModuleCat.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
      exact hw
    · rintro ⟨w, hw⟩
      refine ⟨(C.XIsoOfEq hprev).inv w, ?_⟩
      change C.d ((ComplexShape.up ℕ).prev (k+1)) (k+1)
        ((C.XIsoOfEq hprev).inv w) = C.iCycles (k+1) z
      rw [← ModuleCat.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
      exact hw
  exact (Iff.of_eq (show ((C.sc (k+1)).homologyπ z = 0) = (C.homologyπ (k+1) z = 0)
    from rfl)).symm.trans (key.trans hR)

/-! ## Part 0: bookkeeping lemmas for the crux -/

/-- `castChainLM` does not depend on the proof of the equality of degrees. -/
theorem pd_castChainLM_congr {X : SSet} {a b : ℕ} (h h' : a = b)
    (x : (X.chainComplex (ModuleCat.of ℤ ℤ)).X a) :
    castChainLM (X := X) h x = castChainLM (X := X) h' x := by
  simp only [castChainLM_apply]

/-- Degree casts do not depend on the proof of the equality. -/
theorem pd_cast_proof_irrel {α : Sort*} {P : α → Type*} {a b : α} (h h' : a = b) (x : P a) :
    (h ▸ x : P b) = (h' ▸ x : P b) := by
  rw [Subsingleton.elim h h']

/-- The `XIsoOfEq`-cast of a chain is the `▸`-cast. -/
theorem pd_XIsoOfEq_hom_eq_cast {C : ChainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (x : C.X a) : ConcreteCategory.hom (C.XIsoOfEq h).hom x = (h ▸ x : C.X b) := by
  cases h; rfl

/-- The transport of a membership in a set along an equality of sets, in the form needed by the
pair maps. -/
theorem pd_mem_of_eq {X : TopCat} {S S' : Set X} (h : S = S') :
    ∀ x ∈ S, (𝟙 X : X ⟶ X) x ∈ S' := fun x hx => by
  simpa using (show x ∈ S' from h ▸ hx)

/-- The degree cast of chains commutes with a chain map of simplicial sets. -/
theorem pd_sset_chainMap_castChainLM {X Y : SSet} (f : X ⟶ Y) {a b : ℕ} (h : a = b)
    (x : (X.chainComplex (ModuleCat.of ℤ ℤ)).X a) :
    (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f b (castChainLM (X := X) h x)
      = castChainLM (X := Y) h ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f a x) := by
  rw [castChainLM_apply, castChainLM_apply]
  cases h
  rfl

/-- The underlying chain of the degree cast of a cycle. -/
theorem pd_iCycles_cast_cycle {C : ChainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (γ : C.cycles a) :
    C.iCycles b (h ▸ γ) = ConcreteCategory.hom (C.XIsoOfEq h).hom (C.iCycles a γ) := by
  cases h
  rfl

/-- The homology class of the degree cast of a cycle. -/
theorem pd_homologyπ_cast_cycle {C : ChainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (γ : C.cycles a) :
    C.homologyπ b (h ▸ γ) = h ▸ (C.homologyπ a γ) := by
  cases h
  rfl

/-- The canonical map `W ∩ S ⟶ S` is a left inverse of the canonical map `S ⟶ W ∩ S`. -/
theorem pdTrMap_comp_pdTrInv' {M : TopCat} {S W : Set M} (h : S ⊆ W) :
    pdTrMap h ≫ pdTrInv h = 𝟙 (TopCat.of S) := by
  ext x; rfl

/-- **Injectivity of the inclusion of chains** `C_*(W) → C_*(M)` for `W ⊆ M`. -/
theorem pd_inclChains_injective {M : TopCat} (W : Set M) (n : ℕ) :
    Function.Injective (ConcreteCategory.hom ((inclChains M W).f n)) := by
  intro x y hxy
  exact injective_chainComplexMap_subtypeIncl M W n hxy

/-- The inclusion `C_*(S) → C_*(W)` for `S ⊆ W` is injective. -/
theorem pd_inclChainsSub_injective {M : TopCat} {S W : Set M} (h : S ⊆ W) (n : ℕ) :
    Function.Injective (ConcreteCategory.hom ((inclChainsSub M S W h).f n)) := by
  have hcomp : chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)
      ≫ chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)
      = 𝟙 (singularChains ℤ (TopCat.of S)) := by
    rw [chainMap_compPD, pdTrMap_comp_pdTrInv' h, chainMap_id']
  intro x y hxy
  have hxy1 : ConcreteCategory.hom ((chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of W)
      (subtypeIncl (TopCat.of W) (pdTr W S))).f n)
      (ConcreteCategory.hom ((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S))
        (pdTrMap h)).f n) x)
      = ConcreteCategory.hom ((chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of W)
      (subtypeIncl (TopCat.of W) (pdTr W S))).f n)
      (ConcreteCategory.hom ((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S))
        (pdTrMap h)).f n) y) := by
    rw [inclChainsSub_eq_pdTrMap] at hxy
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using hxy
  have h2 := injective_chainComplexMap_subtypeIncl (TopCat.of W) (pdTr W S) n hxy1
  have hleft : ∀ z, ConcreteCategory.hom ((chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S)
      (pdTrInv h)).f n) (ConcreteCategory.hom ((chainMap ℤ (TopCat.of S)
      (TopCat.of (pdTr W S)) (pdTrMap h)).f n) z) = z := by
    intro z
    have hh := congrArg (fun (g : singularChains ℤ (TopCat.of S) ⟶
      singularChains ℤ (TopCat.of S)) => ConcreteCategory.hom (g.f n) z) hcomp
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply] using hh
  rw [← hleft x, h2, hleft y]

/-- **The canonical isomorphism between the relative cochain complexes of two equal subsets.** -/
def pdRelComplexCongr {X : TopCat} {S S' : Set X} (h : S = S') :
    relComplex ℤ X S ≅ relComplex ℤ X S' where
  hom := relComplexMap ℤ S' S (𝟙 X) (pd_mem_of_eq h.symm)
  inv := relComplexMap ℤ S S' (𝟙 X) (pd_mem_of_eq h)
  hom_inv_id := by
    have h1 := capRel_relComplexMap_comp (R := ℤ) (X₀ := X) (X₁ := X) (X₂ := X) S S' S
      (𝟙 X) (𝟙 X) (pd_mem_of_eq h) (pd_mem_of_eq h.symm)
    simp only [Category.id_comp] at h1
    rw [← h1]
    exact capRel_relComplexMap_id ℤ S _
  inv_hom_id := by
    have h1 := capRel_relComplexMap_comp (R := ℤ) (X₀ := X) (X₁ := X) (X₂ := X) S' S S'
      (𝟙 X) (𝟙 X) (pd_mem_of_eq h.symm) (pd_mem_of_eq h)
    simp only [Category.id_comp] at h1
    rw [← h1]
    exact capRel_relComplexMap_id ℤ S' _

/-- The underlying cochain of the canonical isomorphism of equal subsets. -/
theorem pdRelComplexCongr_coe {X : TopCat} {S S' : Set X} (h : S = S') (n : ℕ)
    (x : (relComplex ℤ X S).X n) :
    (((pdRelComplexCongr h).hom.f n).hom x : relKern ℤ X S' n).1 = x.1 := by
  rw [pdRelComplexCongr, relComplexMap_f, ModuleCat.hom_ofHom]
  exact PDABClean.relMapLM_id_coe (X := X) (A₁ := S') (A₂ := S) (pd_mem_of_eq h.symm) n x

/-- Two morphisms of relative cochain complexes with the same source and target are equal as soon
as they agree on the underlying cochains. -/
theorem pdRelComplex_hom_ext {X : TopCat} {S T : Set X}
    {f g : relComplex ℤ X S ⟶ relComplex ℤ X T}
    (h : ∀ (n : ℕ) (x : (relComplex ℤ X S).X n),
      ((ModuleCat.Hom.hom (f.f n)) x).1 = ((ModuleCat.Hom.hom (g.f n)) x).1) : f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subtype.ext (h n x)

/-- The underlying cochain of a `relComplexMap` of the identity is the cochain itself. -/
theorem pd_relComplexMap_id_coe {X : TopCat} {S T : Set X} (h : ∀ x ∈ T, (𝟙 X : X ⟶ X) x ∈ S)
    (n : ℕ) (x : (relComplex ℤ X S).X n) :
    (((relComplexMap ℤ T S (𝟙 X) h).f n).hom x : relKern ℤ X T n).1 = x.1 := by
  rw [relComplexMap_f, ModuleCat.hom_ofHom]
  exact PDABClean.relMapLM_id_coe (X := X) (A₁ := T) (A₂ := S) h n x


/-- The degree cast of the underlying chain of a cast of a chain by `XIsoOfEq`. -/
theorem pd_castChainLM_eq_XIsoOfEq {X : SSet} {a b : ℕ} (h : a = b)
    (x : (X.chainComplex (ModuleCat.of ℤ ℤ)).X a) :
    castChainLM (X := X) h x
      = ConcreteCategory.hom ((X.chainComplex (ModuleCat.of ℤ ℤ)).XIsoOfEq h).hom x := by
  rw [castChainLM_apply]
  cases h
  rfl

/-- `▸` commutes with a chain map. -/
theorem pd_chainMap_cast {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) {a b : ℕ}
    (h : a = b) (x : C.X a) : (φ.f b) (h ▸ x) = h ▸ (φ.f a x) := by
  cases h; rfl

/-- `XIsoOfEq` commutes with a chain map, elementwise. -/
theorem pd_XIsoOfEq_nat {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) {a b : ℕ}
    (h : a = b) (x : C.X a) :
    ConcreteCategory.hom (D.XIsoOfEq h).hom (ConcreteCategory.hom (φ.f a) x)
      = ConcreteCategory.hom (φ.f b) (ConcreteCategory.hom (C.XIsoOfEq h).hom x) := by
  have hh := congrArg (fun (g : C.X a ⟶ D.X b) => ConcreteCategory.hom g x)
    (HomologicalComplex.XIsoOfEq_hom_naturality φ h)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- If the duality map `D_W^K` kills the class of the relative cocycle `z`, and `γ` is a relative
cycle of `W` modulo `W∖K` representing the local fundamental class, then the cap product of the
cochain of `z` with any lift `ξ` of `γ` is a boundary in the chains of `W`. -/
theorem pd_cap_chain_boundary {M : TopCat} [T2Space M] {K W : Set M}
    (hW : IsOpen W) (hKW : K ⊆ W) (hKc : IsCompact K) {k m : ℕ}
    (c : (singularChains ℤ M).homology (k + m))
    (z : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).cycles k)
    (γ : (relChains (TopCat.of W) (pdRelSub W K)).cycles (k + m))
    (hγ : (relChains (TopCat.of W) (pdRelSub W K)).homologyπ (k + m) γ
        = localFundClass (k + m) c W hW K hKW hKc)
    (ξ : (singularChains ℤ (TopCat.of W)).X (k + m))
    (hξ : (relChains (TopCat.of W) (pdRelSub W K)).iCycles (k + m) γ
      = ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f (k + m)).hom ξ)
    (hx : goodD (k + m) c W hW K hKW hKc k m rfl
            ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homologyπ k z) = 0) :
    ∃ β : (singularChains ℤ (TopCat.of W)).X (m + 1),
      (singularChains ℤ (TopCat.of W)).d (m + 1) m β
        = cap ℤ (TopCat.toSSet.obj (TopCat.of W))
            (((relComplex ℤ (TopCat.of W) (pdRelSub W K)).iCycles k z).1) m ξ := by
  have hgood : goodD (k + m) c W hW K hKW hKc k m rfl
      ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homologyπ k z)
      = (singularChains ℤ (TopCat.of W)).homologyπ m
          (relCapPairZ (TopCat.of W) (pdRelSub W K) k m z γ) :=
    goodD_homologyπ c W hW K hKW hKc k m rfl z γ hγ ξ hξ
  rw [hx] at hgood
  have hcyc : (singularChains ℤ (TopCat.of W)).iCycles m
      (relCapPairZ (TopCat.of W) (pdRelSub W K) k m z γ)
      = cap ℤ (TopCat.toSSet.obj (TopCat.of W))
          (((relComplex ℤ (TopCat.of W) (pdRelSub W K)).iCycles k z).1) m ξ :=
    @relCapPairZ_iCycles_apply (TopCat.of W) (pdRelSub W K) k m z γ ξ hξ
  have hzero : (singularChains ℤ (TopCat.of W)).homologyπ m
      (relCapPairZ (TopCat.of W) (pdRelSub W K) k m z γ) = 0 := hgood.symm
  obtain ⟨β, hβ⟩ := (pdHom_homologyπ_eq_zero_iff_d m
    (relCapPairZ (TopCat.of W) (pdRelSub W K) k m z γ)).mp hzero
  refine ⟨β, ?_⟩
  rw [hβ, hcyc]

/-- **The chain-level crux identity, with the cycle condition weakened to "a cycle modulo the
`Kᶜ ∩ Lᶜ`-supported chains".** -/
theorem pd_crux_identity_weak {X : TopCat} {K L : Set X} {k mj : ℕ}
    (α₁ α₂ α₃ : (singularChains ℤ X).X (k + (mj + 1)))
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj X) k)
    (hφA : φA ∈ relKern ℤ X Kᶜ k) (hφB : φB ∈ relKern ℤ X Lᶜ k)
    (hlift : φ = φA - φB)
    (hL : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
      ∈ LinearMap.range (((inclChains X Lᶜ).f (k + mj)).hom))
    (hK : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃
      ∈ LinearMap.range (((inclChains X Kᶜ).f (k + mj)).hom))
    (hd : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
      ∈ LinearMap.range (((inclChains X (Kᶜ ∩ Lᶜ)).f (k + mj)).hom))
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0) :
    (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁
          + cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ (k + 1) • cap ℤ (TopCat.toSSet.obj X)
          (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂) := by
  obtain ⟨ξ, hξ⟩ := hd
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  -- the cochain `φ` vanishes on the chains supported in `Kᶜ ∩ Lᶜ`
  have hφKL : φ ∈ relKern ℤ X (Kᶜ ∩ Lᶜ) k := by
    rw [hlift]
    exact Submodule.sub_mem _ (relKern_mono (Set.inter_subset_left) hφA)
      (relKern_mono (Set.inter_subset_right) hφB)
  have hφBKL : φB ∈ relKern ℤ X (Kᶜ ∩ Lᶜ) k :=
    relKern_mono Set.inter_subset_right hφB
  -- the vanishing of the three "error" terms
  have hzeroL : cap ℤ (TopCat.toSSet.obj X) φB mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact cap_inclChains_eq_zero X Lᶜ φB hφB mj e'
  have hzeroK : cap ℤ (TopCat.toSSet.obj X) φA mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact cap_inclChains_eq_zero X Kᶜ φA hφA mj f'
  have hzeroξ : cap ℤ (TopCat.toSSet.obj X) φ mj ((inclChains X (Kᶜ ∩ Lᶜ)).f (k + mj) ξ) = 0 :=
    cap_inclChains_eq_zero X (Kᶜ ∩ Lᶜ) φ hφKL mj ξ
  have hzeroξB : cap ℤ (TopCat.toSSet.obj X) φB mj ((inclChains X (Kᶜ ∩ Lᶜ)).f (k + mj) ξ) = 0 :=
    cap_inclChains_eq_zero X (Kᶜ ∩ Lᶜ) φB hφBKL mj ξ
  -- the relation `d α₁ + d α₂ + d α₃ = inclChains ξ`
  have hrel : (inclChains X (Kᶜ ∩ Lᶜ)).f (k + mj) ξ
      = (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ := by
    rw [hξ, map_add, map_add]
  -- the key identity
  have hP : cap ℤ (TopCat.toSSet.obj X) φ mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) := by
    refine eq_neg_of_add_eq_zero_left ?_
    have hdα : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
        = (inclChains X (Kᶜ ∩ Lᶜ)).f (k + mj) ξ
          - (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
          - (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ := by
      rw [hrel]; abel
    have hsub : cap ℤ (TopCat.toSSet.obj X) φ mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
        = cap ℤ (TopCat.toSSet.obj X) φA mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj X) φB mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) := by
      rw [hlift, cap_sub_apply]
    have hsub₃ : cap ℤ (TopCat.toSSet.obj X) φ mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃)
        = - cap ℤ (TopCat.toSSet.obj X) φB mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) := by
      rw [hlift, cap_sub_apply, hzeroK, zero_sub]
    -- the `φB`-terms cancel
    have hBsum : cap ℤ (TopCat.toSSet.obj X) φB mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
        + cap ℤ (TopCat.toSSet.obj X) φB mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
      have h23 : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
          + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃
          = (inclChains X (Kᶜ ∩ Lᶜ)).f (k + mj) ξ
            - (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁ := by
        rw [hrel]; abel
      rw [← map_add, h23, map_sub, hzeroξB, hzeroL, sub_zero]
    rw [hdα, map_sub, map_sub, hsub, hsub₃, hzeroξ]
    rw [zero_sub, sub_neg_eq_add, ← hBsum]
    abel
  -- the boundary formula for the cocycle `φ` applied to `α₁`
  have hA : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      = (-1 : ℤ) ^ k • cap ℤ (TopCat.toSSet.obj X) φ mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) := by
    have h := cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) φ α₁
    rw [hφd, cap_zero, LinearMap.zero_apply, sub_zero] at h
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj X)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj X) φ mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)))
  -- the boundary formula for `φA` applied to `α₂`
  have hB : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ k • (cap ℤ (TopCat.toSSet.obj X) φA mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) φA α₂
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj X)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj X) φA mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)))
  -- the arithmetic combination
  have key : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)
      = - (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
          (cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂) := by
    rw [hA, hP, hB]
    rw [zsmul_neg]
    rw [show (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k by rw [pow_succ]; ring, neg_zsmul, zsmul_sub]
    abel
  rw [map_add]
  have hK2 := key
  rw [sub_eq_iff_eq_add] at hK2
  rw [hK2]
  abel

/-- The `U ∩ V`-supported refinement of the crux identity, with the cycle condition weakened to
"a cycle modulo the `Kᶜ ∩ Lᶜ`-supported chains" and the support of `α₃` replaced by the support of
its cap with `φ`. -/
theorem pd_union_crux_zero_weak {X : TopCat} {U V K L : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {k mj : ℕ}
    (α₁ α₂ α₃ : (singularChains ℤ X).X (k + (mj + 1)))
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj X) k)
    (hφA : φA ∈ relKern ℤ X Kᶜ k) (hφB : φB ∈ relKern ℤ X Lᶜ k)
    (hlift : φ = φA - φB)
    (hα₁ : α₁ ∈ LinearMap.range (((inclChains X U).f (k + (mj + 1))).hom))
    (hα₂ : α₂ ∈ LinearMap.range (((inclChains X (U ∩ V)).f (k + (mj + 1))).hom))
    (h₃V : cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₃
      ∈ LinearMap.range (((inclChains X V).f (mj + 1)).hom))
    (hL : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
      ∈ LinearMap.range (((inclChains X Lᶜ).f (k + mj)).hom))
    (hK : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃
      ∈ LinearMap.range (((inclChains X Kᶜ).f (k + mj)).hom))
    (hd : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
      ∈ LinearMap.range (((inclChains X (Kᶜ ∩ Lᶜ)).f (k + mj)).hom))
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0)
    (hbd : ∃ β : (singularChains ℤ X).X (mj + 2),
        (singularChains ℤ X).d (mj + 2) (mj + 1) β
          = cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) (α₁ + α₂ + α₃)) :
    ∃ γ ∈ LinearMap.range (((inclChains X (U ∩ V)).f (mj + 1)).hom),
        (singularChains ℤ X).d (mj + 1) mj γ =
          (-1 : ℤ) ^ (k + 1) • cap ℤ (TopCat.toSSet.obj X)
            (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
              ((capIdx k mj) ▸ α₂) := by
  have hcrux := pd_crux_identity_weak α₁ α₂ α₃ φ φA φB hφA hφB hlift hL hK hd hφd
  have h₁U : cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁ ∈
      LinearMap.range ((inclChains X U).f (mj + 1)).hom :=
    cap_mem_range_inclChains (M := X) U k (mj + 1) φ hα₁
  have hA₂U : cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂ ∈
      LinearMap.range ((inclChains X U).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := U ∩ V) (T := U) (fun x hx => hx.1)
      (cap_mem_range_inclChains (M := X) (U ∩ V) k (mj + 1) φA hα₂)
  have hA₂V : cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂ ∈
      LinearMap.range ((inclChains X V).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := U ∩ V) (T := V) (fun x hx => hx.2)
      (cap_mem_range_inclChains (M := X) (U ∩ V) k (mj + 1) φA hα₂)
  have h₂V : cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₂ ∈
      LinearMap.range ((inclChains X V).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := U ∩ V) (T := V) (fun x hx => hx.2)
      (cap_mem_range_inclChains (M := X) (U ∩ V) k (mj + 1) φ hα₂)
  obtain ⟨β, hβ⟩ := hbd
  obtain ⟨c, hcmem, hcd⟩ := mv_boundary_d_of_small_cycle (X := X) hU hV hcov
    (z := cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) (α₁ + α₂ + α₃))
    (zU := cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁
      + cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
    (zV := cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₂
      + cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₃
      - cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
    (add_mem h₁U hA₂U)
    (sub_mem (add_mem h₂V h₃V) hA₂V)
    (by rw [map_add, map_add]; abel)
    ⟨β, hβ⟩
  refine ⟨c, hcmem, ?_⟩
  rw [hcd]
  exact hcrux


theorem pd_ab_lift_of_iso {X : TopCat} (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (k : ℕ)
    (ψ : (pdABCoh X A B).cycles (k+1)) :
    ∃ (u : (relComplex ℤ X (A ∪ B)).cycles (k+1)) (χ : (pdABCoh X A B).X k),
      (pdABCoh X A B).d k (k+1) χ
        = (pdABCoh X A B).iCycles (k+1) ψ
          - (pdABInclRel X A B).f (k+1) ((relComplex ℤ X (A ∪ B)).iCycles (k+1) u) := by
  classical
  haveI hqi : IsIso (HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1)) :=
    pdABCoh_quasiIso hA hB (k+1)
  let y : (relComplex ℤ X (A ∪ B)).homology (k+1) :=
    (CategoryTheory.inv (HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1)))
      ((pdABCoh X A B).homologyπ (k+1) ψ)
  obtain ⟨u, hu⟩ : ∃ u : (relComplex ℤ X (A ∪ B)).cycles (k+1),
      (relComplex ℤ X (A ∪ B)).homologyπ (k+1) u = y :=
    (ModuleCat.epi_iff_surjective ((relComplex ℤ X (A ∪ B)).homologyπ (k+1))).mp inferInstance y
  have hcl : HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1)
      ((relComplex ℤ X (A ∪ B)).homologyπ (k+1) u) = (pdABCoh X A B).homologyπ (k+1) ψ := by
    rw [hu]
    exact IsIso.inv_hom_id_apply
      (HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1))
      ((pdABCoh X A B).homologyπ (k+1) ψ)
  have hnat : HomologicalComplex.homologyMap (pdABInclRel X A B) (k+1)
      ((relComplex ℤ X (A ∪ B)).homologyπ (k+1) u)
      = (pdABCoh X A B).homologyπ (k+1)
        (HomologicalComplex.cyclesMap (pdABInclRel X A B) (k+1) u) := by
    have h := congrArg (fun (g : ((relComplex ℤ X (A ∪ B)).cycles (k+1) ⟶
        (pdABCoh X A B).homology (k+1))) => (ModuleCat.Hom.hom g) u)
      (HomologicalComplex.homologyπ_naturality (pdABInclRel X A B) (k+1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hz : (pdABCoh X A B).homologyπ (k+1)
      (HomologicalComplex.cyclesMap (pdABInclRel X A B) (k+1) u - ψ) = 0 := by
    rw [map_sub, ← hnat, hcl, sub_self]
  obtain ⟨χ, hχ⟩ :=
    (pd_cochain_homologyπ_eq_zero_iff_d (C := pdABCoh X A B) k
      (HomologicalComplex.cyclesMap (pdABInclRel X A B) (k+1) u - ψ)).mp hz
  have hcyc : (pdABCoh X A B).iCycles (k+1)
        (HomologicalComplex.cyclesMap (pdABInclRel X A B) (k+1) u)
      = (pdABInclRel X A B).f (k+1) ((relComplex ℤ X (A ∪ B)).iCycles (k+1) u) := by
    have h := congrArg (fun (g : ((relComplex ℤ X (A ∪ B)).cycles (k+1) ⟶
        (pdABCoh X A B).X (k+1))) => (ModuleCat.Hom.hom g) u)
      (HomologicalComplex.cyclesMap_i (pdABInclRel X A B) (k+1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  refine ⟨u, -χ, ?_⟩
  rw [map_neg, hχ, map_sub, hcyc]
  abel


theorem pd_inter_data {M : TopCat} [T2Space M] {U V K₁ K₂ : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂) (k : ℕ)
    (ψ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (k+1))
    (hψK : ψ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₁) (k+1))
    (hψL : ψ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₂) (k+1))
    (hψd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k+1) ψ = 0) :
    ∃ (u : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).cycles (k+1))
      (χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k),
      χ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₁) k ∧
      χ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₂) k ∧
      cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) χ
        = ψ - pdCohUnderCycle (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂)) (k+1) u := by
  classical
  let X : TopCat := TopCat.of (U ∪ V : Set M)
  let A : Set X := pdRelSub (U ∪ V : Set M) K₁
  let B : Set X := pdRelSub (U ∪ V : Set M) K₂
  have hAopen : IsOpen A := by
    rw [show A = (pdTr (U ∪ V : Set M) K₁)ᶜ from pdRelSub_eq_compl_pdTr (U ∪ V : Set M) K₁]
    exact (hK₁c.isClosed.preimage continuous_subtype_val).isOpen_compl
  have hBopen : IsOpen B := by
    rw [show B = (pdTr (U ∪ V : Set M) K₂)ᶜ from pdRelSub_eq_compl_pdTr (U ∪ V : Set M) K₂]
    exact (hK₂c.isClosed.preimage continuous_subtype_val).isOpen_compl
  have hψK' : ψ ∈ relKern ℤ X A (k+1) := hψK
  have hψL' : ψ ∈ relKern ℤ X B (k+1) := hψL
  let ψel : (pdABCoh X A B).X (k+1) :=
    ⟨ψ, Submodule.mem_inf.mpr ⟨hψK', hψL'⟩⟩
  have hψelco : ψel.1 = ψ := rfl
  have hψcycle : (pdABCoh X A B).d (k+1) (k+2) ψel = 0 := by
    apply Subtype.ext
    rw [pdABCoh_d_coe, Submodule.coe_zero, hψelco]
    rw [pd_singularD_eq_cochainDiff X (k+1) ψ]
    exact hψd
  let ψc : (pdABCoh X A B).cycles (k+1) :=
    HomologicalComplex.cyclesMk (pdABCoh X A B) ψel (k+2)
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (k+1) (k+2) rfl)) hψcycle
  have hiψ : (pdABCoh X A B).iCycles (k+1) ψc = ψel := by
    exact HomologicalComplex.i_cyclesMk (K := pdABCoh X A B) (x := ψel) (j := k+2) _ hψcycle
  obtain ⟨u0, χ0, hχ0d⟩ := pd_ab_lift_of_iso A B hAopen hBopen k ψc
  have hAuB : A ∪ B = pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂) := by
    rw [show A = pdRelSub (U ∪ V : Set M) K₁ from rfl,
      show B = pdRelSub (U ∪ V : Set M) K₂ from rfl]
    exact pdRelSub_union_sub (U ∪ V : Set M) K₁ K₂
  let u : (relComplex ℤ X (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).cycles (k+1) :=
    HomologicalComplex.cyclesMap (pdRelComplexCongr hAuB).hom (k+1) u0
  refine ⟨u, χ0.1, ?_, ?_, ?_⟩
  · exact (Submodule.mem_inf.mp χ0.2).1
  · exact (Submodule.mem_inf.mp χ0.2).2
  · have hcycle1 : (((pdABCoh X A B).iCycles (k+1) ψc) : (pdABCoh X A B).X (k+1)).1 = ψ := by
      rw [hiψ, hψelco]
    have hu : pdCohUnderCycle X (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂)) (k+1) u
        = (((relComplex ℤ X (A ∪ B)).iCycles (k+1) u0) :
            (relComplex ℤ X (A ∪ B)).X (k+1)).1 := by
      rw [show u = HomologicalComplex.cyclesMap (pdRelComplexCongr hAuB).hom (k+1) u0 from rfl]
      rw [show pdCohUnderCycle X (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂)) (k+1)
            (HomologicalComplex.cyclesMap (pdRelComplexCongr hAuB).hom (k+1) u0)
          = (((relComplex ℤ X (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).iCycles (k+1)
              (HomologicalComplex.cyclesMap (pdRelComplexCongr hAuB).hom (k+1) u0)) :
              (relComplex ℤ X (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).X (k+1)).1
        from rfl]
      rw [pdInter_iCycles_cyclesMap_apply]
      exact pdRelComplexCongr_coe hAuB (k+1) ((relComplex ℤ X (A ∪ B)).iCycles (k+1) u0)
    have hco : ((pdABCoh X A B).d k (k+1) χ0).1
        = (((pdABCoh X A B).iCycles (k+1) ψc) : (pdABCoh X A B).X (k+1)).1
          - (((pdABInclRel X A B).f (k+1)
              ((relComplex ℤ X (A ∪ B)).iCycles (k+1) u0)) :
                (pdABCoh X A B).X (k+1)).1 := by
      rw [hχ0d, Submodule.coe_sub]
    rw [pdABCoh_d_coe, pd_singularD_eq_cochainDiff X k χ0.1, hcycle1, pdABInclRel_coe] at hco
    rw [← hu] at hco
    exact hco

theorem pd_ab_exact_decomp {X : TopCat} (A B : Set X) (k : ℕ)
    (w : (relComplex ℤ X (A ∩ B)).homology k)
    (h : PDABClean.pdABδ X A B k w = 0) :
    ∃ (x₁ : (relComplex ℤ X A).homology k) (x₂ : (relComplex ℤ X B).homology k),
      w = (HomologicalComplex.homologyMap (pdToInterA X A B) k) x₁
          - (HomologicalComplex.homologyMap (pdToInterB X A B) k) x₂ := by
  classical
  obtain ⟨e, he1, he2⟩ := homology_biprod_iso (relComplex ℤ X A) (relComplex ℤ X B) k
  have hsurj := (ShortComplex.moduleCat_exact_iff (S :=
    ShortComplex.mk (HomologicalComplex.homologyMap (PDABClean.pdABg X A B) k)
      (PDABClean.pdABδ X A B k) (PDABClean.pdAB_comp_δ X A B k))).mp
      (PDABClean.pdAB_exact₃ X A B k)
  obtain ⟨z, hz⟩ := hsurj w h
  let y := (ModuleCat.Hom.hom e.hom) z
  let x₁ : (relComplex ℤ X A).homology k :=
    (ModuleCat.Hom.hom (biprod.fst : (relComplex ℤ X A).homology k ⊞
      (relComplex ℤ X B).homology k ⟶ (relComplex ℤ X A).homology k)) y
  let x₂ : (relComplex ℤ X B).homology k :=
    (ModuleCat.Hom.hom (biprod.snd : (relComplex ℤ X A).homology k ⊞
      (relComplex ℤ X B).homology k ⟶ (relComplex ℤ X B).homology k)) y
  have htotal : (ModuleCat.Hom.hom (biprod.inl : (relComplex ℤ X A).homology k ⟶
        (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k)) x₁
      + (ModuleCat.Hom.hom (biprod.inr : (relComplex ℤ X B).homology k ⟶
        (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k)) x₂ = y := by
    have htot : (biprod.fst : (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k ⟶
          (relComplex ℤ X A).homology k) ≫ (biprod.inl : (relComplex ℤ X A).homology k ⟶
          (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k)
        + (biprod.snd : (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k ⟶
          (relComplex ℤ X B).homology k) ≫ (biprod.inr : (relComplex ℤ X B).homology k ⟶
          (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k) = 𝟙 _ := by
      have hb := IsBilimit.binary_total (BinaryBiproduct.isBilimit
        ((relComplex ℤ X A).homology k) ((relComplex ℤ X B).homology k))
      simpa [BinaryBiproduct.bicone_fst, BinaryBiproduct.bicone_snd, BinaryBiproduct.bicone_inl,
        BinaryBiproduct.bicone_inr] using hb
    have h := congrArg (fun (f : (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k ⟶
      (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k) =>
      (ModuleCat.Hom.hom f) y) htot
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  have hz2 : z = (HomologicalComplex.homologyMap
        (biprod.inl : relComplex ℤ X A ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B) k) x₁
      + (HomologicalComplex.homologyMap
        (biprod.inr : relComplex ℤ X B ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B) k) x₂ := by
    have hinv : z = (ConcreteCategory.hom e.inv)
        ((ModuleCat.Hom.hom (biprod.inl : (relComplex ℤ X A).homology k ⟶
            (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k)) x₁
          + (ModuleCat.Hom.hom (biprod.inr : (relComplex ℤ X B).homology k ⟶
            (relComplex ℤ X A).homology k ⊞ (relComplex ℤ X B).homology k)) x₂) := by
      rw [htotal]
      simpa only [y] using (Iso.hom_inv_id_apply e z).symm
    rw [hinv, map_add]
    congr 1
    · have hh := congrArg (fun (g : (relComplex ℤ X A).homology k ⟶
          (relComplex ℤ X A ⊞ relComplex ℤ X B).homology k) => (ModuleCat.Hom.hom g) x₁) he1
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
    · have hh := congrArg (fun (g : (relComplex ℤ X B).homology k ⟶
          (relComplex ℤ X A ⊞ relComplex ℤ X B).homology k) => (ModuleCat.Hom.hom g) x₂) he2
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have hcoefA : CategoryTheory.CategoryStruct.comp (biprod.inl : relComplex ℤ X A ⟶
      relComplex ℤ X A ⊞ relComplex ℤ X B) (PDABClean.pdABg X A B) = pdToInterA X A B :=
    biprod.inl_desc _ _
  have hcoefB : CategoryTheory.CategoryStruct.comp (biprod.inr : relComplex ℤ X B ⟶
      relComplex ℤ X A ⊞ relComplex ℤ X B) (PDABClean.pdABg X A B) = - pdToInterB X A B :=
    biprod.inr_desc _ _
  have hkey1 : (HomologicalComplex.homologyMap (PDABClean.pdABg X A B) k)
      ((HomologicalComplex.homologyMap (biprod.inl : relComplex ℤ X A ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B) k) x₁)
      = (HomologicalComplex.homologyMap (pdToInterA X A B) k) x₁ := by
    rw [← hcoefA, HomologicalComplex.homologyMap_comp]
    rfl
  have hkey2 : (HomologicalComplex.homologyMap (PDABClean.pdABg X A B) k)
      ((HomologicalComplex.homologyMap (biprod.inr : relComplex ℤ X B ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B) k) x₂)
      = - (HomologicalComplex.homologyMap (pdToInterB X A B) k) x₂ := by
    have h1 : HomologicalComplex.homologyMap
        (CategoryTheory.CategoryStruct.comp (biprod.inr : relComplex ℤ X B ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B) (PDABClean.pdABg X A B)) k
        = HomologicalComplex.homologyMap (biprod.inr : relComplex ℤ X B ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B) k
          ≫ HomologicalComplex.homologyMap (PDABClean.pdABg X A B) k :=
      HomologicalComplex.homologyMap_comp (biprod.inr : relComplex ℤ X B ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B) (PDABClean.pdABg X A B) k
    rw [hcoefB, HomologicalComplex.homologyMap_neg] at h1
    have h2 := congrArg (fun (g : (relComplex ℤ X B).homology k ⟶
        (relComplex ℤ X (A ∩ B)).homology k) => (ModuleCat.Hom.hom g) x₂) h1.symm
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
      LinearMap.neg_apply] using h2
  refine ⟨x₁, x₂, ?_⟩
  rw [← hz, hz2, map_add, hkey1, hkey2, sub_eq_add_neg]

theorem pd_split_crux {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Work.Cohomology.Good N c U hU) (hVV : Work.Cohomology.Good N c V hV)
    (hII : Work.Cohomology.Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) (hm : 1 ≤ m)
    {K₁ K₂ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    (x : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k)
    (hx : Work.Cohomology.goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k m hkm x = 0) :
    ∃ (K₁' K₂' : Set M) (h₁ : K₁ ⊆ K₁') (h₂ : K₂ ⊆ K₂') (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
      (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
      (x₁ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁')).homology k)
      (x₂ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂')).homology k),
      (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.union_subset (h₁.trans Set.subset_union_left)
          (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k) x
        = (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
          - (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂ := by
  classical
  -- ## Step 0: degree bookkeeping and notation
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hNz : N = k + (m' + 1) := by omega
  subst hNz
  let W : Set M := U ∪ V
  let X : TopCat := TopCat.of W
  have hW : IsOpen W := hU.union hV
  have hUW : U ⊆ W := Set.subset_union_left
  have hVW : V ⊆ W := Set.subset_union_right
  have hUt : IsOpen (pdTr W U) := hU.preimage continuous_subtype_val
  have hVt : IsOpen (pdTr W V) := hV.preimage continuous_subtype_val
  have hcov : pdTr W U ∪ pdTr W V = (Set.univ : Set W) := by
    rw [pdTr_union]
    ext x
    exact ⟨fun _ => trivial, fun _ => x.2⟩
  let K₀ : Set M := K₁ ∩ K₂
  have hK₀U : K₀ ⊆ U := fun x hx => hK₁U hx.1
  have hK₀V : K₀ ⊆ V := fun x hx => hK₂V hx.2
  have hK₀I : K₀ ⊆ U ∩ V := fun x hx => ⟨hK₀U hx, hK₀V hx⟩
  have hK₀c : IsCompact K₀ := hK₁c.inter hK₂c
  have hK₁W : K₁ ⊆ W := hK₁U.trans hUW
  have hK₂W : K₂ ⊆ W := hK₂V.trans hVW
  have hKW : K₁ ∪ K₂ ⊆ W := Set.union_subset hK₁W hK₂W
  have hKc : IsCompact (K₁ ∪ K₂) := hK₁c.union hK₂c
  -- ## Step 1: a cocycle representative of `x`, and the duality hypothesis
  obtain ⟨z, hz⟩ : ∃ z : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).cycles k,
      (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).homologyπ k z = x :=
    (ModuleCat.epi_iff_surjective
      ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).homologyπ k)).mp inferInstance x
  have hxW : goodD (k + (m' + 1)) c W hW (K₁ ∪ K₂) hKW hKc k (m' + 1) rfl
      ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).homologyπ k z) = 0 := by
    rw [hz]; exact hx
  set φz : Cochain ℤ (TopCat.toSSet.obj X) k :=
    ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z).1 with hφzdef
  -- ## Step 2: the Hatcher decomposition in the ambient space
  obtain ⟨αM, hαMc, aM, bM, dM, jM, hαMsum, ⟨a', ha'⟩, ⟨b0', hb0'⟩, ⟨d', hd'⟩, ⟨j', hj'⟩⟩ :=
    pd_hatcher_data (N := k + (m' + 1)) c hU hV hK₁c hK₂c hK₁U hK₂V
  have hA1M : aM ∈ LinearMap.range (((inclChains M (U \ K₂)).f (k + (m' + 1))).hom) :=
    ⟨a', ha'⟩
  have hA2M : bM ∈ LinearMap.range (((inclChains M (U ∩ V)).f (k + (m' + 1))).hom) :=
    ⟨b0', hb0'⟩
  have hA3M : dM ∈ LinearMap.range (((inclChains M (V \ K₁)).f (k + (m' + 1))).hom) :=
    ⟨d', hd'⟩
  have hA4M : jM ∈ LinearMap.range (((inclChains M ((K₁ ∪ K₂)ᶜ)).f (k + (m' + 1))).hom) :=
    ⟨j', hj'⟩
  -- ## Step 3: the middle piece in the `U ∩ V`-world
  have hsub₂₄ : (U \ K₂ : Set M) ⊆ (K₁ ∩ K₂)ᶜ := fun x hx h => hx.2 h.2
  have hsub₃₄ : (V \ K₁ : Set M) ⊆ (K₁ ∩ K₂)ᶜ := fun x hx h => hx.2 h.1
  have hsub_j : ((K₁ ∪ K₂)ᶜ : Set M) ⊆ (K₁ ∩ K₂)ᶜ := by
    intro x hx h
    exact hx (Or.inl h.1)
  have haM4 : aM ∈ LinearMap.range (((inclChains M ((K₁ ∩ K₂)ᶜ)).f (k + (m' + 1))).hom) :=
    mem_range_inclChains_of_subset hsub₂₄ hA1M
  have hdM45 : dM + jM ∈ LinearMap.range
      (((inclChains M ((K₁ ∩ K₂)ᶜ)).f (k + (m' + 1))).hom) :=
    add_mem (mem_range_inclChains_of_subset hsub₃₄ hA3M)
      (mem_range_inclChains_of_subset hsub_j hA4M)
  have hξM : (singularChains ℤ M).iCycles (k + (m' + 1)) αM - (aM + bM + (dM + jM))
      ∈ LinearMap.range (((inclChains M ((K₁ ∩ K₂)ᶜ)).f (k + (m' + 1))).hom) := by
    have hzero : (aM + bM + dM + jM) - (aM + bM + (dM + jM)) = 0 := by abel
    rw [hαMsum, hzero]
    exact Submodule.zero_mem _
  obtain ⟨b', γ₂, hb', hγ₂i, hγ₂c⟩ :=
    pd_hatcher_inter_wk2 (N := k + (m' + 1)) (c := c) (K := K₁) (L := K₂)
      hU hV hI hK₁c hK₂c hK₁U hK₂V αM aM bM (dM + jM) hξM haM4 hA2M hdM45 hαMc
  -- ## Step 4: the pieces in the space `X = W`
  have h₁W : (U \ K₂ : Set M) ⊆ W := fun x hx => Set.mem_union_left V hx.1
  have h₂W : (U ∩ V : Set M) ⊆ W := fun x hx => Set.mem_union_left V hx.1
  have h₃W : (V \ K₁ : Set M) ⊆ W := fun x hx => Set.mem_union_right U hx.1
  let aW : (singularChains ℤ X).X (k + (m' + 1)) :=
    (inclChainsSub M (U \ K₂) W h₁W).f (k + (m' + 1)) a'
  let bW : (singularChains ℤ X).X (k + (m' + 1)) :=
    (inclChainsSub M (U ∩ V) W h₂W).f (k + (m' + 1)) b'
  let dW : (singularChains ℤ X).X (k + (m' + 1)) :=
    (inclChainsSub M (V \ K₁) W h₃W).f (k + (m' + 1)) d'
  have haW : (inclChains M W).f (k + (m' + 1)) aW = aM := by
    have h := congrArg (fun (φ : singularChains ℤ (TopCat.of ↥(U \ K₂)) ⟶ singularChains ℤ M) =>
      (φ.f (k + (m' + 1))).hom a') (inclChainsSub_comp M (U \ K₂) W h₁W)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.trans ha'
  have hbW : (inclChains M W).f (k + (m' + 1)) bW = bM := by
    have h := congrArg (fun (φ : singularChains ℤ (TopCat.of ↥(U ∩ V)) ⟶ singularChains ℤ M) =>
      (φ.f (k + (m' + 1))).hom b') (inclChainsSub_comp M (U ∩ V) W h₂W)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.trans hb'
  have hdW : (inclChains M W).f (k + (m' + 1)) dW = dM := by
    have h := congrArg (fun (φ : singularChains ℤ (TopCat.of ↥(V \ K₁)) ⟶ singularChains ℤ M) =>
      (φ.f (k + (m' + 1))).hom d') (inclChainsSub_comp M (V \ K₁) W h₃W)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.trans hd'
  have haWmem : aW ∈ LinearMap.range
      (((inclChains X (pdTr W (U \ K₂))).f (k + (m' + 1))).hom) :=
    inclChainsSub_mem_range h₁W (k + (m' + 1)) a'
  have hbWmem : bW ∈ LinearMap.range
      (((inclChains X (pdTr W (U ∩ V))).f (k + (m' + 1))).hom) :=
    inclChainsSub_mem_range h₂W (k + (m' + 1)) b'
  have hdWmem : dW ∈ LinearMap.range
      (((inclChains X (pdTr W (V \ K₁))).f (k + (m' + 1))).hom) :=
    inclChainsSub_mem_range h₃W (k + (m' + 1)) d'
  -- the boundary of `aW + bW + dW` is supported outside `K₁ ∪ K₂`
  have hdjM : (singularChains ℤ M).d (k + (m' + 1)) (k + m' + 1 - 1) jM
      ∈ LinearMap.range (((inclChains M ((K₁ ∪ K₂)ᶜ)).f (k + m' + 1 - 1)).hom) :=
    d_mem_range_inclChains hA4M
  have hbdM : (singularChains ℤ M).d (k + (m' + 1)) (k + m' + 1 - 1) (aM + bM + dM)
      = - ((singularChains ℤ M).d (k + (m' + 1)) (k + m' + 1 - 1) jM) := by
    have h2 : (singularChains ℤ M).d (k + (m' + 1)) (k + m' + 1 - 1)
        (aM + bM + dM + jM) = 0 := by
      rw [← hαMsum, ← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
      simp
    have h3 : (singularChains ℤ M).d (k + (m' + 1)) (k + m' + 1 - 1) (aM + bM + dM)
        + (singularChains ℤ M).d (k + (m' + 1)) (k + m' + 1 - 1) jM = 0 := by
      rw [← map_add]
      exact h2
    exact eq_neg_of_add_eq_zero_left h3
  have hmem4 : (singularChains ℤ X).d (k + (m' + 1)) (k + m' + 1 - 1) (aW + bW + dW)
      ∈ LinearMap.range (((inclChains X (pdTr W ((K₁ ∪ K₂)ᶜ))).f (k + m' + 1 - 1)).hom) := by
    apply mem_range_inclChains_of_image (M := M) (W := W) (S := (K₁ ∪ K₂)ᶜ) (k + m' + 1 - 1)
    have hnat : (singularChains ℤ M).d (k + (m' + 1)) (k + m' + 1 - 1)
        ((inclChains M W).f (k + (m' + 1)) (aW + bW + dW))
        = (inclChains M W).f (k + m' + 1 - 1)
          ((singularChains ℤ X).d (k + (m' + 1)) (k + m' + 1 - 1) (aW + bW + dW)) := by
      have h := congrArg (fun (g : (singularChains ℤ X).X (k + (m' + 1)) ⟶
          (singularChains ℤ M).X (k + m' + 1 - 1)) => (ModuleCat.Hom.hom g) (aW + bW + dW))
        ((inclChains M W).comm (k + (m' + 1)) (k + m' + 1 - 1))
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    rw [← hnat]
    have hsplit : (inclChains M W).f (k + (m' + 1)) (aW + bW + dW) = aM + bM + dM := by
      rw [map_add, map_add, haW, hbW, hdW]
    rw [hsplit, hbdM]
    exact neg_mem hdjM
  -- ## Step 5: the relative cycle in `X` representing the local class of `W` at `K₁ ∪ K₂`
  have hmem4' : (singularChains ℤ X).d (k + (m' + 1)) (k + m' + 1 - 1) (aW + bW + dW)
      ∈ LinearMap.range
        (((inclChains X (pdRelSub W (K₁ ∪ K₂))).f (k + m' + 1 - 1)).hom) :=
    mem_range_inclChains_of_subset (M := X) (S := pdTr W ((K₁ ∪ K₂)ᶜ))
      (T := pdRelSub W (K₁ ∪ K₂)) (fun x hx => hx) hmem4
  obtain ⟨e4, he4⟩ := hmem4'
  have hcyc4 : (relChains X (pdRelSub W (K₁ ∪ K₂))).d (k + (m' + 1)) (k + m' + 1 - 1)
      (((cokernel.π (inclChains X (pdRelSub W (K₁ ∪ K₂)))).f (k + (m' + 1)))
        (aW + bW + dW)) = 0 := by
    show ((cokernel (inclChains X (pdRelSub W (K₁ ∪ K₂)))).d (k + (m' + 1)) (k + m' + 1 - 1))
      (((cokernel.π (inclChains X (pdRelSub W (K₁ ∪ K₂)))).f (k + (m' + 1))) (aW + bW + dW)) = 0
    have hnat := congrArg (fun (g : (singularChains ℤ X).X (k + (m' + 1)) ⟶
        (cokernel (inclChains X (pdRelSub W (K₁ ∪ K₂)))).X (k + m' + 1 - 1)) =>
      (ModuleCat.Hom.hom g) (aW + bW + dW))
      ((cokernel.π (inclChains X (pdRelSub W (K₁ ∪ K₂)))).comm (k + (m' + 1)) (k + m' + 1 - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hnat, ← he4]
    exact cokernel_π_f_apply_eq_zero (k + m' + 1 - 1) e4
  let γW : (relChains X (pdRelSub W (K₁ ∪ K₂))).cycles (k + (m' + 1)) :=
    cycleOf (k + (m' + 1)) (((cokernel.π (inclChains X (pdRelSub W (K₁ ∪ K₂)))).f (k + (m' + 1)))
      (aW + bW + dW)) hcyc4
  have hγWi : (relChains X (pdRelSub W (K₁ ∪ K₂))).iCycles (k + (m' + 1)) γW
      = ((cokernel.π (inclChains X (pdRelSub W (K₁ ∪ K₂)))).f (k + (m' + 1)))
        (aW + bW + dW) := iCycles_cycleOf _ _ hcyc4
  have hξbc : (inclChains M W).f (k + (m' + 1)) (aW + bW + dW)
      = (singularChains ℤ M).iCycles (k + (m' + 1)) αM - jM := by
    rw [map_add, map_add, haW, hbW, hdW, hαMsum]
    abel
  have hj0 : ((cokernel.π (inclChains M ((K₁ ∪ K₂)ᶜ))).f (k + (m' + 1))) jM = 0 := by
    obtain ⟨y, hy⟩ := hA4M
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero (k + (m' + 1)) y
  have hγWc : (relChains X (pdRelSub W (K₁ ∪ K₂))).homologyπ (k + (m' + 1)) γW
      = localFundClass (k + (m' + 1)) c W hW (K₁ ∪ K₂) hKW hKc := by
    have hcovW : (W : Set M) ∪ (K₁ ∪ K₂)ᶜ = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      by_cases h : x ∈ K₁ ∪ K₂
      · exact Or.inl (hKW h)
      · exact Or.inr h
    have hcl : HomologicalComplex.homologyMap (relChainsMap M W ((K₁ ∪ K₂)ᶜ)) (k + (m' + 1))
        ((relChains X (pdRelSub W (K₁ ∪ K₂))).homologyπ (k + (m' + 1)) γW)
        = relLocClass M (k + (m' + 1)) c (K₁ ∪ K₂) :=
      relCycle_homologyMap_eq_relLocClass c γW hγWi hαMc hξbc hj0
    haveI : IsIso (HomologicalComplex.homologyMap (relChainsMap M W ((K₁ ∪ K₂)ᶜ))
        (k + (m' + 1))) :=
      excision_relChainsMap_isIso M W ((K₁ ∪ K₂)ᶜ) hW hKc.isClosed.isOpen_compl hcovW
        (k + (m' + 1))
    have hspec := localFundClass_spec (k + (m' + 1)) c W hW (K₁ ∪ K₂) hKW hKc
    calc (relChains X (pdRelSub W (K₁ ∪ K₂))).homologyπ (k + (m' + 1)) γW
        = inv (HomologicalComplex.homologyMap (relChainsMap M W ((K₁ ∪ K₂)ᶜ)) (k + (m' + 1)))
            (HomologicalComplex.homologyMap (relChainsMap M W ((K₁ ∪ K₂)ᶜ)) (k + (m' + 1))
              ((relChains X (pdRelSub W (K₁ ∪ K₂))).homologyπ (k + (m' + 1)) γW)) :=
          (IsIso.hom_inv_id_apply _ _).symm
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M W ((K₁ ∪ K₂)ᶜ)) (k + (m' + 1)))
            (relLocClass M (k + (m' + 1)) c (K₁ ∪ K₂)) := by rw [hcl]
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M W ((K₁ ∪ K₂)ᶜ)) (k + (m' + 1)))
            (HomologicalComplex.homologyMap (relChainsMap M W ((K₁ ∪ K₂)ᶜ)) (k + (m' + 1))
              (localFundClass (k + (m' + 1)) c W hW (K₁ ∪ K₂) hKW hKc)) := by rw [hspec]
      _ = localFundClass (k + (m' + 1)) c W hW (K₁ ∪ K₂) hKW hKc := IsIso.hom_inv_id_apply _ _
  -- ## Step 6: the cap with the fundamental cycle is a boundary
  have hbd : ∃ β : (singularChains ℤ X).X ((m' + 1) + 1),
      (singularChains ℤ X).d ((m' + 1) + 1) (m' + 1) β
        = cap ℤ (TopCat.toSSet.obj X) φz (m' + 1) (aW + bW + dW) :=
    pd_cap_chain_boundary (M := M) (K := K₁ ∪ K₂) (W := W) hW hKW hKc
      c z γW hγWc (aW + bW + dW) hγWi hxW
  -- ## Step 7: the `A+B` world
  let A : Set X := pdRelSub W K₁
  let B : Set X := pdRelSub W K₂
  have hAB : A ∩ B = pdRelSub W (K₁ ∪ K₂) := (pdRelSub_union W K₁ K₂).symm
  have hφzmem : φz ∈ relKern ℤ X (pdRelSub W (K₁ ∪ K₂)) k :=
    ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z).2
  have hφzmem' : φz ∈ relKern ℤ X (A ∩ B) k := hAB ▸ hφzmem
  -- the lift in the `A+B` bicomplex
  obtain ⟨φt, hφt⟩ := PDABClean.pdBiprodToInter_surj X A B k
    (⟨φz, hφzmem'⟩ : (relComplex ℤ X (A ∩ B)).X k)
  let φA : (relComplex ℤ X A).X k :=
    (biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶ relComplex ℤ X A).f k φt
  let φB : (relComplex ℤ X B).X k :=
    (biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶ relComplex ℤ X B).f k φt
  have hdecomp : (biprod.inl : relComplex ℤ X A ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B).f k φA
      + (biprod.inr : relComplex ℤ X B ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B).f k φB = φt :=
    PDABClean.pdBiprod_total X A B k φt
  have hlift : φz = ((φA : relKern ℤ X A k).1 : Cochain ℤ (TopCat.toSSet.obj X) k)
      - (φB : relKern ℤ X B k).1 := by
    have h1 : (ModuleCat.Hom.hom ((pdBiprodToInter X A B).f k))
        ((ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) φA
          + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) φB)
        = (⟨φz, hφzmem'⟩ : (relComplex ℤ X (A ∩ B)).X k) := by
      rw [hdecomp]; exact hφt
    have h2 : ((ModuleCat.Hom.hom ((pdBiprodToInter X A B).f k))
        ((ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) φA
          + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f k)) φB) : relKern ℤ X (A ∩ B) k).1 = φz := by
      rw [congrArg (fun (x : (relComplex ℤ X (A ∩ B)).X k) => (x : relKern ℤ X (A ∩ B) k).1) h1]
    exact h2.symm.trans (PDABClean.pdBiprodToInter_coe X A B k φA φB)
  have hφAc : ((φA : relKern ℤ X A k).1 : Cochain ℤ (TopCat.toSSet.obj X) k)
      ∈ relKern ℤ X ((pdTr W K₁)ᶜ) k := φA.2
  have hφBc : ((φB : relKern ℤ X B k).1 : Cochain ℤ (TopCat.toSSet.obj X) k)
      ∈ relKern ℤ X ((pdTr W K₂)ᶜ) k := φB.2
  set φAc : Cochain ℤ (TopCat.toSSet.obj X) k :=
    ((φA : relKern ℤ X A k).1 : Cochain ℤ (TopCat.toSSet.obj X) k) with hφAcdef
  set φBc : Cochain ℤ (TopCat.toSSet.obj X) k :=
    ((φB : relKern ℤ X B k).1 : Cochain ℤ (TopCat.toSSet.obj X) k) with hφBcdef
  have hφzd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φz = 0 := by
    have h0 : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1)
        ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z) = 0 := by
      have hcomp : (ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k ≫
            (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1))) z
          = (ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).d k (k + 1)))
            ((ConcreteCategory.hom ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k)) z) :=
        CategoryTheory.ConcreteCategory.comp_apply _ _ z
      rw [← hcomp]
      exact congrArg (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).cycles k ⟶
          (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).X (k + 1)) =>
          (ConcreteCategory.hom g) z)
        (HomologicalComplex.iCycles_d (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))) k (k + 1))
    have hcomm := congrArg
      (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).X k ⟶
          (singularCochainComplex ℤ X).X (k+1)) =>
        (ConcreteCategory.hom g)
          ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z))
      ((relIncl ℤ X (pdRelSub W (K₁ ∪ K₂))).comm k (k+1))
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcomm
    rw [h0, map_zero] at hcomm
    have hrel : (ConcreteCategory.hom ((relIncl ℤ X (pdRelSub W (K₁ ∪ K₂))).f k))
          ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z) = φz := rfl
    rw [hrel] at hcomm
    rw [pd_singularD_eq_cochainDiff X k φz] at hcomm
    exact hcomm
  -- the `A+B` cocycle `ψ = d φA`
  have hsub_ψ : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) (φAc - φBc) = 0 := by
    have heq : φAc - φBc = φz := by
      rw [hφAcdef, hφBcdef]
      exact hlift.symm
    rw [heq, hφzd]
  have hψd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φAc
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φBc := by
    have h2 : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φAc
        - cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φBc = 0 := by
      have hms := map_sub (cochainDiffLM ℤ (TopCat.toSSet.obj X) k) φAc φBc
      simp only [cochainDiffLM_apply] at hms
      rw [← hms]
      exact hsub_ψ
    exact sub_eq_zero.mp h2
  have hψA : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φAc ∈ relKern ℤ X A (k + 1) := by
    rw [hφAcdef,
      ← pd_singularD_eq_cochainDiff X k
        ((φA : relKern ℤ X A k).1 : Cochain ℤ (TopCat.toSSet.obj X) k)]
    exact relKern_d_mem X A k ((φA : relKern ℤ X A k).1) (φA : relKern ℤ X A k).2
  have hψB : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φAc ∈ relKern ℤ X B (k + 1) := by
    rw [hψd, hφBcdef,
      ← pd_singularD_eq_cochainDiff X k
        ((φB : relKern ℤ X B k).1 : Cochain ℤ (TopCat.toSSet.obj X) k)]
    exact relKern_d_mem X B k ((φB : relKern ℤ X B k).1) (φB : relKern ℤ X B k).2
  obtain ⟨K₁', K₂', h₁, h₂, hK₁'U, hK₂'V, hK₁'c, hK₂'c, x₁, x₂, hfin⟩ :=
    pd_split_crux_rest (N := k + (m' + 1)) (c := c) hU hV hI hUU hVV hII
      k (m' + 1) rfl (by omega) hK₁U hK₂V hK₁c hK₂c z φA φB hlift hxW
  exact ⟨K₁', K₂', h₁, h₂, hK₁'U, hK₂'V, hK₁'c, hK₂'c, x₁, x₂, by rw [← hz]; exact hfin⟩

end

end Work.Cohomology
