import Mathlib
import Submission.Work.Whitney.RelRelCupG
import Submission.Work.Whitney.RelRelCup
import Submission.Work.Whitney.RelABComplex
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

/-!
# Naturality of the canonical relative–relative cup product

This file proves `Work.Whitney.relRelCup_natural`: there is a relative–relative cup product for
open `A B ⊆ X` (the *canonical* one: the Alexander–Whitney product on the `A+B` complex
transported along the inverse of the quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`) which
(i) forgets to the absolute cup product and (ii) is natural under a continuous map of pairs.

The proof is in three layers.

* `pdABMap` — the pullback of the `A+B` complex along a map of pairs, together with its
  compatibility with the Alexander–Whitney product (`pdABMap_starAB`) and with the inclusion
  `pdABInclRelR` (`pdABMap_comm`).
* `relRelCupHMap_natural` — naturality of the Alexander–Whitney product `relRelCupHMap` on
  cohomology, obtained from `pdABMap_starAB` by reducing to classes of cocycles.
* `pdABInvTransport` — the canonical transport (the inverse of the quasi-isomorphism on homology),
  its gauge-fixing equation `pdABInvTransport_gauge` and its naturality
  `pdABInvTransport_natural` (which follows from `pdABMap_comm` and the injectivity of a
  quasi-isomorphism).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
noncomputable section
variable {R : Type} [CommRing R]

/-- The `n`-th component of the pullback of the `A+B` complex along a map of pairs: the transpose
of the induced chain map, restricted to the intersection of the relative kernels. -/
noncomputable def pdABMapLM {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
    (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A) (hB' : ∀ x ∈ B', f x ∈ B) (n : ℕ) :
    pdABKernR (R := R) (TopCat.of X) A B n →ₗ[R] pdABKernR (R := R) (TopCat.of X') A' B' n where
  toFun γ := ⟨((dualChainMap R (TopCat.of X') (TopCat.of X) (TopCat.ofHom f)).f n).hom γ.1,
    Submodule.mem_inf.mpr ⟨
      relKern_map_mem (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hA' n
        ⟨γ.1, (Submodule.mem_inf.mp γ.2).1⟩,
      relKern_map_mem (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hB' n
        ⟨γ.1, (Submodule.mem_inf.mp γ.2).2⟩⟩⟩
  map_add' γ δ := by apply Subtype.ext; simp
  map_smul' c γ := by apply Subtype.ext; simp

/-- **The pullback of the `A+B` complex** `C^*(X,A+B) → C^*(X',A'+B')` along a continuous map
`f : X' → X` with `f '' A' ⊆ A`, `f '' B' ⊆ B`. -/
noncomputable def pdABMap {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
    (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A) (hB' : ∀ x ∈ B', f x ∈ B) :
    pdABCohR (R := R) (TopCat.of X) A B ⟶ pdABCohR (R := R) (TopCat.of X') A' B' :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (pdABMapLM (R := R) f A B A' B' hA' hB' n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, pdABCohR_d]
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        ((dualChainMap R (TopCat.of X') (TopCat.of X) (TopCat.ofHom f)).comm n (n+1))) x.1)

@[simp] theorem pdABMap_f {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
    (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A) (hB' : ∀ x ∈ B', f x ∈ B) (n : ℕ) :
    (pdABMap (R := R) f A B A' B' hA' hB').f n
      = ModuleCat.ofHom (pdABMapLM (R := R) f A B A' B' hA' hB' n) := rfl

theorem pdABMap_coe {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
    (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A) (hB' : ∀ x ∈ B', f x ∈ B) (n : ℕ)
    (γ : (pdABCohR (R := R) (TopCat.of X) A B).X n) :
    ((pdABMap (R := R) f A B A' B' hA' hB').f n γ).1
      = ((dualChainMap R (TopCat.of X') (TopCat.of X) (TopCat.ofHom f)).f n).hom γ.1 := by
  rw [pdABMap_f]
  rfl

/-- **Naturality of the Alexander–Whitney product `starAB`** on the `A+B` complexes: the pullback
of the product is the product of the pullbacks.  This is the cochain-level statement that
`Work.Whitney.relRelCupHMap_natural` descends to cohomology, and it is a restriction of the
naturality `Work.Cohomology.cupNatural` of the absolute cup product. -/
theorem pdABMap_starAB {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
    (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A) (hB' : ∀ x ∈ B', f x ∈ B)
    (m n : ℕ) (a : (relComplex R (TopCat.of X) A).X m) (b : (relComplex R (TopCat.of X) B).X n) :
    (pdABMap (R := R) f A B A' B' hA' hB').f (m+n)
        (starAB (R := R) (TopCat.of X) A B m n a b)
      = starAB (R := R) (TopCat.of X') A' B' m n
          (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hA' m a)
          (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hB' n b) := by
  apply Subtype.ext
  rw [pdABMap_coe, starAB_coe, starAB_coe, relMapLM_coe, relMapLM_coe]
  exact (cupNatural R (TopCat.toSSet.map (TopCat.ofHom f)) a.1 b.1).symm

/-- **The pullback of the `A+B` complex is compatible with the inclusion** `C^*(X,A∪B) → C^*(X,A+B)`:
the square of cochain maps commutes. -/
theorem pdABMap_comm {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
    (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A) (hB' : ∀ x ∈ B', f x ∈ B)
    (hmU : ∀ x ∈ A' ∪ B', f x ∈ A ∪ B) :
    relComplexMap (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) (A' ∪ B') (A ∪ B)
        (TopCat.ofHom f) hmU ≫ pdABInclRelR (R := R) (TopCat.of X') A' B'
      = pdABInclRelR (R := R) (TopCat.of X) A B ≫ pdABMap (R := R) f A B A' B' hA' hB' := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-! ## Cocycle lemmas -/

lemma cyclesMap_cocycleOfK {K L : CochainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {k : ℕ}
    (γ : (K.X k)) (h : ((K.d k (k+1)).hom) γ = 0)
    (h' : ((L.d k (k+1)).hom) ((φ.f k).hom γ) = 0) :
    (HomologicalComplex.cyclesMap φ k).hom (cocycleOfK K γ h)
      = cocycleOfK L ((φ.f k).hom γ) h' := by
  apply iCycles_injective_K L k
  rw [cyclesMap_i_apply_gen, iCycles_cocycleOfK, iCycles_cocycleOfK]

lemma homologyMap_cocycleOfK {K L : CochainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {k : ℕ}
    (γ : (K.X k)) (h : ((K.d k (k+1)).hom) γ = 0)
    (h' : ((L.d k (k+1)).hom) ((φ.f k).hom γ) = 0) :
    (HomologicalComplex.homologyMap φ k).hom ((K.homologyπ k).hom (cocycleOfK K γ h))
      = (L.homologyπ k).hom (cocycleOfK L ((φ.f k).hom γ) h') := by
  rw [homologyMap_homologyπ, cyclesMap_cocycleOfK]

lemma homologyπ_cocycleOfK_proof_irrel (K : CochainComplex (ModuleCat R) ℕ) {k : ℕ}
    (γ : (K.X k)) (h h' : ((K.d k (k+1)).hom) γ = 0) :
    (K.homologyπ k).hom (cocycleOfK K γ h) = (K.homologyπ k).hom (cocycleOfK K γ h') :=
  congrArg (fun z => (K.homologyπ k).hom z) (cocycleOfK_proof_irrel K γ h h')

lemma homologyπ_cocycleOfK_congr (K : CochainComplex (ModuleCat R) ℕ) {k : ℕ}
    {x y : (K.X k)} (hxy : x = y)
    (hx : ((K.d k (k+1)).hom) x = 0) (hy : ((K.d k (k+1)).hom) y = 0) :
    (K.homologyπ k).hom (cocycleOfK K x hx) = (K.homologyπ k).hom (cocycleOfK K y hy) := by
  subst hxy
  exact homologyπ_cocycleOfK_proof_irrel K x hx hy

/-! ## The pullback of the `A+B` complex on cocycles -/

lemma pdABMap_cocycle {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
    (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A) (hB' : ∀ x ∈ B', f x ∈ B)
    {k : ℕ} (γ : (pdABCohR (R := R) (TopCat.of X) A B).X k)
    (hγ : ((pdABCohR (R := R) (TopCat.of X) A B).d k (k+1)).hom γ = 0) :
    ((pdABCohR (R := R) (TopCat.of X') A' B').d k (k+1)).hom
      (((pdABMap (R := R) f A B A' B' hA' hB').f k).hom γ) = 0 := by
  have hcomm := HomologicalComplex.Hom.comm (pdABMap (R := R) f A B A' B' hA' hB') k (k+1)
  have h2 := congrArg (fun (g : (pdABCohR (R := R) (TopCat.of X) A B).X k ⟶
      (pdABCohR (R := R) (TopCat.of X') A' B').X (k+1)) => g.hom γ) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [hγ, map_zero] at h2
  exact h2

lemma pdABMap_homologyMap_cocycleOfK {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X]
    (f : C(X', X)) (A B : Set X) (A' B' : Set X') (hA' : ∀ x ∈ A', f x ∈ A)
    (hB' : ∀ x ∈ B', f x ∈ B) {k : ℕ} (γ : (pdABCohR (R := R) (TopCat.of X) A B).X k)
    (hγ : ((pdABCohR (R := R) (TopCat.of X) A B).d k (k+1)).hom γ = 0) :
    (HomologicalComplex.homologyMap (pdABMap (R := R) f A B A' B' hA' hB') k).hom
        ((HomologicalComplex.homologyπ (pdABCohR (R := R) (TopCat.of X) A B) k).hom
          (cocycleOfK (pdABCohR (R := R) (TopCat.of X) A B) γ hγ))
      = (HomologicalComplex.homologyπ (pdABCohR (R := R) (TopCat.of X') A' B') k).hom
          (cocycleOfK (pdABCohR (R := R) (TopCat.of X') A' B')
            ((pdABMap (R := R) f A B A' B' hA' hB').f k γ)
            (pdABMap_cocycle (R := R) f A B A' B' hA' hB' γ hγ)) :=
  homologyMap_cocycleOfK (pdABMap (R := R) f A B A' B' hA' hB') γ hγ
    (pdABMap_cocycle (R := R) f A B A' B' hA' hB' γ hγ)

/-! ## Naturality of `relRelCupHMap` -/

theorem relRelCupHMap_natural {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X]
    (f : C(X', X)) (A B : Set X) (A' B' : Set X') (hmA : ∀ x ∈ A', f x ∈ A)
    (hmB : ∀ x ∈ B', f x ∈ B) (m n : ℕ)
    (a : (relComplex R (TopCat.of X) A).homology m)
    (b : (relComplex R (TopCat.of X) B).homology n) :
    (HomologicalComplex.homologyMap (pdABMap (R := R) f A B A' B' hmA hmB) (m+n)).hom
        ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b)
      = (relRelCupHMap (R := R) (TopCat.of X') A' B' m n)
          ((HomologicalComplex.homologyMap (relComplexMap (R := R) (X₁ := TopCat.of X')
            (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hmA) m).hom a)
          ((HomologicalComplex.homologyMap (relComplexMap (R := R) (X₁ := TopCat.of X')
            (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hmB) n).hom b) := by
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf R (TopCat.of X) A m a
  obtain ⟨β, hβ, rfl⟩ := exists_relClassOf R (TopCat.of X) B n b
  have hα' : ((relComplex R (TopCat.of X) A).d m (m+1)).hom α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβ' : ((relComplex R (TopCat.of X) B).d n (n+1)).hom β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hstar : ((pdABCohR (R := R) (TopCat.of X) A B).d (m+n) (m+n+1)).hom
      (starAB (R := R) (TopCat.of X) A B m n α β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (TopCat.of X) A B) m n α β hα' hβ'
  have hα'' : relDiffLM R (TopCat.of X') A' m
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hmA m α) = 0 :=
    relDiffLM_relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hmA α hα
  have hβ'' : relDiffLM R (TopCat.of X') B' n
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hmB n β) = 0 :=
    relDiffLM_relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hmB β hβ
  have hα2 : ((relComplex R (TopCat.of X') A').d m (m+1)).hom
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hmA m α) = 0 := by
    rw [relComplex_d_apply]; exact hα''
  have hβ2 : ((relComplex R (TopCat.of X') B').d n (n+1)).hom
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hmB n β) = 0 := by
    rw [relComplex_d_apply]; exact hβ''
  have hstar2 : ((pdABCohR (R := R) (TopCat.of X') A' B').d (m+n) (m+n+1)).hom
      (starAB (R := R) (TopCat.of X') A' B' m n
        (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hmA m α)
        (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hmB n β)) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (TopCat.of X') A' B') m n _ _ hα2 hβ2
  rw [homologyMap_relComplexMap_relClassOf (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X)
      A' A (TopCat.ofHom f) hmA α hα,
    homologyMap_relComplexMap_relClassOf (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X)
      B' B (TopCat.ofHom f) hmB β hβ]
  rw [relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) A α hα hα',
    relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) B β hβ hβ']
  rw [relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X') A'
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hmA m α)
      hα'' hα2,
    relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X') B'
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hmB n β)
      hβ'' hβ2]
  rw [relRelCupHMap_apply (R := R) (TopCat.of X) A B m n α β hα' hβ' hstar]
  rw [pdABMap_homologyMap_cocycleOfK (R := R) f A B A' B' hmA hmB
    (starAB (R := R) (TopCat.of X) A B m n α β) hstar]
  rw [relRelCupHMap_apply (R := R) (TopCat.of X') A' B' m n
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) A' A (TopCat.ofHom f) hmA m α)
      (relMapLM (R := R) (X₁ := TopCat.of X') (X₂ := TopCat.of X) B' B (TopCat.ofHom f) hmB n β)
      hα2 hβ2 hstar2]
  exact homologyπ_cocycleOfK_congr (pdABCohR (R := R) (TopCat.of X') A' B')
    (pdABMap_starAB (R := R) f A B A' B' hmA hmB m n α β)
    (pdABMap_cocycle (R := R) f A B A' B' hmA hmB
      (starAB (R := R) (TopCat.of X) A B m n α β) hstar) hstar2

/-- **The canonical transport** `H^N(X,A+B) → H^N(X,A∪B)`: the inverse of the quasi-isomorphism
`pdABInclRelR : C^*(X,A∪B) → C^*(X,A+B)` on homology (for open `A B`).  Its defining property is
the gauge-fixing equation `pdABInvTransport_gauge`. -/
noncomputable def pdABInvTransport {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (N : ℕ) :
    (pdABCohR (R := R) (TopCat.of X) A B).homology N →ₗ[R] Work.Thom.RelCoh R N X (A ∪ B) := by
  haveI : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) N) :=
    pdABInclRelR_quasiIso (R := R) (M := TopCat.of X) A B hA hB N
  exact (CategoryTheory.inv (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) N)).hom

/-- **The gauge-fixing equation** of the canonical transport: `φ ∘ g = id`. -/
theorem pdABInvTransport_gauge {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (N : ℕ) (y : (pdABCohR (R := R) (TopCat.of X) A B).homology N) :
    (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) N).hom
      (pdABInvTransport A B hA hB N y) = y := by
  haveI : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) N) :=
    pdABInclRelR_quasiIso (R := R) (M := TopCat.of X) A B hA hB N
  exact IsIso.inv_hom_id_apply _ y

private lemma hom_injective_of_isIso {M N : ModuleCat R} (φ : M ⟶ N) [IsIso φ] :
    Function.Injective φ.hom := fun x y h => by
  rw [← IsIso.hom_inv_id_apply φ x, ← IsIso.hom_inv_id_apply φ y, h]

/-- **Naturality of the canonical transport**: the inverse of a natural quasi-isomorphism is
natural (the square commutes because `φ'` is injective). -/
theorem pdABInvTransport_natural {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X]
    (f : C(X', X)) (A B : Set X) (A' B' : Set X') (hA : IsOpen A) (hB : IsOpen B)
    (hA' : IsOpen A') (hB' : IsOpen B') (hmA : ∀ x ∈ A', f x ∈ A) (hmB : ∀ x ∈ B', f x ∈ B)
    (hmU : ∀ x ∈ A' ∪ B', f x ∈ A ∪ B) (N : ℕ)
    (y : (pdABCohR (R := R) (TopCat.of X) A B).homology N) :
    (HomologicalComplex.homologyMap (relComplexMap (R := R) (X₁ := TopCat.of X')
        (X₂ := TopCat.of X) (A' ∪ B') (A ∪ B) (TopCat.ofHom f) hmU) N).hom
      (pdABInvTransport A B hA hB N y)
      = pdABInvTransport A' B' hA' hB' N
          ((HomologicalComplex.homologyMap (pdABMap (R := R) f A B A' B' hmA hmB) N).hom y) := by
  haveI : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) N) :=
    pdABInclRelR_quasiIso (R := R) (M := TopCat.of X) A B hA hB N
  haveI : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X') A' B') N) :=
    pdABInclRelR_quasiIso (R := R) (M := TopCat.of X') A' B' hA' hB' N
  have hsq : (HomologicalComplex.homologyMap (relComplexMap (R := R) (X₁ := TopCat.of X')
        (X₂ := TopCat.of X) (A' ∪ B') (A ∪ B) (TopCat.ofHom f) hmU) N)
      ≫ (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X') A' B') N)
      = (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) N)
        ≫ (HomologicalComplex.homologyMap (pdABMap (R := R) f A B A' B' hmA hmB) N) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pdABMap_comm]
  have hsq' : ∀ z : Work.Thom.RelCoh R N X (A ∪ B),
      (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X') A' B') N).hom
        ((HomologicalComplex.homologyMap (relComplexMap (R := R) (X₁ := TopCat.of X')
          (X₂ := TopCat.of X) (A' ∪ B') (A ∪ B) (TopCat.ofHom f) hmU) N).hom z)
      = (HomologicalComplex.homologyMap (pdABMap (R := R) f A B A' B' hmA hmB) N).hom
          ((HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) N).hom z) := by
    intro z
    have h := congrArg (fun (g : (relComplex R (TopCat.of X) (A ∪ B)).homology N ⟶
        (pdABCohR (R := R) (TopCat.of X') A' B').homology N) => g.hom z) hsq
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  apply hom_injective_of_isIso (HomologicalComplex.homologyMap
    (pdABInclRelR (R := R) (TopCat.of X') A' B') N)
  rw [hsq' (pdABInvTransport A B hA hB N y),
    pdABInvTransport_gauge A B hA hB N y,
    pdABInvTransport_gauge A' B' hA' hB' N
      ((HomologicalComplex.homologyMap (pdABMap (R := R) f A B A' B' hmA hmB) N).hom y)]

/-- **The canonical relative–relative cup product** `H^m(X,A) → H^n(X,B) → H^{m+n}(X,A∪B)` for
open `A B ⊆ X`: the Alexander–Whitney product `Work.Whitney.relRelCupHMap` on the `A+B` complex,
transported to `C^*(X,A∪B)` along the **inverse** of the quasi-isomorphism
`C^*(X,A∪B) → C^*(X,A+B)` (`pdABInvTransport`, i.e. `CategoryTheory.inv` of `pdABInclRelR` on
homology).  Unlike `Work.Whitney.relRelCup`, this operation is *computable*: it is given by an
explicit transport, not by an existential. -/
noncomputable def relRelCupOpen : ∀ {X : Type} [TopologicalSpace X] (A B : Set X),
    IsOpen A → IsOpen B → (m n : ℕ) →
      Work.Thom.RelCoh R m X A →ₗ[R] Work.Thom.RelCoh R n X B →ₗ[R]
        Work.Thom.RelCoh R (m + n) X (A ∪ B) :=
  fun {X} _ A B hA hB m n => relRelCupG A B m n (pdABInvTransport A B hA hB (m + n))

/-- The defining formula of `Work.Whitney.relRelCupOpen`. -/
@[simp] theorem relRelCupOpen_apply {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (m n : ℕ) (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCupOpen A B hA hB m n a b
      = relRelCupG A B m n (pdABInvTransport A B hA hB (m + n)) a b := rfl

/-- **The computation rule of the canonical relative–relative cup**: forgetting the relative data
recovers the absolute cup product of the two classes. -/
theorem relRelCupOpen_relToAbs {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (m n : ℕ) (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (relRelCupOpen A B hA hB m n a b)
      = Work.Cohomology.cupH' R (Work.Whitney.ssB X) m n
          ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b) :=
  relRelCupG_relToAbs A B m n (pdABInvTransport A B hA hB (m + n))
    (pdABInvTransport_gauge A B hA hB (m + n)) a b

/-- **Naturality of the canonical relative–relative cup** under a continuous map of pairs
`f : X' → X` with `f '' A' ⊆ A` and `f '' B' ⊆ B`. -/
theorem relRelCupOpen_natural {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X]
    (f : C(X', X)) (A B : Set X) (A' B' : Set X') (hA : IsOpen A) (hB : IsOpen B)
    (hA' : IsOpen A') (hB' : IsOpen B') (hmA : ∀ x ∈ A', f x ∈ A) (hmB : ∀ x ∈ B', f x ∈ B)
    (hmU : ∀ x ∈ A' ∪ B', f x ∈ A ∪ B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relCohMap f (A' ∪ B') (A ∪ B) hmU R (m + n)).hom (relRelCupOpen A B hA hB m n a b)
      = relRelCupOpen A' B' hA' hB' m n
          ((Work.Thom.relCohMap f A' A hmA R m).hom a)
          ((Work.Thom.relCohMap f B' B hmB R n).hom b) := by
  rw [relRelCupOpen_apply, relRelCupOpen_apply, relRelCupG_apply, relRelCupG_apply]
  rw [pdABInvTransport_natural f A B A' B' hA hB hA' hB' hmA hmB hmU (m + n)
    ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b)]
  rw [relRelCupHMap_natural f A B A' B' hmA hmB m n a b]

/-- There is a relative–relative cup product (for open `A`, `B ⊆ X`) with (i) the computation rule
`relToAbs (a ⌣ b) = relToAbs a ⌣ relToAbs b` and (ii) **naturality** under a continuous map of pairs
`f : X' → X` with `f '' A' ⊆ A`, `f '' B' ⊆ B`.

The witness is the *canonical* cup `Work.Whitney.relRelCupOpen` (the Alexander–Whitney product on
the `A+B` complex transported along the inverse of the quasi-isomorphism
`C^*(X,A∪B) → C^*(X,A+B)`); it is **not** `Classical.choose` of `Work.Whitney.exists_relRelCup`,
whose defining property (i) alone does not determine it (`relToAbs` is not injective). -/
theorem relRelCup_natural (R : Type) [CommRing R] :
    ∃ cup : ∀ {X : Type} [TopologicalSpace X] (A B : Set X), IsOpen A → IsOpen B → (m n : ℕ) →
        Work.Thom.RelCoh R m X A →ₗ[R] Work.Thom.RelCoh R n X B →ₗ[R]
          Work.Thom.RelCoh R (m + n) X (A ∪ B),
      (∀ {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
        (m n : ℕ) (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B),
        (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (cup A B hA hB m n a b)
          = Work.Cohomology.cupH' R (Work.Whitney.ssB X) m n
              ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b))
      ∧ (∀ {X' X : Type} [TopologicalSpace X'] [TopologicalSpace X] (f : C(X', X))
          (A B : Set X) (A' B' : Set X') (hA : IsOpen A) (hB : IsOpen B)
          (hA' : IsOpen A') (hB' : IsOpen B')
          (hmA : ∀ x ∈ A', f x ∈ A) (hmB : ∀ x ∈ B', f x ∈ B)
          (hmU : ∀ x ∈ A' ∪ B', f x ∈ A ∪ B)
          (m n : ℕ) (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B),
        (Work.Thom.relCohMap f (A' ∪ B') (A ∪ B) hmU R (m + n)).hom (cup A B hA hB m n a b)
          = cup A' B' hA' hB' m n
              ((Work.Thom.relCohMap f A' A hmA R m).hom a)
              ((Work.Thom.relCohMap f B' B hmB R n).hom b)) :=
  ⟨relRelCupOpen, relRelCupOpen_relToAbs, relRelCupOpen_natural⟩

end
