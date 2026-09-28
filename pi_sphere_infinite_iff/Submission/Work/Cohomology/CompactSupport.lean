import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.Kronecker

set_option synthInstance.maxHeartbeats 400000


/-!
# Compactly supported singular cohomology

The *compactly supported* cohomology `H^*_c(X;R)` is the cohomology of the subcomplex of singular
cochains whose support is contained in a compact set:

  `C^k_c(X;R) = { φ : C_k(X) →ₗ R | ∃ K ⊆ X compact, φ(σ) = 0 for every singular `k`-simplex `σ`
    whose image is disjoint from `K` }`.

This is the (co)homological input of Poincaré duality for non-compact manifolds:
for an oriented `n`-manifold without boundary the cap product with a *locally finite* fundamental
class is an isomorphism `H^k_c(M;R) ≅ H_{n-k}(M;R)`, and for a closed manifold the induction proving
`H^k(M;R) ≅ H_{n-k}(M;R)` runs over an open cover, whose pieces are open subsets of `ℝⁿ` — precisely
the case where the compactly supported version is needed.

## Main definitions

* `simplexRange X σ` — the image of a singular simplex, a compact subset of `X`;
* `compactSupport R X k` — the submodule of `k`-cochains supported in a compact set;
* `compactSupportedComplex R X` — the resulting cochain complex (`cochainDiff` preserves the
  submodule because the faces of a simplex have image contained in the image of the simplex);
* `compactCohomology R X k` — its cohomology, i.e. `H^k_c(X;R)`.

## Main results

* `simplexRange_face` — the image of a face is contained in the image of the simplex;
* `mem_compactSupport` — the defining property;
* `compactSupport_eq_top_of_compact` — if `X` is compact then every cochain has compact support;
* `cochainDiff_mem_compactSupport` — the coboundary of a compactly supported cochain is compactly
  supported.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

open TopCat in
/-- **The image of a singular simplex**, as a subset of the space. -/
def simplexRange (X : TopCat) {k : ℕ} (σ : (TopCat.toSSet.obj X) _⦋k⦌) : Set X :=
  Set.range (TopCat.toSSetObjEquivT X (Opposite.op ⦋k⦌) σ)

open TopCat in
/-- The image of a singular simplex is compact. -/
theorem isCompact_simplexRange (X : TopCat) {k : ℕ} (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    IsCompact (simplexRange X σ) :=
  isCompact_range (TopCat.toSSetObjEquivT X (Opposite.op ⦋k⦌) σ).continuous

open TopCat in
/-- **The image of a face is contained in the image of the simplex.** -/
theorem simplexRange_face (X : TopCat) {k : ℕ} (i : Fin (k + 2))
    (σ : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    simplexRange X ((TopCat.toSSet.obj X).δ i σ) ⊆ simplexRange X σ := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨stdSimplex.map i.succAbove z, (TopCat.toSSetObjEquivT_δ_apply (X := X) σ i z).symm⟩

open TopCat in
/-- **The submodule of compactly supported `k`-cochains.** -/
def compactSupport (X : TopCat) (k : ℕ) :
    Submodule R (Cochain R (TopCat.toSSet.obj X) k) where
  carrier := {φ | ∃ K : Set X, IsCompact K ∧
    ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, Disjoint (simplexRange X σ) K →
      φ (genElt R (TopCat.toSSet.obj X) σ) = 0}
  zero_mem' := ⟨∅, isCompact_empty, by intro σ _; simp⟩
  add_mem' := by
    intro φ ψ hφ hψ
    obtain ⟨K, hK, hK'⟩ := hφ
    obtain ⟨L, hL, hL'⟩ := hψ
    refine ⟨K ∪ L, hK.union hL, ?_⟩
    intro σ hσ
    change φ (genElt R (TopCat.toSSet.obj X) σ) + ψ (genElt R (TopCat.toSSet.obj X) σ) = 0
    rw [hK' σ (Disjoint.mono_right Set.subset_union_left hσ),
      hL' σ (Disjoint.mono_right Set.subset_union_right hσ), add_zero]
  smul_mem' := by
    intro r φ hφ
    obtain ⟨K, hK, hK'⟩ := hφ
    refine ⟨K, hK, ?_⟩
    intro σ hσ
    change r • φ (genElt R (TopCat.toSSet.obj X) σ) = 0
    rw [hK' σ hσ, smul_zero]

open TopCat in
/-- The defining property of the compactly supported cochains. -/
theorem mem_compactSupport {X : TopCat} {k : ℕ} {φ : Cochain R (TopCat.toSSet.obj X) k} :
    φ ∈ compactSupport R X k ↔ ∃ K : Set X, IsCompact K ∧
      ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, Disjoint (simplexRange X σ) K →
        φ (genElt R (TopCat.toSSet.obj X) σ) = 0 :=
  Iff.rfl

open TopCat in
/-- The coboundary of a compactly supported cochain is compactly supported: the faces of a simplex
have image contained in the image of the simplex, so a cochain vanishing away from a compact `K` has
coboundary vanishing away from `K`. -/
theorem cochainDiff_mem_compactSupport (X : TopCat) {k : ℕ}
    {φ : Cochain R (TopCat.toSSet.obj X) k} (hφ : φ ∈ compactSupport R X k) :
    cochainDiff R (TopCat.toSSet.obj X) φ ∈ compactSupport R X (k + 1) := by
  obtain ⟨K, hK, hK'⟩ := hφ
  refine ⟨K, hK, ?_⟩
  intro σ hσ
  show genEval R (TopCat.toSSet.obj X) (cochainDiff R (TopCat.toSSet.obj X) φ) σ = 0
  rw [cochainDiff_apply, capd_d_gen]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  have h := hK' ((TopCat.toSSet.obj X).δ i σ)
    (Disjoint.mono_left (simplexRange_face X i σ) hσ)
  simp only [genElt] at h
  rw [h, smul_zero]

open TopCat in
/-- **For a compact space every cochain has compact support.** -/
theorem mem_compactSupport_of_compact (X : TopCat) [CompactSpace X] {k : ℕ}
    (φ : Cochain R (TopCat.toSSet.obj X) k) : φ ∈ compactSupport R X k := by
  refine ⟨Set.univ, isCompact_univ, ?_⟩
  intro σ hσ
  have hne : (simplexRange X σ).Nonempty :=
    ⟨(TopCat.toSSetObjEquivT X (Opposite.op ⦋k⦌) σ) (stdSimplex.vertex 0), Set.mem_range_self _⟩
  exact absurd (Set.disjoint_univ.mp hσ) hne.ne_empty

open TopCat in
/-- **For a compact space the compactly supported cochains are all cochains.** -/
theorem compactSupport_eq_top_of_compact (X : TopCat) [CompactSpace X] (k : ℕ) :
    compactSupport R X k = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_compactSupport_of_compact R X _

/-- The coboundary of a coboundary of a cochain vanishes (the cochain complex is a complex). -/
theorem cochainDiff_cochainDiff (X : SSet) {k : ℕ} (α : Cochain R X k) :
    cochainDiff R X (cochainDiff R X α) = 0 := by
  rw [cochainDiff, cochainDiff, LinearMap.comp_assoc]
  have h : (((X.chainComplex (ModuleCat.of R R)).d (k + 1) k).hom.comp
      ((X.chainComplex (ModuleCat.of R R)).d (k + 2) (k + 1)).hom) = 0 := by
    rw [← ModuleCat.hom_comp, HomologicalComplex.d_comp_d, ModuleCat.hom_zero]
  rw [h, LinearMap.comp_zero]

open TopCat in
/-- The coboundary as a linear map between the modules of compactly supported cochains. -/
def compactSupportD (X : TopCat) (k : ℕ) :
    ↥(compactSupport R X k) →ₗ[R] ↥(compactSupport R X (k + 1)) where
  toFun φ := ⟨cochainDiff R (TopCat.toSSet.obj X) φ.1,
    cochainDiff_mem_compactSupport R X φ.2⟩
  map_add' φ ψ := by
    ext1
    show cochainDiff R (TopCat.toSSet.obj X) (φ.1 + ψ.1) = _
    rw [← cochainDiffLM_apply, map_add, cochainDiffLM_apply, cochainDiffLM_apply]
    simp
  map_smul' r φ := by
    ext1
    show cochainDiff R (TopCat.toSSet.obj X) (r • φ.1) = _
    rw [← cochainDiffLM_apply, map_smul, cochainDiffLM_apply]
    simp

open TopCat in
/-- **The compactly supported cochain complex** of a topological space: the subcomplex of the
singular cochain complex formed by the cochains whose support is contained in a compact set. -/
def compactSupportedComplex (X : TopCat) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun k => ModuleCat.of R ↥(compactSupport R X k))
    (fun k => ModuleCat.ofHom (compactSupportD R X k))
    (fun k => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change compactSupportD R X (k + 1) (compactSupportD R X k φ) = 0
      ext1
      change cochainDiff R (TopCat.toSSet.obj X)
        (cochainDiff R (TopCat.toSSet.obj X) φ.1) = 0
      exact cochainDiff_cochainDiff R (TopCat.toSSet.obj X) φ.1)

open TopCat in
/-- **The compactly supported cohomology** `H^k_c(X;R)` of a topological space. -/
abbrev compactCohomology (X : TopCat) (k : ℕ) : ModuleCat R :=
  (compactSupportedComplex R X).homology k

end

end Work.Cohomology
