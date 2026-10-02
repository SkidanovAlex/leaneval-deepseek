import Mathlib
import Submission.Work.ThomBordism.RelDuality.CollapseData
import Submission.Work.ThomBordism.RelDuality.Defs
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.homotopyInvariance
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.isIso_homologyMap_tau1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomological transfer `H^k(M,∂M) → H^k(M,Kᶜ)` along a boundary collapse

This file proves the lemma `Work.ThomBordism.RelDuality.relClass_lift_of_boundaryCollapse`: a
*boundary collapse datum* `C : BoundaryCollapse M` on a compact charted `9`-manifold with boundary
supplies a compact `K ⊆ int M` for which the restriction

`relRestrOffBdry K hK : H^k(M, Kᶜ) ⟶ H^k(M, ∂M)`

is *surjective* in every degree `k`.

## The argument

* `relLiftΨ C`  — the map of pairs `(M,∂M) → (M,Kᶜ)` induced by the collapsing map `ψ`;
* `relLiftΨ₀ C` — the map of pairs `(M,∂M) → (M,∂M)` induced by `ψ`;
* `relLiftΨ_comp_restr` — the key identity `relLiftΨ ≫ relRestrOffBdry = relLiftΨ₀`;
* `ψ` is homotopic to the identity of `M` (`C.H`) and fixes `∂M`, so the induced map `ψ^*` is an
  isomorphism on `H^*(M;ℤ) = H^*(M,∅;ℤ)` (`relLift_isIso_abs`) and, `ψ` fixing `∂M`, on
  `H^*(∂M;ℤ)` (`relLift_isIso_bdry`).  The five lemma applied to the map `relLiftPairMap` of short
  exact sequences of the pair `(M,∂M)` (`pairShort_shortExact`) then shows that `relLiftΨ₀` is an
  isomorphism on `H^*(M,∂M;ℤ)` (`relLift_isIso_rel`, via
  `Work.Cohomology.isIso_homologyMap_tau1`);
* hence `relRestrOffBdry` is surjective: a preimage of `u` under `(relLiftΨ₀)_*` is pushed forward
  by `relLiftΨ` to a class mapping to `u`.

Geometrically this is the "compactly supported cohomology computes relative cohomology" half of
Hatcher's Theorem 3.43.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold unitInterval

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]

/-- **The map of pairs `(M,∂M) → (M,Kᶜ)` induced by the collapsing map.** -/
noncomputable def relLiftΨ (C : BoundaryCollapse M) :
    Work.Cohomology.relComplex ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) ⟶
      Work.Cohomology.relComplex ℤ (TopCat.of M) C.Kᶜ :=
  Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of M) (X₂ := TopCat.of M) C.Kᶜ
    ((modelWithCornersEuclideanHalfSpace 9).boundary M) (TopCat.ofHom C.ψ)
    (fun x hx => C.ψ_compl x hx)

/-- **The map of pairs `(M,∂M) → (M,∂M)` induced by the collapsing map.** -/
noncomputable def relLiftΨ₀ (C : BoundaryCollapse M) :
    Work.Cohomology.relComplex ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) ⟶
      Work.Cohomology.relComplex ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) :=
  Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of M) (X₂ := TopCat.of M)
    ((modelWithCornersEuclideanHalfSpace 9).boundary M)
    ((modelWithCornersEuclideanHalfSpace 9).boundary M) (TopCat.ofHom C.ψ)
    (fun x hx => C.ψ_bdry x hx)

/-- The boundary is contained in the complement of the collapsed set. -/
theorem relLift_bdry_subset_compl (C : BoundaryCollapse M) :
    ((modelWithCornersEuclideanHalfSpace 9).boundary M) ⊆ C.Kᶜ :=
  fun x hx hxK => C.hK hxK hx

/-- `relRestrOffBdry` is compatible with the inclusions of the relative cochain complexes into the
absolute ones. -/
theorem relLift_restr_comp_relIncl (C : BoundaryCollapse M) :
    relRestrOffBdry (M := M) C.K C.hK ≫
        Work.Cohomology.relIncl ℤ (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace 9).boundary M)
      = Work.Cohomology.relIncl ℤ (TopCat.of M) C.Kᶜ := by
  have h := @Work.Cohomology.relComplexMap_comp_relIncl ℤ _
    (TopCat.of M) (TopCat.of M)
    ((modelWithCornersEuclideanHalfSpace 9).boundary M) C.Kᶜ (𝟙 (TopCat.of M))
    (fun x hx => relLift_bdry_subset_compl C hx)
  unfold relRestrOffBdry
  rw [h, Work.Cohomology.dualChainMap_id, Category.comp_id]

/-- **The key identity**: the map induced by the collapse, followed by the restriction off the
boundary, is the map induced by the collapse on the pair `(M,∂M)`. -/
theorem relLiftΨ_comp_restr (C : BoundaryCollapse M) :
    relLiftΨ C ≫ relRestrOffBdry (M := M) C.K C.hK = relLiftΨ₀ C := by
  haveI hmono := Work.Cohomology.capRel_relIncl_mono (X := TopCat.of M)
    ((modelWithCornersEuclideanHalfSpace 9).boundary M)
  refine (cancel_mono (Work.Cohomology.relIncl ℤ (TopCat.of M)
    ((modelWithCornersEuclideanHalfSpace 9).boundary M))).1 ?_
  have hleft : (relLiftΨ C ≫ relRestrOffBdry (M := M) C.K C.hK) ≫
      Work.Cohomology.relIncl ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M)
      = Work.Cohomology.relIncl ℤ (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace 9).boundary M) ≫
        Work.Cohomology.dualChainMap ℤ (TopCat.of M) (TopCat.of M) (TopCat.ofHom C.ψ) := by
    rw [Category.assoc, relLift_restr_comp_relIncl C]
    exact @Work.Cohomology.relComplexMap_comp_relIncl ℤ _ (TopCat.of M) (TopCat.of M)
      C.Kᶜ ((modelWithCornersEuclideanHalfSpace 9).boundary M) (TopCat.ofHom C.ψ)
      (fun x hx => C.ψ_compl x hx)
  have hright : relLiftΨ₀ C ≫ Work.Cohomology.relIncl ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M)
      = Work.Cohomology.relIncl ℤ (TopCat.of M)
          ((modelWithCornersEuclideanHalfSpace 9).boundary M) ≫
        Work.Cohomology.dualChainMap ℤ (TopCat.of M) (TopCat.of M) (TopCat.ofHom C.ψ) :=
    @Work.Cohomology.relComplexMap_comp_relIncl ℤ _ (TopCat.of M) (TopCat.of M)
      ((modelWithCornersEuclideanHalfSpace 9).boundary M)
      ((modelWithCornersEuclideanHalfSpace 9).boundary M) (TopCat.ofHom C.ψ)
      (fun x hx => C.ψ_bdry x hx)
  rw [hleft, hright]

/-- The map induced by `ψ` on the boundary is the identity, because `ψ` fixes `∂M` pointwise. -/
theorem relLift_relMapSub_eq_id (C : BoundaryCollapse M) :
    Work.Cohomology.relMapSub ((modelWithCornersEuclideanHalfSpace 9).boundary M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) (TopCat.ofHom C.ψ)
        (fun x hx => C.ψ_bdry x hx)
      = 𝟙 (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary M)) := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  exact C.ψ_fix z.1 z.2

/-- The pullback along the collapsing map is an isomorphism on the absolute cohomology of `M`,
because `ψ` is homotopic to the identity. -/
theorem relLift_isIso_abs (C : BoundaryCollapse M) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ
      (TopCat.of M) (TopCat.of M) (TopCat.ofHom C.ψ)) n) := by
  have hhom : Work.Cohomology.singularCohomologyMap ℤ (TopCat.of M) (TopCat.of M)
      (TopCat.ofHom C.ψ) n
      = 𝟙 (Work.Cohomology.singularCohomology ℤ n (TopCat.of M)) := by
    rw [← Work.Cohomology.homotopyInvariance ℤ (TopCat.of M) (TopCat.of M) C.H n]
    exact Work.Cohomology.singularCohomologyMap_id (R := ℤ) (X := TopCat.of M) n
  have hhom' : HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ
      (TopCat.of M) (TopCat.of M) (TopCat.ofHom C.ψ)) n
      = 𝟙 (Work.Cohomology.singularCohomology ℤ n (TopCat.of M)) := hhom
  exact hhom' ▸ IsIso.id (Work.Cohomology.singularCohomology ℤ n (TopCat.of M))

/-- The pullback along the collapsing map is an isomorphism on the cohomology of the boundary,
because `ψ` fixes `∂M`. -/
theorem relLift_isIso_bdry (C : BoundaryCollapse M) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ
      (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary M))
      (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary M))
      (Work.Cohomology.relMapSub ((modelWithCornersEuclideanHalfSpace 9).boundary M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M) (TopCat.ofHom C.ψ)
        (fun x hx => C.ψ_bdry x hx))) n) := by
  rw [relLift_relMapSub_eq_id C, Work.Cohomology.dualChainMap_id,
    HomologicalComplex.homologyMap_id]
  exact IsIso.id (Work.Cohomology.singularCohomology ℤ n
    (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary M)))

/-- **The five lemma step**: the map induced by the collapse on `H^*(M,∂M;ℤ)` is an isomorphism. -/
theorem relLift_isIso_rel (C : BoundaryCollapse M) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (relLiftΨ₀ C) n) := by
  classical
  let X : TopCat := TopCat.of M
  let A₁ : Set X := (modelWithCornersEuclideanHalfSpace 9).boundary M
  have h' : ∀ x ∈ A₁, (TopCat.ofHom C.ψ) x ∈ A₁ := fun x hx => C.ψ_bdry x hx
  let φ : Work.Cohomology.pairShort ℤ X A₁ ⟶ Work.Cohomology.pairShort ℤ X A₁ :=
    ShortComplex.homMk (Work.Cohomology.relComplexMap ℤ A₁ A₁ (TopCat.ofHom C.ψ) h')
      (Work.Cohomology.dualChainMap ℤ X X (TopCat.ofHom C.ψ))
      (Work.Cohomology.dualChainMap ℤ (TopCat.of ↥A₁) (TopCat.of ↥A₁)
        (Work.Cohomology.relMapSub A₁ A₁ (TopCat.ofHom C.ψ) h'))
      (by
        show Work.Cohomology.relComplexMap ℤ A₁ A₁ (TopCat.ofHom C.ψ) h' ≫
            Work.Cohomology.relIncl ℤ X A₁
          = Work.Cohomology.relIncl ℤ X A₁ ≫
              Work.Cohomology.dualChainMap ℤ X X (TopCat.ofHom C.ψ)
        exact Work.Cohomology.relComplexMap_comp_relIncl (R := ℤ) A₁ A₁ (TopCat.ofHom C.ψ) h')
      (by
        show Work.Cohomology.dualChainMap ℤ X X (TopCat.ofHom C.ψ) ≫
            Work.Cohomology.restr ℤ X A₁
          = Work.Cohomology.restr ℤ X A₁ ≫ Work.Cohomology.dualChainMap ℤ
              (TopCat.of ↥A₁) (TopCat.of ↥A₁)
              (Work.Cohomology.relMapSub A₁ A₁ (TopCat.ofHom C.ψ) h')
        exact Work.Cohomology.dualChainMap_restr_comp ℤ A₁ A₁ (TopCat.ofHom C.ψ) h')
  have h₂ : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₂ k) :=
    fun k => relLift_isIso_abs C k
  have h₃ : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₃ k) :=
    fun k => relLift_isIso_bdry C k
  have hmain := Work.Cohomology.isIso_homologyMap_tau1 ℤ φ
    (Work.Cohomology.pairShort_shortExact ℤ X A₁)
    (Work.Cohomology.pairShort_shortExact ℤ X A₁) h₂ h₃ n
  exact hmain

end

/-- **The transfer of relative cohomology classes along a boundary collapse.**  A boundary collapse
datum on `M` produces a compact `K ⊆ int M` such that every class of `H^k(M,∂M;ℤ)` is the image of
a class of `H^k(M,Kᶜ;ℤ)` under the restriction `relRestrOffBdry`.

This is the cohomological half of the comparison `H^k(M,∂M) ≅ H^k_c(int M)` (Hatcher, Theorem
3.43), stated for the `K` produced by the collapse datum. -/
theorem relClass_lift_of_boundaryCollapse {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 9) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]
    (C : BoundaryCollapse M) (k : ℕ) :
    ∀ u : (Work.Cohomology.relComplex ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M)).homology k,
      ∃ (K : Set M) (hK : K ⊆ {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}),
        IsCompact K ∧
        ∃ x : (Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ)).homology k,
          (HomologicalComplex.homologyMap
            (Work.ThomBordism.relRestrOffBdry (M := M) K hK) k) x = u := by
  intro u
  refine ⟨C.K, C.hK, C.hKc, ?_⟩
  haveI hiso : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relLiftΨ₀ C) k) := relLift_isIso_rel C k
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap (relLiftΨ₀ C) k) :=
    (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap (relLiftΨ₀ C) k)).2
  obtain ⟨y, hy⟩ := hsurj u
  refine ⟨(HomologicalComplex.homologyMap (relLiftΨ C) k) y, ?_⟩
  have hcomp : (HomologicalComplex.homologyMap (relLiftΨ C) k ≫
      HomologicalComplex.homologyMap (relRestrOffBdry (M := M) C.K C.hK) k) y = u := by
    rw [← HomologicalComplex.homologyMap_comp, relLiftΨ_comp_restr C]
    exact hy
  simpa only [ModuleCat.comp_apply] using hcomp

end Work.ThomBordism.RelDuality
