import Mathlib
import Submission.Work.Serre.csrDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cell step: relative homology depends only on the pair

The main result of this file is `Work.Serre.csrRelIso`: for `A ⊆ B ⊆ X`, if the pair `(B, A)` has
vanishing rational relative homology in every degree, then the map of pairs induced by the identity
of `X` is an isomorphism `H_m(X, A; ℚ) → H_m(X, B; ℚ)`.

The proof is the five lemma for the map of the long exact sequences of the pairs `(X,A)` and
`(X,B)`: the map of short exact sequences of chain complexes

`0 ⟶ C_*(A;ℚ) ⟶ C_*(X;ℚ) ⟶ C_*(X,A;ℚ) ⟶ 0`
`        ↓                 ↓                 ↓`
`0 ⟶ C_*(B;ℚ) ⟶ C_*(X;ℚ) ⟶ C_*(X,B;ℚ) ⟶ 0`

has two quasi-isomorphisms among its first two components (the identity of `C_*(X;ℚ)` and the
inclusion `C_*(A;ℚ) → C_*(B;ℚ)`, which is a quasi-isomorphism because `H_*(B,A;ℚ) = 0`), so by
`HomologicalComplex.HomologySequence.quasiIso_τ₃` the third one is a quasi-isomorphism as well.

The inclusion `C_*(A;ℚ) → C_*(B;ℚ)` is a quasi-isomorphism because it sits in the short exact
sequence of the pair `(B,A)`, whose third term is acyclic; the identification of the two models of
the chains of `A` (as a subspace of `X`, and as the subset `{x : B | (x : X) ∈ A}` of `B`) is by the
canonical homeomorphism `subtypeHomeo`.
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-! ## The inclusion of singular chains of a smaller subset into a larger one -/

/-- The inclusion of singular chains `C_*(A;R) ⟶ C_*(B;R)` induced by `A ⊆ B ⊆ X`. -/
def relChainsRInclSub (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (A B : Set X) (hAB : A ⊆ B) :
    Work.Cohomology.singularChains R (TopCat.of A) ⟶
      Work.Cohomology.singularChains R (TopCat.of B) :=
  Work.Cohomology.chainMap R (TopCat.of A) (TopCat.of B)
    (TopCat.ofHom ⟨fun x => ⟨x.1, hAB x.2⟩, by fun_prop⟩)

/-- Functoriality of `chainMap` with general coefficients. -/
theorem chainMap_compR (R : Type) [CommRing R] {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.Cohomology.chainMap R X Y f ≫ Work.Cohomology.chainMap R Y Z g =
      Work.Cohomology.chainMap R X Z (f ≫ g) :=
  (Functor.map_comp _ _ _).symm

/-- The inclusion of chains factors through the inclusion `A ⊆ B`. -/
theorem relChainsRInclSub_comp (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (A B : Set X) (hAB : A ⊆ B) :
    relChainsRInclSub R A B hAB ≫ Work.StemsB.relChainsRIncl R (TopCat.of X) B =
      Work.StemsB.relChainsRIncl R (TopCat.of X) A := by
  rw [relChainsRInclSub, Work.StemsB.relChainsRIncl, Work.StemsB.relChainsRIncl, chainMap_compR]
  congr 1

/-! ## The two models of the chains of `A` -/

/-- The canonical homeomorphism `A ≃ₜ {x : ↥B | (x : X) ∈ A}` for `A ⊆ B`. -/
def subtypeHomeo {X : Type} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B) :
    ↥A ≃ₜ {x : ↥B | (x : X) ∈ A} where
  toFun a := ⟨⟨a.1, hAB a.2⟩, a.2⟩
  invFun y := ⟨(y.1 : X), y.2⟩
  left_inv a := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun a => hAB a.2)) (fun a => a.2)
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

/-- The homeomorphism of the previous definition, followed by the inclusion of `{x : ↥B | (x : X)
∈ A}` into `B`, is the canonical inclusion `A → B`. -/
theorem subtypeHomeo_square {X : Type} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B) :
    (TopCat.isoOfHomeo (subtypeHomeo A B hAB)).hom ≫
        Work.Cohomology.subtypeIncl (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}
      = TopCat.ofHom (⟨fun x : A => ⟨x.1, hAB x.2⟩, by fun_prop⟩ : C(A, B)) := by
  apply TopCat.hom_ext
  ext a
  rfl

/-! ## Acyclic short exact sequences -/

/-- If the third term of a short exact sequence of chain complexes has vanishing homology in every
degree, then the first map is a quasi-isomorphism: in the long exact sequence the map
`H_k(X₁) → H_k(X₂)` has zero kernel (exactness at `X₂`) and its image is the kernel of the
connecting map to `H_{k-1}(X₁)`, which is zero (exactness at `X₃`). -/
theorem isIso_homologyMap_f_of_isZero {S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)}
    (hS : S.ShortExact) (h : ∀ j, IsZero (S.X₃.homology j)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap S.f k) := by
  haveI hmono : Mono (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.mono_g (hS.homology_exact₁ (k+1) k (by simp [ComplexShape.down]))
      (IsZero.eq_zero_of_src (h (k+1)) _)
  haveI hepi : Epi (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.epi_f (hS.homology_exact₂ k) (IsZero.eq_zero_of_tgt (h k) _)
  exact isIso_of_mono_of_epi _

/-- **The inclusion of a subspace is a quasi-isomorphism when the relative homology vanishes**: if
`H_*(X,A;ℚ) = 0` then `C_*(A;ℚ) → C_*(X;ℚ)` is a quasi-isomorphism. -/
theorem quasiIso_relChainsRIncl_of_isZero (X : TopCat) (A : Set X)
    (h : ∀ j, IsZero ((Work.StemsB.relChainsR ℚ X A).homology j)) :
    QuasiIso (Work.StemsB.relChainsRIncl ℚ X A) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_f_of_isZero (Work.StemsB.relChainsR_shortExact ℚ X A) h k

/-! ## The inclusion `A → B` in the `X`-model -/

/-- **The inclusion `C_*(A;ℚ) → C_*(B;ℚ)` (both as subspaces of `X`) is a quasi-isomorphism as
soon as the relative homology `H_*(B,A;ℚ)` (in the model in which `A` is a subset of `B`)
vanishes.**  The two models of the chains of `A` are compared by the homeomorphism
`subtypeHomeo`. -/
theorem quasiIso_relChainsRInclSub {X : Type} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B)
    (h : ∀ j, IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of ↥B)
      {x : ↥B | (x : X) ∈ A}).homology j)) :
    QuasiIso (relChainsRInclSub ℚ A B hAB) := by
  have hq1 : QuasiIso (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}) :=
    quasiIso_relChainsRIncl_of_isZero _ _ h
  have heq : relChainsRInclSub ℚ A B hAB =
      ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
          (TopCat.isoOfHomeo (subtypeHomeo A B hAB)).hom
        ≫ Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A} := by
    rw [Work.StemsB.relChainsRIncl, ← Functor.map_comp, subtypeHomeo_square]
    rfl
  rw [heq]
  haveI := hq1
  exact inferInstance

/-! ## The projection formula for a map of pairs -/

/-- The projection onto `C_*(Y,B;ℚ)` of a map of relative chain complexes induced by a map of
pairs. -/
theorem cokernel_π_relChainsRPairMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫ relChainsRPairMap A B g hg
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g) ≫
        cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B) := by
  rw [relChainsRPairMap, csrRelMapOf]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-! ## The main result -/

/-- **Relative homology depends only on the pair, up to the natural comparison.**  If `A ⊆ B ⊆ X` and the pair `(B, A)` has vanishing rational relative homology in every degree, then the identity of `X` induces an isomorphism `H_m(X, A; ℚ) → H_m(X, B; ℚ)` for every `m`.  (Both pairs sit in the long exact sequences of `(X,A)` and `(X,B)`, related through the pair `(B,A)`: a five-homomorphism argument.) -/
theorem csrRelIso {X : Type} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B) (h : ∀ m : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}).homology m)) (m : ℕ) : CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B (ContinuousMap.id X) (by intro x hx; exact hAB hx)) m) := by
  let τ₁ : Work.Cohomology.singularChains ℚ (TopCat.of A) ⟶
      Work.Cohomology.singularChains ℚ (TopCat.of B) := relChainsRInclSub ℚ A B hAB
  let τ₂ : Work.Cohomology.singularChains ℚ (TopCat.of X) ⟶
      Work.Cohomology.singularChains ℚ (TopCat.of X) := 𝟙 _
  let τ₃ := relChainsRPairMap A B (ContinuousMap.id X) (by intro x hx; exact hAB hx)
  have sq₁ : τ₁ ≫ (Work.StemsB.relChainsRShort ℚ (TopCat.of X) B).f
      = (Work.StemsB.relChainsRShort ℚ (TopCat.of X) A).f ≫ τ₂ := by
    show relChainsRInclSub ℚ A B hAB ≫ Work.StemsB.relChainsRIncl ℚ (TopCat.of X) B
      = Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A ≫ 𝟙 _
    rw [Category.comp_id, relChainsRInclSub_comp]
  have sq₂ : τ₂ ≫ (Work.StemsB.relChainsRShort ℚ (TopCat.of X) B).g
      = (Work.StemsB.relChainsRShort ℚ (TopCat.of X) A).g ≫ τ₃ := by
    show (𝟙 _ : Work.Cohomology.singularChains ℚ (TopCat.of X) ⟶
        Work.Cohomology.singularChains ℚ (TopCat.of X))
      ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) B)
      = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)
        ≫ relChainsRPairMap A B (ContinuousMap.id X) (by intro x hx; exact hAB hx)
    have hπ := cokernel_π_relChainsRPairMap A B (ContinuousMap.id X) (by intro x hx; exact hAB hx)
    rw [Category.id_comp, hπ]
    have h1 : Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of X)
        (TopCat.ofHom (ContinuousMap.id X)) = 𝟙 _ := CategoryTheory.Functor.map_id _ _
    rw [h1, Category.id_comp]
  let φ : Work.StemsB.relChainsRShort ℚ (TopCat.of X) A ⟶
      Work.StemsB.relChainsRShort ℚ (TopCat.of X) B := ShortComplex.homMk τ₁ τ₂ τ₃ sq₁ sq₂
  haveI hq : QuasiIso φ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
      (Work.StemsB.relChainsR_shortExact ℚ (TopCat.of X) A)
      (Work.StemsB.relChainsR_shortExact ℚ (TopCat.of X) B)
      (by show QuasiIso τ₁; exact quasiIso_relChainsRInclSub A B hAB h)
      (by show QuasiIso (𝟙 _ : Work.Cohomology.singularChains ℚ (TopCat.of X) ⟶
            Work.Cohomology.singularChains ℚ (TopCat.of X)); infer_instance)
  have hIso : IsIso (HomologicalComplex.homologyMap τ₃ m) := by
    rw [quasiIso_iff] at hq
    exact (quasiIsoAt_iff_isIso_homologyMap τ₃ m).mp (hq m)
  exact hIso

end

end Work.Serre
