import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.diskPairHomologyZero
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mvComp
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.cokerSmallOfU_iso_relChains_compat
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.puncturedBallSphere
import Submission.Work.Cohomology.diskPairHomologyTopOne
import Submission.Work.Cohomology.homologyPairShortExact
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.homologyContractible
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option synthInstance.maxHeartbeats 400000

/-!
# Local homology of an `n`-manifold

For a charted space `M` of dimension `n ≥ 1` and a point `x : M`, the `n`-th local homology
`Hₙ(M, M ∖ {x}; ℤ)` is `ℤ`.

The proof has three steps.

1. **Excision / relative small chains.**  For open subsets `U, A ⊆ X` with `U ∪ A = X`, the
   inclusion of pairs `(U, U ∩ A) → (X, A)` induces an isomorphism on relative homology.  Applied
   to `X = M`, `U` a chart neighborhood of `x` and `A = M ∖ {x}` this gives
   `Hₙ(M, M∖{x}) ≅ Hₙ(U, U∖{x})`.
2. **Homeomorphism invariance of pairs.**  A homeomorphism of pairs induces an isomorphism on
   relative homology, so the chart identification with an open ball `Bⁿ` gives
   `Hₙ(U, U∖{x}) ≅ Hₙ(Bⁿ, Bⁿ∖{0})`.
3. **The punctured ball.**  `Hₙ(Bⁿ, Bⁿ∖{0}) ≅ ℤ` by the long exact sequence of the pair, the
   contractibility of `Bⁿ` and `H_{n-1}(S^{n-1}) ≅ ℤ`.

The three ingredients of steps 1 and 3 are proved in the modules
`Submission.Work.Cohomology.relChainsMap_quasiIso`, `...relChainsMapOf_isIso` and
`...ballPairHomologyTop`; they are reproduced here (with primed names) because those modules import
the present file (they use the definitions below), so that importing them back would be circular.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Comparison maps of relative chain complexes -/

/-- The inclusion `{y : U | (y : X) ∈ A} ⟶ A` of the intersection, as a map of topological
spaces. -/
def inclInterA (X : TopCat) (U A : Set X) :
    TopCat.of {y : U | (y : X) ∈ A} ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun y => ⟨((y : U) : X), y.2⟩,
    Continuous.subtype_mk (f := fun y : {y : U | (y : X) ∈ A} => ((y : U) : X))
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)⟩

/-- The map `U ⟶ X` for a subset `U ⊆ X`, as a map of topological spaces. -/
abbrev inclU (X : TopCat) (U : Set X) : TopCat.of U ⟶ X := subtypeIncl X U

/-- **The map of relative chain complexes induced by a map of pairs.**

A map `f : X ⟶ Y` and a map `g : A ⟶ B` on the subspaces, compatible in the sense that
`subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`, induce a chain map `C_*(X,A) ⟶ C_*(Y,B)`. -/
def relChainsMapOf (X Y : TopCat) (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) : relChains X A ⟶ relChains Y B :=
  cokernel.map (inclChains X A) (inclChains Y B) (chainMap ℤ (TopCat.of A) (TopCat.of B) g)
    (chainMap ℤ X Y f) (by
      have h1 : chainMap ℤ (TopCat.of A) (TopCat.of B) g ≫ chainMap ℤ (TopCat.of B) Y
            (subtypeIncl Y B)
          = chainMap ℤ (TopCat.of A) Y (g ≫ subtypeIncl Y B) := by
        simp only [chainMap, Functor.map_comp]
      have h2 : chainMap ℤ (TopCat.of A) X (subtypeIncl X A) ≫ chainMap ℤ X Y f
          = chainMap ℤ (TopCat.of A) Y (subtypeIncl X A ≫ f) := by
        simp only [chainMap, Functor.map_comp]
      rw [inclChains, inclChains, h2, h1, w])

/-- **The map of relative chain complexes induced by the inclusion of pairs `(U, U ∩ A) ⊆ (X, A)`.** -/
def relChainsMap (X : TopCat) (U A : Set X) :
    relChains (TopCat.of U) {y : U | (y : X) ∈ A} ⟶ relChains X A :=
  relChainsMapOf (TopCat.of U) X {y : U | (y : X) ∈ A} A (subtypeIncl X U) (inclInterA X U A)
    (by ext y; simp only [subtypeIncl, inclInterA]; rfl)

/-- The naturality of `CokernelCofork.π` with respect to `cokernel.map`. -/
theorem cokernel_π_map {C : Type*} [Category C] [HasZeroMorphisms C] {X Y X' Y' : C}
    (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') :
    cokernel.π f ≫ cokernel.map f f' p q w = q ≫ cokernel.π f' := by
  rw [cokernel.map]
  exact cokernel.π_desc _ _ _

/-- The compatibility of `relChainsMap` with the projections to the relative chain complexes. -/
theorem cokernel_π_relChainsMap (X : TopCat) (U A : Set X) :
    cokernel.π (inclChains (TopCat.of U) {y : U | (y : X) ∈ A}) ≫ relChainsMap X U A
      = chainMap ℤ (TopCat.of U) X (subtypeIncl X U) ≫ cokernel.π (inclChains X A) := by
  rw [relChainsMap, relChainsMapOf]
  exact cokernel_π_map (inclChains (TopCat.of U) {y : U | (y : X) ∈ A}) (inclChains X A)
    (chainMap ℤ (TopCat.of {y : U | (y : X) ∈ A}) (TopCat.of A) (inclInterA X U A))
    (chainMap ℤ (TopCat.of U) X (subtypeIncl X U)) _


/-! ## The three delegated ingredients (copies of the modules that import this file) -/

/-- **The morphism of short exact sequences of pairs induced by a map of pairs.**

For `f : X ⟶ Y` and `g : TopCat.of A ⟶ TopCat.of B` compatible in the sense that
`subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`, this is the morphism of short exact sequences
`0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X,A) ⟶ 0  ⟶  0 ⟶ C_*(B) ⟶ C_*(Y) ⟶ C_*(Y,B) ⟶ 0`
with components `chainMap ℤ (TopCat.of A) (TopCat.of B) g`, `chainMap ℤ X Y f` and
`relChainsMapOf X Y A B f g w`. -/
def hPairShortMap_aux (X Y : TopCat) (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) :
    hPairShort X A ⟶ hPairShort Y B :=
  ShortComplex.homMk (chainMap ℤ (TopCat.of A) (TopCat.of B) g) (chainMap ℤ X Y f)
    (relChainsMapOf X Y A B f g w)
    (by
      show chainMap ℤ (TopCat.of A) (TopCat.of B) g ≫ inclChains Y B
        = inclChains X A ≫ chainMap ℤ X Y f
      simp only [inclChains, chainMap, ← Functor.map_comp]
      rw [w])
    (by
      show chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B)
        = cokernel.π (inclChains X A) ≫ relChainsMapOf X Y A B f g w
      rw [relChainsMapOf]
      exact (cokernel_π_map (inclChains X A) (inclChains Y B)
        (chainMap ℤ (TopCat.of A) (TopCat.of B) g) (chainMap ℤ X Y f) _).symm)

/-- A morphism of pairs which is a quasi-isomorphism on both spaces induces a quasi-isomorphism of
the relative chain complexes.

`Work.Cohomology.relChainsMapOf X Y A B f g w : relChains X A ⟶ relChains Y B` is defined in
`Submission/Work/Cohomology/localHomology.lean` for `f : X ⟶ Y` and `g : TopCat.of A ⟶ TopCat.of B`
compatible in the sense that `subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`.

The two maps `chainMap ℤ X Y f` and `chainMap ℤ (TopCat.of A) (TopCat.of B) g` are assumed to be
quasi-isomorphisms (isomorphisms on homology in every degree); this is the necessary form of the
hypotheses (a five term argument at degree `n` uses the neighbouring degree `n - 1` as well), and it
is what a homeomorphism (or homotopy equivalence) of pairs supplies.

Proof: apply `HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃` to the morphism of short
exact complexes `hPairShort X A ⟶ hPairShort Y B` whose components are
`chainMap ℤ (TopCat.of A) (TopCat.of B) g`, `chainMap ℤ X Y f` and `relChainsMapOf X Y A B f g w`.
The needed compatibility with the projections `cokernel.π` is `cokernel.π_map` (proved in
`localHomology.lean`). -/
theorem relChainsMapOf_homologyMap_isIso {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X A) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl Y B)) (n : ℕ)
    (hf : ∀ k, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) k))
    (hg : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) k)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X Y A B f g w) n) := by
  refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (hPairShortMap_aux X Y A B f g w) (hPairShort_shortExact X A) (hPairShort_shortExact Y B) n
    ?_ (hf n) ?_ ?_
  · show Epi (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) g) n)
    exact IsIso.epi_of_iso _
  · intro j _
    show IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) g) j)
    exact hg j
  · intro j _
    show Mono (HomologicalComplex.homologyMap (chainMap ℤ X Y f) j)
    exact IsIso.mono_of_iso _

set_option maxHeartbeats 1600000 in
/-- Excision in the form of relative small chains: for open `U, A ⊆ X` with `U ∪ A = X`, the
inclusion of pairs `(U, U ∩ A) → (X, A)` is a quasi-isomorphism on relative singular homology.

`Work.Cohomology.relChainsMap X U A` is defined in `Submission/Work/Cohomology/localHomology.lean`.
Route: let `P` be the pushout `(C(U) ⊕ C(A))/{(x,-x)}`. The map `τ₂ : P → C(X)`, `[(u,a)] ↦ i_U u + i_A a`
is a quasi-isomorphism (it identifies `P` with `smallChains U A`: use `pushChain_gen`,
`isSmallChain_gen`, `smallToSing_gen`, `mem_of_gen`, `smallToSing_f_injective` and
`smallChains_homology_iso`), and `0 → C(A) → P → C(U, U∩A) → 0` is short exact. Then apply
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃` to the morphism of short exact
sequences `hPairShort X A → (0 → C(A) → P → C(U,U∩A) → 0)` with `τ₁ = 𝟙` and `τ₂` as above.
The non-elementary input is `range (C(U) → C(X)) ⊓ range (C(A) → C(X)) = range (C(U∩A) → C(X))`;
prove it with the projections `π_σ` of `SSet.isColimitChainComplexXCofan` (checks on generators via
`SSet.chainComplex_hom_ext`), the idempotent on generators
`gen σ ↦ if σ factors through U∩A then gen σ else 0`,
and `ModuleCat.coprodIsoDirectSum` with `DirectSum.ext_component` for
"equal coordinates implies equal elements". -/
theorem excision_relChainsMap_isIso (X : TopCat) (U A : Set X) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) n) := by
  have hcov' : A ∪ U = Set.univ := by rw [Set.union_comm]; exact hcov
  let A' : Set U := {x : U | (x : X) ∈ A}
  let u : singularChains ℤ (TopCat.of A) ⟶ smallChains A U := smallOfU A U
  let w : smallChains A U ⟶ singularChains ℤ X := smallToSing A U
  have huw : u ≫ w = inclChains X A := smallOfU_comp_smallToSing A U
  have huw' : u ≫ w = (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A := by
    rw [Category.id_comp]; exact huw
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort X A
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel u
      mono_f := mono_smallOfU A U
      epi_g := inferInstance }
  have hS₂ : S₂.ShortExact := hPairShort_shortExact X A
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := cokernel.map u (inclChains X A) (𝟙 _) w huw'
  have hcomp1 : (𝟙 S₁.X₁) ≫ S₂.f = S₁.f ≫ w := by
    show (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A = u ≫ w
    rw [Category.id_comp]; exact huw.symm
  have hcomp2 : w ≫ S₂.g = S₁.g ≫ τ₃ := by
    show w ≫ cokernel.π (inclChains X A)
      = cokernel.π u ≫ cokernel.map u (inclChains X A) (𝟙 _) w huw'
    exact (cokernel_π_map u (inclChains X A) (𝟙 _) w huw').symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 S₁.X₁) w τ₃ hcomp1 hcomp2
  have hφ₂ : φ.τ₂ = w := rfl
  have hφ₁ : φ.τ₁ = 𝟙 S₁.X₁ := rfl
  have hτ₃ : IsIso (HomologicalComplex.homologyMap τ₃ n) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ n ?_ ?_ ?_ ?_
    · rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · rw [hφ₂]; exact smallChains_homology_iso A U hA hU hcov' n
    · intro j _
      rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · intro j _
      rw [hφ₂]
      haveI := smallChains_homology_iso A U hA hU hcov' j
      infer_instance
  obtain ⟨e, he⟩ := cokerSmallOfU_iso_relChains_compat X A U
  have key : cokernel.π (smallOfU A U) ≫ τ₃ = w ≫ cokernel.π (inclChains X A) :=
    cokernel_π_map u (inclChains X A) (𝟙 _) w huw'
  have hfac : relChainsMap X U A = e.hom ≫ τ₃ := by
    apply (cancel_epi (cokernel.π (inclChains (TopCat.of U) A'))).1
    calc cokernel.π (inclChains (TopCat.of U) A') ≫ relChainsMap X U A
        = chainMap ℤ (TopCat.of U) X (subtypeIncl X U) ≫ cokernel.π (inclChains X A) :=
          cokernel_π_relChainsMap X U A
      _ = inclChains X U ≫ cokernel.π (inclChains X A) := rfl
      _ = (smallOfV A U ≫ w) ≫ cokernel.π (inclChains X A) := by
            rw [smallOfV_comp_smallToSing]
      _ = smallOfV A U ≫ (w ≫ cokernel.π (inclChains X A)) := Category.assoc _ _ _
      _ = smallOfV A U ≫ (cokernel.π (smallOfU A U) ≫ τ₃) := by rw [key]
      _ = (smallOfV A U ≫ cokernel.π (smallOfU A U)) ≫ τ₃ := (Category.assoc _ _ _).symm
      _ = (cokernel.π (inclChains (TopCat.of U) A') ≫ e.hom) ≫ τ₃ := by rw [he]
      _ = cokernel.π (inclChains (TopCat.of U) A') ≫ (e.hom ≫ τ₃) :=
          Category.assoc _ _ _
  rw [hfac, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (HomologicalComplex.homologyMap e.hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n) e.hom
  exact inferInstance

/-- **A pair with vanishing `H₁` and reduced `H₀` of the subspace equal to `ℤ` has `H₁(X,A) = ℤ`.**

If `H₁(X) = 0` and the augmentation `ε_X : H₀(X) ⟶ ℤ` is invertible (as for a contractible `X`),
then the connecting map of the pair identifies `H₁(X,A)` with `ker ε_A`, the reduced zeroth
homology of `A`. -/
theorem relH1OfPair_aux (X : TopCat) (A : Set X)
    (h1 : IsZero ((singularChains ℤ X).homology 1))
    (hε : IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)))
    (hA : Nonempty (kerMod (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ))) ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty ((relChains X A).homology 1 ≅ ModuleCat.of ℤ ℤ) := by
  haveI := hε
  -- `H₁(X,A)` is the kernel of the map induced by the inclusion on `H₀`
  obtain ⟨e1⟩ := relHomologyOne_iso_kernel X A h1
  -- that map is `ε_A` followed by the inverse of `ε_X`, hence has the kernel of `ε_A`
  have hcomp : HomologicalComplex.homologyMap (inclChains X A) 0 ≫
      (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) =
      TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ) :=
    epsilonNaturality (TopCat.of A) X (subtypeIncl X A)
  have e2 : kernel (HomologicalComplex.homologyMap (inclChains X A) 0) ≅
      kernel (TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ)) :=
    (IsLimit.conePointUniqueUpToIso
      (kernel.ofCompIso (f := TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ))
        (HomologicalComplex.homologyMap (inclChains X A) 0)
        (asIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ))) hcomp)
      (limit.isLimit _)).symm
  obtain ⟨hA⟩ := hA
  exact ⟨e1 ≪≫ e2 ≪≫ ModuleCat.kernelIsoKer
      (TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ)) ≪≫
    moduleCatOfIsoOfEq ≪≫ hA⟩

/-- **The top relative homology of a punctured open interval is `ℤ`.**

Let `y : EuclideanSpace ℝ (Fin 1)`, `r > 0`, `X = TopCat.of (Metric.ball y r)` (an open interval,
hence contractible) and `A = {z : Metric.ball y r | (z : ℝ¹) ≠ y} ⊆ X`.  Given a homotopy
equivalence of `A` with the two point space `S⁰ = Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1`
(for instance the `n = 1` case of `Work.Cohomology.puncturedBallSphere`, to be proved in
`Submission/Work/Cohomology/puncturedBallSphere.lean`), the first relative singular homology of
the pair is `ℤ`.

Suggested route: `H₁(X) = 0` because `X` is contractible (`Work.Cohomology.homologyContractible`),
so `Work.Cohomology.relHomologyOne_iso_kernel` identifies `H₁(X,A)` with the kernel of
`H₀(A) ⟶ H₀(X)` (see `Submission/Work/Cohomology/diskPairHomologyTopOne.lean` for exactly this
style of argument); by naturality of the augmentation (`Work.Cohomology.epsilonNaturality`) and
invertibility of `ε_X` (contractible `X`) this kernel is the kernel of the augmentation of `A`,
i.e. the reduced `H₀` of a two point space.  For the latter use
`Work.Cohomology.ker_eps_homotopyEquiv` together with
`Work.Cohomology.reducedH0SphereInUnitOne` (the reduced `H₀` of `sphereInUnit 1`) and
`Work.Cohomology.sphereInUnitHomeomorph`, converting between `kerMod` and
`ModuleCat.of ℤ ↥(LinearMap.ker ·)` via `Work.Cohomology.ofKerIsoKerMod`.
(Do NOT import `Submission.Work.Cohomology.reducedH0SphereOne`: its helper names clash with
`reducedH0SphereInUnitOne`, which is already pulled in through `localHomology`.) -/
theorem ballPairHomologyTopOne_aux (y : EuclideanSpace ℝ (Fin 1)) (r : ℝ) (hr : 0 < r)
    (e : ContinuousMap.HomotopyEquiv
      {z : Metric.ball y r // (z : EuclideanSpace ℝ (Fin 1)) ≠ y}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) :
    Nonempty ((relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin 1)) ≠ y}).homology 1
        ≅ ModuleCat.of ℤ ℤ) := by
  -- the open ball is a nonempty convex subset of `ℝ¹`, hence contractible
  haveI hc : ContractibleSpace (TopCat.of (Metric.ball y r)) :=
    Convex.contractibleSpace (convex_ball y r) ⟨y, Metric.mem_ball_self hr⟩
  refine relH1OfPair_aux (TopCat.of (Metric.ball y r))
    {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin 1)) ≠ y}
    (homologyContractible 1 (by norm_num)) inferInstance ?_
  -- the punctured ball is homotopy equivalent to `S⁰`, and the reduced `H₀` of `S⁰` is `ℤ`
  obtain ⟨eH⟩ := ker_eps_homotopyEquiv e
  obtain ⟨eS⟩ := ker_eps_homotopyEquiv (sphereInUnitHomeomorph 1).toHomotopyEquiv
  obtain ⟨e4⟩ := reducedH0SphereInUnitOne
  exact ⟨eH ≪≫ eS.symm ≪≫ moduleCatOfIsoOfEq ≪≫ e4⟩

/-- The open ball `Metric.ball y r` is contractible (`r > 0`): it is a nonempty convex subset of
the Euclidean space. -/
theorem ballContractible_aux (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    ContractibleSpace (TopCat.of (Metric.ball y r)) := by
  show ContractibleSpace ↥(Metric.ball y r)
  exact Convex.contractibleSpace (convex_ball y r) ⟨y, Metric.mem_ball_self hr⟩

/-- **The top relative homology of the punctured open ball, `n ≥ 2`.**

Here the long exact sequence of the pair has two vanishing terms `Hₙ(B) = Hₙ₋₁(B) = 0`, so the
connecting map `δ : Hₙ(B, B∖{y}) ⟶ Hₙ₋₁(B∖{y})` is an isomorphism, and the punctured ball is
homotopy equivalent to `Sⁿ⁻¹` (`Work.Cohomology.puncturedBallSphere`), whose `(n-1)`-st homology
is `ℤ` (`Work.Cohomology.sphereHomologyTop`). -/
theorem ballPairHomologyTopGeTwo_aux (n : ℕ) (hn : 2 ≤ n) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : 0 < r) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y}).homology n
        ≅ ModuleCat.of ℤ ℤ) := by
  haveI hcontr : ContractibleSpace (TopCat.of (Metric.ball y r)) := ballContractible_aux n y r hr
  have hn1 : 1 ≤ n := by omega
  -- the ball has vanishing homology in degrees `n` and `n - 1`
  have hz1 : IsZero ((singularChains ℤ (TopCat.of (Metric.ball y r))).homology n) :=
    homologyContractible n (by omega)
  have hz0 : IsZero ((singularChains ℤ (TopCat.of (Metric.ball y r))).homology (n - 1)) :=
    homologyContractible (n - 1) (by omega)
  have hδ : IsZero ((singularChains ℤ (TopCat.of (Metric.ball y r))).homology ((n - 1) + 1)) := by
    rw [Nat.sub_add_cancel hn1]; exact hz1
  -- hence the connecting map of the pair is an isomorphism
  haveI hiso : IsIso (hPairδ (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y} (n - 1)) :=
    hPairδ_isIso _ _ _ hδ hz0
  -- the punctured ball is homotopy equivalent to `Sⁿ⁻¹`
  have he := Classical.choice (puncturedBallSphere n hn1 y r hr)
  refine ⟨(eqToIso (congrArg (fun k => (relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y}).homology k)
      (Nat.sub_add_cancel hn1))).symm ≪≫ asIso (hPairδ _ _ (n - 1))
      ≪≫ Classical.choice (homologyIso_of_homotopyEquiv he (n - 1)) ≪≫ ?_⟩
  -- and `Hₙ₋₁(Sⁿ⁻¹) ≅ ℤ`
  exact (Nat.sub_add_cancel hn1) ▸ Classical.choice (sphereHomologyTop (n - 1) (by omega))

/-! ## The main statement -/

/-- **The relative homology of a punctured open ball.**

For `n ≥ 1`, a point `y` of `EuclideanSpace ℝ (Fin n)` and `r > 0`, the `n`-th relative singular
homology (with `ℤ` coefficients) of the pair consisting of the open ball `Metric.ball y r` and its
complement of `{y}` is `ℤ`.

Suggested route: the long exact sequence of the pair `(B, B ∖ {y})` (`hPairδ`, `hPair_exact₁`,
`hPair_exact₃` and the trick of `hPairδ_isIso` in `Submission/Work/Cohomology/diskPairHomologyTop.lean`),
the contractibility of the ball (`convex_ball`, `Convex.contractibleSpace`, `homologyContractible`)
and `Work.Cohomology.sphereHomologyTop`, using that `B ∖ {y}` deformation retracts onto the sphere
of radius `r/2` around `y` (`homologyIso_of_homotopyEquiv`, in
`Submission/Work/Cohomology/sphereHomologyTop.lean`).  For `n = 1` the same sequence computes the
reduced `H₀` of a two point space: `Work.Cohomology.reducedH0OfTwoPoints` and
`Work.Cohomology.ker_eps_homotopyEquiv`. -/
theorem ballPairHomologyTop_aux (n : ℕ) (hn : 1 ≤ n) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : 0 < r) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y}).homology n
        ≅ ModuleCat.of ℤ ℤ) := by
  rcases eq_or_lt_of_le hn with h1 | h1
  · -- `n = 1`: `H₁` of the pair is the reduced `H₀` of the two point space `S⁰`
    subst h1
    exact ballPairHomologyTopOne_aux y r hr
      (Classical.choice (puncturedBallSphere 1 le_rfl y r hr))
  · -- `n ≥ 2`: the connecting map is an isomorphism onto `Hₙ₋₁(Sⁿ⁻¹)`
    exact ballPairHomologyTopGeTwo_aux n h1 y r hr

/-! ## Homeomorphisms used in the reduction to the flat ball -/

/-- The punctured version of a homeomorphism: a homeomorphism `e` carrying `a` to `b` restricts to
a homeomorphism of the complements of these points. -/
def homeomorphComplSingleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : X) (b : Y) (hab : e a = b) :
    {x : X // x ≠ a} ≃ₜ {y : Y // y ≠ b} where
  toFun x := ⟨e x.1, fun h => x.2 (e.injective (by rw [h, hab]))⟩
  invFun y := ⟨e.symm y.1, fun h => y.2 (by have h' := congrArg e h; simpa [hab] using h')⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

/-- The restriction of an open partial homeomorphism to the preimage of a ball contained in its
target, as a homeomorphism onto that ball. -/
def partialHomeomorphBallHomeo {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (e : OpenPartialHomeomorph X Y) {c : Y} {r : ℝ}
    (hsub : Metric.ball c r ⊆ e.target) :
    ↥(e.source ∩ e ⁻¹' Metric.ball c r) ≃ₜ ↥(Metric.ball c r) where
  toFun y := ⟨e y.1, y.2.2⟩
  invFun ζ := ⟨e.symm ζ.1,
    ⟨e.map_target (hsub ζ.2),
      by simpa only [Set.mem_preimage, e.right_inv (hsub ζ.2)] using ζ.2⟩⟩
  left_inv y := by
    ext
    exact e.left_inv y.2.1
  right_inv ζ := by
    ext
    exact e.right_inv (hsub ζ.2)
  continuous_toFun := by
    have h1 : Continuous fun y : ↥(e.source ∩ e ⁻¹' Metric.ball c r) =>
        (⟨y.1, y.2.1⟩ : ↥e.source) :=
      Continuous.subtype_mk continuous_subtype_val (fun y => y.2.1)
    have h2 : Continuous fun z : ↥e.source =>
        (⟨e z.1, e.map_source z.2⟩ : ↥e.target) :=
      (e.toHomeomorphSourceTarget).continuous
    have h3 : Continuous fun w : ↥e.target => (w : Y) := continuous_subtype_val
    have h4 : Continuous fun y : ↥(e.source ∩ e ⁻¹' Metric.ball c r) => e y.1 :=
      h3.comp (h2.comp h1)
    exact Continuous.subtype_mk h4 (fun y => y.2.2)
  continuous_invFun := by
    have h1 : Continuous fun ζ : ↥(Metric.ball c r) =>
        (⟨ζ.1, hsub ζ.2⟩ : ↥e.target) :=
      Continuous.subtype_mk continuous_subtype_val (fun ζ => hsub ζ.2)
    have h2 : Continuous fun w : ↥e.target =>
        (⟨e.symm w.1, e.map_target w.2⟩ : ↥e.source) :=
      (e.symm.toHomeomorphSourceTarget).continuous
    have h3 : Continuous fun z : ↥e.source => (z : X) := continuous_subtype_val
    have h4 : Continuous fun ζ : ↥(Metric.ball c r) => e.symm ζ.1 := h3.comp (h2.comp h1)
    exact Continuous.subtype_mk h4 (fun ζ =>
      ⟨e.map_target (hsub ζ.2),
        by simpa only [Set.mem_preimage, e.right_inv (hsub ζ.2)] using ζ.2⟩)

/-- A homotopy equivalence induces an isomorphism on singular homology in every degree, for the
chain map induced by its forward map. -/
theorem isIso_homologyMap_chainMap_of_homotopyEquiv {X Y : TopCat}
    (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y (TopCat.ofHom e.toFun)) n) := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.right_inv.some
  exact homologyEquiv ℤ X Y f g h1 h2 n

theorem localHomology (n : ℕ) (hn : 1 ≤ n) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of M) {y : M | y ≠ x}).homology n) ≅
      ModuleCat.of ℤ ℤ) := by
  haveI : T1Space M := ChartedSpace.t1Space (EuclideanSpace ℝ (Fin n)) M
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨r, hr, hsub⟩ : ∃ r > 0, Metric.ball (e x) r ⊆ e.target :=
    Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let s' : Set M := e.source ∩ e ⁻¹' Metric.ball (e x) r
  have hs'_open : IsOpen s' := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxcov : s' ∪ {y : M | y ≠ x} = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases hy : y = x
      · subst hy
        exact Or.inl ⟨hx, by simpa using hr⟩
      · exact Or.inr hy
  set φ : ↥s' ≃ₜ ↥(Metric.ball (e x) r) := partialHomeomorphBallHomeo e hsub with hφdef
  set x' : ↥s' := ⟨x, ⟨hx, by simpa using hr⟩⟩ with hx'def
  set y' : ↥(Metric.ball (e x) r) := ⟨e x, by simpa using hr⟩ with hy'def
  have hφx : φ x' = y' := Subtype.ext rfl
  -- Step 1 : excision in `M`
  have hexc : IsIso (HomologicalComplex.homologyMap
      (relChainsMap (TopCat.of M) s' {y : M | y ≠ x}) n) :=
    excision_relChainsMap_isIso (X := TopCat.of M) (U := s') (A := {y : M | y ≠ x})
      (hU := hs'_open) (hA := isClosed_singleton.isOpen_compl) (hcov := hxcov) (n := n)
  have h1 := CategoryTheory.asIso (HomologicalComplex.homologyMap
    (relChainsMap (TopCat.of M) s' {y : M | y ≠ x}) n)
  -- Step 2 : the chart homeomorphism
  set A2 : Set ↥s' := {y | y ≠ x'} with hA2def
  set B2 : Set ↥(Metric.ball (e x) r) := {ζ | ζ ≠ y'} with hB2def
  set ψ : ↥A2 ≃ₜ ↥B2 := homeomorphComplSingleton φ x' y' hφx with hψdef
  set Xs : TopCat := TopCat.of ↥s' with hXsdef
  set Yb : TopCat := TopCat.of ↥(Metric.ball (e x) r) with hYbdef
  set Xa : TopCat := TopCat.of ↥A2 with hXadef
  set Yp : TopCat := TopCat.of ↥B2 with hYpdef
  set f : Xs ⟶ Yb := TopCat.ofHom φ.toHomotopyEquiv.toFun with hfdef
  set g : Xa ⟶ Yp := TopCat.ofHom ψ.toHomotopyEquiv.toFun with hgdef
  have hfq : ∀ k, IsIso (HomologicalComplex.homologyMap (chainMap ℤ Xs Yb f) k) :=
    fun k => isIso_homologyMap_chainMap_of_homotopyEquiv (X := Xs) (Y := Yb) φ.toHomotopyEquiv k
  have hgq : ∀ k, IsIso (HomologicalComplex.homologyMap (chainMap ℤ Xa Yp g) k) :=
    fun k => isIso_homologyMap_chainMap_of_homotopyEquiv (X := Xa) (Y := Yp) ψ.toHomotopyEquiv k
  have hw : subtypeIncl Xs A2 ≫ f = g ≫ subtypeIncl Yb B2 := by
    ext z
    rfl
  have hchart : IsIso (HomologicalComplex.homologyMap (relChainsMapOf Xs Yb A2 B2 f g hw) n) :=
    relChainsMapOf_homologyMap_isIso (X := Xs) (Y := Yb) (A := A2) (B := B2) (f := f) (g := g)
      (w := hw) (n := n) (hf := hfq) (hg := hgq)
  have h2 := CategoryTheory.asIso (HomologicalComplex.homologyMap
    (relChainsMapOf Xs Yb A2 B2 f g hw) n)
  -- convert to the `{y : ↥s' | (y : M) ≠ x}` formulation
  have hAset : {y : ↥s' | (y : M) ≠ x} = A2 := by
    ext y
    exact ⟨fun h hy => h (congrArg Subtype.val hy), fun h hy => h (Subtype.ext hy)⟩
  have hBset : {ζ : ↥(Metric.ball (e x) r) | (ζ : EuclideanSpace ℝ (Fin n)) ≠ e x} = B2 := by
    ext ζ
    exact ⟨fun h hy => h (by rw [hy]), fun h hx => h (Subtype.ext hx)⟩
  rw [← hAset] at h2
  -- Step 3 : the punctured ball
  obtain ⟨h3⟩ := ballPairHomologyTop_aux n hn (e x) r hr
  rw [hBset] at h3
  exact ⟨h1.symm ≪≫ h2 ≪≫ h3⟩


end

end Work.Cohomology
